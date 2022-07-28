{-
Module      : HOI4.Decisions
Description : Feature handler for Hearts of Iron IV decisions
-}
module HOI4.Decisions (
        parseHOI4Decisioncats, writeHOI4DecisionCats,
        parseHOI4Decisions, writeHOI4Decisions
    ,   findActivatedDecisionsInEvents
    ,   findActivatedDecisionsInDecisions
    ,   findActivatedDecisionsInOnActions
    ,   findActivatedDecisionsInNationalFocus
    ) where

import Debug.Trace (trace, traceM)

import Control.Arrow ((&&&))
import Control.Monad (foldM, forM)
import Control.Monad.Except (ExceptT (..), MonadError (..))
import Control.Monad.State (MonadState (..), gets)
import Control.Monad.Trans (MonadIO (..))

import Data.Maybe (catMaybes, fromMaybe, isJust, mapMaybe)
import Data.Monoid ((<>))
import Data.List (intersperse, foldl', intercalate)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T
import Text.PrettyPrint.Leijen.Text (Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP
import System.FilePath ((</>))

import Abstract -- everything
import qualified Doc
import FileIO (Feature (..), writeFeatures)
import HOI4.Messages -- everything
import MessageTools (iquotes, italicText)
import HOI4.Handlers (flagText, getStateLoc)
import QQ (pdx)
import SettingsTypes ( PPT, Settings (..), Game (..)
                     , IsGame (..), IsGameData (..), IsGameState (..)
                     , getGameL10n, getGameL10nIfPresent
                     , setCurrentFile, withCurrentFile
                     , hoistErrors, hoistExceptions)
import HOI4.Common -- everything

-- | Empty decision category. Starts off Nothing/empty everywhere, except id and name
-- (which should get filled in immediately).
newDecisionCat id locid locdesc path = HOI4Decisioncat id locid locdesc Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing path

-- | Take the decisions categories scripts from game data and parse them into decision
-- data structures.
parseHOI4Decisioncats :: (IsGameData (GameData g), IsGameState (GameState g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text HOI4Decisioncat)
parseHOI4Decisioncats scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr ->
                setCurrentFile sourceFile $ mapM parseHOI4Decisioncat scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing decision category: " ++ T.unpack err
            return HM.empty
        Right deccatFilesOrErrors ->
            flip HM.traverseWithKey deccatFilesOrErrors $ \sourceFile edeccats ->
                fmap (mkDecCatMap . catMaybes) . forM edeccats $ \case
                    Left err -> do
                        traceM $ "Error parsing decision categories in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right ddeccat -> return ddeccat
                where mkDecCatMap :: [HOI4Decisioncat] -> HashMap Text HOI4Decisioncat
                      mkDecCatMap = HM.fromList . map (decc_name &&& id)

-- | Parse one decisioncategory script into a decision data structure.
parseHOI4Decisioncat :: (IsGameData (GameData g), IsGameState (GameState g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe HOI4Decisioncat))
parseHOI4Decisioncat (StatementBare _) = throwError "bare statement at top level"
parseHOI4Decisioncat [pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] -> withCurrentFile $ \file -> do
            locid <- getGameL10nIfPresent id
            locdesc <- getGameL10nIfPresent (id <> "_desc")
            ddeccat <- hoistErrors $ foldM decisioncatAddSection
                                        (Just (newDecisionCat id locid locdesc file))
                                        parts
            case ddeccat of
                Left err -> return (Left err)
                Right Nothing -> return (Right Nothing)
                Right (Just deccat) -> withCurrentFile $ \file ->
                    return (Right (Just deccat ))
        _ -> throwError "unrecognized form for decision category"
    _ -> throwError "unrecognized form for decision category"
parseHOI4Decisioncat _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for decisi= reon category in " <> T.pack file)

-- | Add a sub-clause of the decision categry script to the data structure.
decisioncatAddSection :: (IsGameState (GameState g), MonadError Text m) =>
    Maybe HOI4Decisioncat -> GenericStatement -> PPT g m (Maybe HOI4Decisioncat)
decisioncatAddSection Nothing _ = return Nothing
decisioncatAddSection ddeccat stmt
    = return $ (`decisioncatAddSection'` stmt) <$> ddeccat
    where
        decisioncatAddSection' decc stmt = case stmt of
            [pdx| icon           = $txt  |] -> decc { decc_icon = Just txt }
            [pdx| visible        = @scr  |] -> decc { decc_visible = Just scr } -- can check from and root if target_root_trigger is true (or allowed if it's not present)
            [pdx| available      = @scr  |] -> decc { decc_available = Just scr } -- checks visible, if it's false the decision is greyed out but still visible
            [pdx| picture        = $txt  |] -> decc { decc_picture = Just txt }
            [pdx| custom_icon    = %_    |] -> decc
            [pdx| visibility_type = %_   |] -> decc
            [pdx| priority       = %_    |] -> decc
            [pdx| allowed        = @scr  |] -> decc { decc_allowed = Just scr } -- Checks only once on start/load an is used to restrict which countries have/not have it
            [pdx| visible_when_empty = %_ |] -> decc
            [pdx| scripted_gui   = %_    |] -> decc
            [pdx| highlight_states = %_  |] -> decc
            [pdx| on_map_area    = %_    |] -> decc
            [pdx| $other = %_ |] -> trace ("unknown decision category section: " ++ T.unpack other) $ decc
            _ -> trace ("unrecognised form for decision category section") $ decc

-- | Present the parsed decision categoriess as wiki text and write them to the
-- appropriate files.
writeHOI4DecisionCats :: (HOI4Info g, MonadIO m) => PPT g m ()
writeHOI4DecisionCats = do
    decisionCats <- getDecisioncats
    interface <- getInterfaceGFX
    let pathedDecisionCats :: [Feature HOI4Decisioncat]
        pathedDecisionCats = map (\decc -> Feature {
                                        featurePath = Just $ decc_path decc
                                    ,   featureId = Just (decc_name decc) <> Just ".txt"
                                    ,   theFeature = Right decc })
                              (HM.elems decisionCats)
    writeFeatures "decisions"
                  pathedDecisionCats
                  (\d -> scope HOI4Country $ pp_decisioncat d interface)

-- | Present a parsed decision category.
pp_decisioncat :: forall g m. (HOI4Info g, MonadError Text m) => HOI4Decisioncat -> HashMap Text Text -> PPT g m Doc
pp_decisioncat decc gfx = do
    version <- gets (gameVersion . getSettings)
    decc_text_loc <- getGameL10nIfPresent ((decc_name decc) <> "_desc")
    let deccArg :: Text -> (HOI4Decisioncat -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
        deccArg fieldname field fmt
            = maybe (return [])
                (\field_content -> do
                    content_pp'd <- fmt field_content
                    return
                        ["| ", Doc.strictText fieldname, " = "
                        ,PP.line
                        ,content_pp'd
                        ,PP.line])
                (field decc)
    allow_pp'd  <- deccArg "allowed" decc_allowed pp_script
    visible_pp'd  <- deccArg "visible" decc_visible pp_script
    available_pp'd  <- deccArg "available" decc_available pp_script
    let name = decc_name decc
        nameD = Doc.strictText name
    name_loc <- getGameL10n name
    let picture = decc_picture decc
    picture_pp <- case picture of
            Just pict ->
                let pictc = if not $ "GFX_decision_cat_" `T.isPrefixOf` pict then "GFX_decision_cat_" <> pict else pict in
                return $ HM.findWithDefault pictc pictc gfx
            _ -> return ""
    return . mconcat $
        ["== ", Doc.strictText picture_pp , "<!-- ", nameD, " --> ", Doc.strictText name_loc," ==", PP.line
        ," version = ", Doc.strictText version, PP.line
        ,maybe mempty
               (\txt -> mconcat [ Doc.strictText $ italicText $ Doc.nl2br txt, PP.line])
               (decc_text_loc)
        ] ++
        allow_pp'd ++
        visible_pp'd ++
        available_pp'd

-- | Empty decision. Starts off Nothing/empty everywhere, except id and name
-- (which should get filled in immediately).
newDecision :: HOI4Decision
newDecision = HOI4Decision undefined undefined Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing False Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing False Nothing Nothing False Nothing Nothing False Nothing undefined undefined

-- | Take the decisions scripts from game data and parse them into decision
-- data structures.
parseHOI4Decisions :: (IsGameData (GameData g), IsGameState (GameState g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text HOI4Decision)
parseHOI4Decisions scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr ->
                setCurrentFile sourceFile $ concat <$> mapM parseHOI4DecisionGroup scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing decisions: " ++ T.unpack err
            return HM.empty
        Right decFilesOrErrors ->
            flip HM.traverseWithKey decFilesOrErrors $ \sourceFile edecs ->
                fmap (mkDecMap . catMaybes) . forM edecs $ \case
                    Left err -> do
                        traceM $ "Error parsing decisions in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right ddec -> return ddec
                where mkDecMap :: [HOI4Decision] -> HashMap Text HOI4Decision
                      mkDecMap = HM.fromList . map (dec_name &&& id)

-- | Parse one file's decision groups scripts into decision data structures.
parseHOI4DecisionGroup :: (IsGameData (GameData g), IsGameState (GameState g), Monad m) =>
    GenericStatement -> PPT g (ExceptT Text m) [Either Text (Maybe HOI4Decision)]
parseHOI4DecisionGroup stmt@(StatementBare _) = throwError "bare statement at top level"
parseHOI4DecisionGroup [pdx| $left = @scr |]
    = forM scr $ \stmt -> (Right <$> parseHOI4Decision stmt left)
                            `catchError` (return . Left)
parseHOI4DecisionGroup [pdx| %check = %_ |] = case check of
    AtLhs _ -> return [(Right Nothing)]
    _-> throwError "unrecognized form for decision block (LHS)"
parseHOI4DecisionGroup _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for decision in " <> T.pack file)

-- | Parse one decision script into a decision data structure.
parseHOI4Decision :: (IsGameData (GameData g), IsGameState (GameState g), Monad m) =>
    GenericStatement -> Text -> PPT g (ExceptT Text m) (Maybe HOI4Decision)
parseHOI4Decision [pdx| $decName = %rhs |] category = case rhs of
    CompoundRhs parts -> do
        decName_loc <- getGameL10n decName
        decDesc <- getGameL10nIfPresent (decName <> "_desc")
        withCurrentFile $ \sourcePath ->
            foldM decisionAddSection
                  (Just (newDecision { dec_name = decName
                              , dec_name_loc = decName_loc
                              , dec_desc = decDesc
                              , dec_path = sourcePath </> T.unpack category -- so decision are divided into maps for the cateogry, should I loc or not?
                              , dec_cat = category}))
                  parts
    _ -> throwError "unrecognized form for decision (RHS)"
parseHOI4Decision [pdx| %check = %_ |] _ = case check of
    AtLhs _ -> return Nothing
    _-> throwError "unrecognized form for decision block (LHS)"
parseHOI4Decision _ _ = throwError "unrecognized form for decision (LHS)"

-- | Add a sub-clause of the decision script to the data structure.
decisionAddSection :: (IsGameData (GameData g),  MonadError Text m) =>
    Maybe HOI4Decision -> GenericStatement -> PPT g m (Maybe HOI4Decision)
decisionAddSection Nothing _ = return Nothing
decisionAddSection dec stmt
    = return $ (`decisionAddSection'` stmt) <$> dec
    where -- the QQ pdx patternmatching takes to long to compile with this many patterns so using case of here
        decisionAddSection' dec stmt@[pdx| $lhs = %rhs |] = case lhs of
            "icon" -> case rhs of
                GenericRhs txt _ ->
                    dec { dec_icon = Just (HOI4DecisionIconSimple txt) }
                CompoundRhs scr -> dec { dec_icon = Just (HOI4DecisionIconScript scr) }
                _ -> trace ("DEBUG: bad decions icon") $ dec
            "allowed" -> case rhs of -- Checks only once on start/load an is used to restrict which countries have/not have it
                CompoundRhs scr -> dec { dec_allowed = Just scr }
                _ -> dec
            "complete_effect" -> case rhs of -- effect when selecting decision, or when mission starts
                CompoundRhs scr -> dec { dec_complete_effect = Just scr }
                _ -> dec
            "ai_will_do" -> case rhs of
                CompoundRhs scr -> dec { dec_ai_will_do = Just (aiWillDo scr) }
                _ -> dec
            "target_root_trigger" -> case rhs of -- can only check root for targeted decisions if allowed is true
                CompoundRhs scr -> dec { dec_target_root_trigger = Just scr }
                _ -> dec
            "visible" -> case rhs of -- can check from and root if target_root_trigger is true (or allowed if it's not present)
                CompoundRhs scr -> dec { dec_visible = Just scr }
                _ -> dec
            "available" -> case rhs of -- checks visible, if it's false the decision is greyed out but still visible
                CompoundRhs scr -> dec { dec_available = Just scr }
                _ -> dec
            "priority" -> case rhs of
                _ -> dec
            "highlight_states" -> case rhs of
                _ -> dec
            "days_re_enable" -> case rhs of -- number of days it takes for decision to reapear after completion
                FloatRhs num -> dec { dec_days_re_enable = Just num }
                _ -> dec
            "fire_only_once"  -> case rhs of --bool, standard false
                GenericRhs "yes" [] -> dec { dec_fire_only_once = True }
                -- no is the default, so I don't think this is ever used
                GenericRhs "no" [] -> dec { dec_fire_only_once = False }
                _ -> dec
            "cost" -> case rhs of --var or num
                GenericRhs var [txt] -> dec { dec_cost = Just (HOI4DecisionCostVariable txt) }
                GenericRhs txt _ -> dec { dec_cost = Just (HOI4DecisionCostVariable txt) }
                FloatRhs num -> dec { dec_cost = Just (HOI4DecisionCostSimple num) }
                _ -> dec
            "custom_cost_trigger" -> case rhs of
                CompoundRhs scr -> dec { dec_custom_cost_trigger = Just scr }
                _ -> dec
            "custom_cost_text" -> case rhs of
                GenericRhs txt _ -> -- localizable
                    dec { dec_custom_cost_text = Just txt }
                _ -> dec
            "days_remove" -> case rhs of --number of days it takes to finish decision
                FloatRhs num -> dec { dec_days_remove = Just num }
                _ -> dec
            "remove_effect" -> case rhs of -- effect when decision completes
                CompoundRhs scr -> dec { dec_remove_effect = Just scr }
                _ -> dec
            "cancel_trigger" -> case rhs of -- trigger for canceling missions
                CompoundRhs scr -> dec { dec_cancel_trigger = Just scr }
                _ -> dec
            "cancel_effect" -> case rhs of -- effect when mission is canceled
                CompoundRhs scr -> dec { dec_cancel_effect = Just scr }
                _ -> dec
            "war_with_on_remove" -> case rhs of -- used to inform if a decison declares war when finished
                _ -> dec
            "war_with_on_complete" -> case rhs of -- used to inform if a decison declares war when selected
                _ -> dec
            "fixed_random_seed" -> case rhs of --bool, standard True
                _ -> dec
            "days_mission_timeout" -> case rhs of -- how long the mission takes to finish, and turns decision into mission
                FloatRhs num -> dec { dec_days_remove = Just num }
                _ -> dec
            "activation" -> case rhs of -- checks for if a mission starts
                _ -> dec
            "selectable_mission" -> case rhs of --bool, standard false
                _ -> dec
            "timeout_effect" -> case rhs of -- effect for mission completing
                CompoundRhs scr -> dec { dec_timeout_effect = Just scr }
                _ -> dec
            "is_good" -> case rhs of --bool, standard false but not really, says wether finishing the mission is good or bad
                _ -> dec
            "targets" -> case rhs of -- weirdo array , checks countries for which decision can be targeted to, turn decisions into targeted decision
                CompoundRhs scr -> dec { dec_targets = Just scr }
                _ -> dec
            "target_array" -> case rhs of -- uses variables to create targets for decision, turn decisions into targeted decision
                GenericRhs txt _ -> dec { dec_target_array = Just txt }
                _ -> dec
            "targets_dynamic" -> case rhs of --bool, standard false , makes targets also check for orignal_tag
                GenericRhs "yes" [] -> dec { dec_targets_dynamic = True }
                -- no is the default, so I don't think this is ever used
                GenericRhs "no" [] -> dec { dec_targets_dynamic = False }
                _ -> dec
            "target_trigger" -> case rhs of -- alternate to visible for targeted decision
                CompoundRhs scr -> dec { dec_target_trigger = Just scr }
                _ -> dec
            "war_with_target_on_complete" -> case rhs of --bool, standard false
                _ -> dec
            "war_with_target_on_remove" -> case rhs of --bool, standard false
                _ -> dec
            "war_with_target_on_timeout" -> case rhs of --bool, standard false ,
                _ -> dec
            "state_target" -> case rhs of --bool, standard false , targeted decison uses targets for states
                GenericRhs "yes" [] -> dec { dec_state_target = True }
                -- no is the default, so I don't think this is ever used
                GenericRhs "no" [] -> dec { dec_state_target = False }
                _ -> dec
            "on_map_mode" -> case rhs of
                _ -> dec
            "modifier" -> case rhs of -- effects that apply when decision is active (timer/mission?)
                CompoundRhs scr -> dec { dec_modifier = Just scr }
                _ -> dec
            "targeted_modifier" -> case rhs of -- effects for country/state targeted and duration?
                CompoundRhs scr -> dec { dec_targeted_modifier = Just scr }
                _ -> dec
            "cancel_if_not_visible" -> case rhs of -- cancels mission if visible is false
                GenericRhs "yes" [] -> dec { dec_cancel_if_not_visible = True }
                -- no is the default, so I don't think this is ever used
                GenericRhs "no" [] -> dec { dec_cancel_if_not_visible = False }
                _ -> dec
            "name" -> case rhs of -- is used over the localized id
                GenericRhs txt _ -> dec {dec_name = txt}
                _ -> dec
            "ai_hint_pp_cost" -> case rhs of
                _ -> dec
            "cosmetic_tag" -> case rhs of -- no clue
                _ -> dec
            "cosmetic_ideology" -> case rhs of -- no clue
                _ -> dec
            "remove_trigger" -> case rhs of -- used to cancel timed decision
                CompoundRhs scr -> dec { dec_remove_trigger = Just scr }
                _ -> dec
            "target_non_existing" -> case rhs of -- no clue
                _ -> dec
            other -> trace ("unknown decision section: " ++ show other ++ "  " ++ show stmt) $ dec
        decisionAddSection' dec stmt = trace ("unrecognised form for decision section") $ dec

-- | Present the parsed decisions as wiki text and write them to the
-- appropriate files.
writeHOI4Decisions :: (HOI4Info g, MonadIO m) => PPT g m ()
writeHOI4Decisions = do
    decisions <- getDecisions
    interface <- getInterfaceGFX
    let pathedDecisions :: [Feature HOI4Decision]
        pathedDecisions = map (\dec -> Feature {
                                        featurePath = Just $ dec_path dec
                                    ,   featureId = Just (dec_name dec) <> Just ".txt"
                                    ,   theFeature = Right dec })
                              (HM.elems decisions)
    writeFeatures "decisions"
                  pathedDecisions
                  (\d -> scope HOI4Country $ pp_decision d interface)

-- | Present a parsed decision.
pp_decision :: forall g m. (HOI4Info g, MonadError Text m) => HOI4Decision -> HashMap Text Text -> PPT g m Doc
pp_decision dec gfx = do
    version <- gets (gameVersion . getSettings)
    dec_text_loc <- getGameL10nIfPresent ((dec_name dec) <> "_desc")
    let decArg :: Text -> (HOI4Decision -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
        decArg fieldname field fmt
            = maybe (return [])
                (\field_content -> do
                    content_pp'd <- fmt field_content
                    return
                        ["| ", Doc.strictText fieldname, " = "
                        ,PP.line
                        ,content_pp'd
                        ,PP.line])
                (field dec)
    targets <- case (dec_targets dec, dec_target_array dec, dec_state_target dec) of
        (Just array, _, True) -> do
            let targetlist = mapMaybe extractTargetsStates array
            targetlistloc <- traverse getStateLoc targetlist
            let targetdoc = [Doc.pp_string (intercalate ", " $ map T.unpack targetlistloc)]
            return $ ["| targets = "] ++ targetdoc ++ [PP.line]
        (Just array, _, False) -> do
            let targetlist = mapMaybe extractTargets array
            targetlistloc <- traverse (flagText (Just HOI4Country)) targetlist
            let targetdoc = [Doc.pp_string (intercalate ", " $ map T.unpack targetlistloc)]
            return $ ["| targets = "] ++ targetdoc ++ [PP.line]
        (_, Just array, True) -> return $ ["| targets = States ",Doc.strictText array]
        (_, Just array, False) -> return $ ["| targets = ",Doc.strictText array]
        _ -> return $ [""]
    ------
    allow_pp'd  <- decArg "allowed" dec_allowed pp_script
    targetRootTrigger_pp'd  <- decArg "target_root_trigger" dec_target_root_trigger pp_script -- checks ROOT
    visible_pp'd  <- decArg "visible" dec_visible pp_script
    targetTrigger_pp'd  <- decArg "target_trigger" dec_target_trigger pp_script --checks FROM and ROOT and makes decision visible if true
    available_pp'd  <- decArg "available" dec_available pp_script
    removeTrigger_pp'd  <- decArg "remove_trigger" dec_remove_trigger pp_script --removes decision? and ends modifier effect and triggers remove_effect?
    cancelTrigger_pp'd  <- decArg "cancel_trigger" dec_cancel_trigger pp_script -- cancels missions, tirggers canceleffect
    effect_pp'd <- setIsInEffect True (decArg "complete_effect" dec_complete_effect pp_script)
    removeEffect_pp'd <- setIsInEffect True (decArg "remove_effect" dec_remove_effect pp_script)
    cancelEffect_pp'd <- setIsInEffect True (decArg "cancel_effect" dec_complete_effect pp_script)
    timeoutEffect_pp'd <- setIsInEffect True (decArg "timeout_effect" dec_timeout_effect pp_script)
    mawd_pp'd   <- setIsInEffect True (mapM ((imsg2doc =<<) . ppAiWillDo) (dec_ai_will_do dec))
    let name = dec_name dec
        nameD = Doc.strictText name
        cost_pp = case dec_cost dec of
            Just (HOI4DecisionCostSimple num) -> T.pack $ show num
            Just (HOI4DecisionCostVariable txt) -> txt
            _ -> "check script"
        isFireOnlyOnce = dec_fire_only_once dec
        cancelIfNotVisible = dec_cancel_if_not_visible dec
        targetsDynamic = dec_targets_dynamic dec
    custom_cost_loc_pp'd <- case dec_custom_cost_text dec of
            Just custom_cost_text -> do
                custom_cost_text_loc <- getGameL10n custom_cost_text
                return ["| custom_cost = ", Doc.strictText custom_cost_text_loc, PP.line]
            _ -> return []
    custom_cost_trigger_pp'd  <- decArg "custom_cost_trigger" dec_custom_cost_trigger pp_script
    activation_pp'd <- decArg "activation" dec_activation pp_script
    modifier_pp'd <- setIsInEffect True (decArg "modifier" dec_modifier pp_script)
    targetedModifier_pp'd <- setIsInEffect True (decArg "targeted_modifier" dec_modifier pp_script)
    name_loc <- getGameL10n name
    icon_pp'd <- case dec_icon dec of
            Just (HOI4DecisionIconSimple txt) ->
                let icond = if not $ "GFX_decision_" `T.isPrefixOf` txt then "GFX_decision_" <> txt else txt in
                return $ HM.findWithDefault icond icond gfx
            _ -> return "Check script"
    let days_remove = dec_days_remove dec
        days_re_enable = dec_days_re_enable dec
        days_mission_timeout = dec_days_mission_timeout dec
    ppActivatedBy_pp'd <- ppActivatedBy (dec_name dec)
    return . mconcat $
        ["<section begin=", nameD, "/>"
        ,"{{Decision", PP.line
        ,"| version = ", Doc.strictText version, PP.line
        ,"| decision_id = ", nameD, PP.line
        ,"| decision_name = ", Doc.strictText name_loc, PP.line
        ,"| icon = ", Doc.strictText icon_pp'd, PP.line
        ,"| cost = ", Doc.strictText cost_pp, PP.line
        ,maybe mempty
               (\txt -> mconcat ["| decision_text = ", Doc.strictText $ italicText $ Doc.nl2br txt, PP.line])
               (dec_text_loc)
        ] ++
        custom_cost_loc_pp'd ++
        custom_cost_trigger_pp'd ++
        [
        maybe mempty
               (\num -> mconcat ["| days_remove = ", Doc.strictText ((T.pack . show . floor) num), PP.line])
               (days_remove)
        ,maybe mempty
               (\num -> mconcat ["| days_re_enable = ", Doc.strictText ((T.pack . show . floor) num), PP.line])
               (days_re_enable)
        ,maybe mempty
               (\num -> mconcat ["| days_mission_timeout = ", Doc.strictText ((T.pack . show . floor) num), PP.line])
               (days_mission_timeout)
        ] ++
        ( if isFireOnlyOnce then
            ["| fire_only_once = yes", PP.line]
        else []) ++
        ( if cancelIfNotVisible then
            ["| cancel_if_not_visible = yes", PP.line]
        else []) ++
        ( if cancelIfNotVisible then
            ["| targets_dynamic = yes", PP.line]
        else []) ++
        allow_pp'd ++
        targetRootTrigger_pp'd ++
        visible_pp'd ++
        targetTrigger_pp'd ++
        targets ++
        ["----",PP.line] ++
        available_pp'd ++
        activation_pp'd ++
        ppActivatedBy_pp'd ++
        ["----",PP.line] ++
        removeTrigger_pp'd ++
        cancelTrigger_pp'd ++
        ["----",PP.line] ++
        effect_pp'd ++
        removeEffect_pp'd ++
        cancelEffect_pp'd ++
        timeoutEffect_pp'd ++
        ["----",PP.line] ++
        modifier_pp'd ++
        targetedModifier_pp'd ++
        flip (maybe []) mawd_pp'd (\awd_pp'd ->
            ["| comment = AI decision factors:", PP.line
            ,awd_pp'd, PP.line]) ++
        ["}}" -- no line, causes unwanted extra space
        ,"<section end=", nameD, "/>"
        ]
    where
        extractTargets (StatementBare (GenericLhs e [])) = Just e
        extractTargets stmt = (trace $ "Unknown in targets array statement: " ++ show stmt) $ Nothing
        extractTargetsStates (StatementBare (IntLhs e)) = Just e
        extractTargetsStates stmt@[pdx| state = !e |] = Just e
        extractTargetsStates stmt = (trace $ "Unknown in targets array statement: " ++ show stmt) $ Nothing


ppActivatedBy :: (HOI4Info g, Monad m) => Text -> PPT g m [Doc]
ppActivatedBy decisionId = do
    decisionTriggers <- getDecisionTriggers
    let mtriggers = HM.lookup decisionId decisionTriggers
    case mtriggers of
        Just triggers -> do
            ts <- mapM ppDecisionSource triggers
            -- FIXME: This is a bit ugly, but we only want a list if there's more than one trigger
            let ts' = if length ts < 2 then
                    ts
                else
                    map (\d -> Doc.strictText $ "* " <> (Doc.doc2text d)) ts
            return $ [mconcat $ ["| activated_by = "] ++ [PP.line] ++ (intersperse PP.line ts') ++ [PP.line]]
        _ -> return $ [Doc.strictText ""]

ppEventLoc :: (HOI4Info g, Monad m) => Text -> PPT g m Text
ppEventLoc id = do
    loc <- getEventTitle id -- Note: Hidden events often have empty titles, see e.g. fetishist_flavor.400
    case loc of
        (Just t) | T.length (T.strip t) /= 0 -> return $ "<!-- " <> id <> " -->" <> iquotes't t -- TODO: Add link if possible
        _ -> return $ "<tt>" <> id <> "</tt>"

formatWeight :: HOI4DecisionWeight -> Text
formatWeight Nothing = ""
formatWeight (Just (n, d)) = T.pack (" (Base weight: " ++ show n ++ "/" ++ show d ++ ")")

iquotes't = Doc.doc2text . iquotes

ppDecisionSource :: (HOI4Info g, Monad m) => HOI4DecisionSource -> PPT g m Doc
ppDecisionSource (HOI4DecSrcOption eventId optionId) = do
    eventLoc <- ppEventLoc eventId
    optLoc <- getGameL10n optionId
    return $ Doc.strictText $ mconcat [ "The event "
        , eventLoc
        , " option "
        , iquotes't optLoc
        ]
ppDecisionSource (HOI4DecSrcImmediate eventId) = do
    eventLoc <- ppEventLoc eventId
    return $ Doc.strictText $ mconcat [ "As an immediate effect of the "
        , eventLoc
        , " event"
        ]
ppDecisionSource (HOI4DecSrcDecComplete id loc) = do
    return $ Doc.strictText $ mconcat ["Taking the decision "
        , "<!-- "
        , id
        , " -->"
        , iquotes't loc
        ]
ppDecisionSource (HOI4DecSrcDecRemove id loc) = do
    return $ Doc.strictText $ mconcat ["Finishing the decision "
        , "<!-- "
        , id
        , " -->"
        , iquotes't loc
        ]
ppDecisionSource (HOI4DecSrcDecCancel id loc) = do
    return $ Doc.strictText $ mconcat ["Triggering the cancel trigger on the decision "
        , "<!-- "
        , id
        , " -->"
        , iquotes't loc
        ]
ppDecisionSource (HOI4DecSrcDecTimeout id loc) = do
    return $ Doc.strictText $ mconcat ["Running out the timer on the decision "
        , "<!-- "
        , id
        , " -->"
        , iquotes't loc
        ]
ppDecisionSource (HOI4DecSrcOnAction act weight) = do
    return $ Doc.strictText $ act <> formatWeight weight
ppDecisionSource (HOI4DecSrcNFComplete id loc) = do
    nfloc <- getGameL10n loc
    return $ Doc.strictText $ mconcat ["Completing the national focus "
        , "<!-- "
        , id
        , " -->"
        , iquotes't nfloc
        ]
ppDecisionSource (HOI4DecSrcNFSelect id loc) = do
    nfloc <- getGameL10n loc
    return $ Doc.strictText $ mconcat ["Selecting the national focus "
        , "<!-- "
        , id
        , " -->"
        , iquotes't nfloc
        ]


findInStmt :: GenericStatement -> [(HOI4DecisionWeight, Text)]
findInStmt stmt@[pdx| $lhs = $id |] | lhs == "activate_mission" = [(Nothing, id)]
findInStmt [pdx| %lhs = @scr |] = findInStmts scr
findInStmt _ = []

findInStmts :: [GenericStatement] -> [(HOI4DecisionWeight, Text)]
findInStmts stmts = concatMap findInStmt stmts

addDecisionSource :: (HOI4DecisionWeight -> HOI4DecisionSource) -> [(HOI4DecisionWeight, Text)] -> [(Text, HOI4DecisionSource)]
addDecisionSource ds l = map (\t -> (snd t, ds (fst t))) l

findInOptions :: Text -> [HOI4Option] -> [(Text, HOI4DecisionSource)]
findInOptions decisionId opts = concatMap (\o -> case hoi4opt_name o of
    Just optName -> addDecisionSource (const (HOI4DecSrcOption decisionId optName)) (maybe [] (concatMap findInStmt) (hoi4opt_effects o))
    _ -> []
    ) opts

addDecisionTriggers :: HOI4DecisionTriggers -> [(Text, HOI4DecisionSource)] -> HOI4DecisionTriggers
addDecisionTriggers hm l = foldl' ins hm l
    where
        ins :: HOI4DecisionTriggers -> (Text, HOI4DecisionSource) -> HOI4DecisionTriggers
        ins hm (k, v) = HM.alter (\orig -> case orig of
            Just l -> Just $ l ++ [v]
            Nothing -> Just [v]) k hm

findActivatedDecisionsInEvents :: HOI4DecisionTriggers -> [HOI4Event] -> HOI4DecisionTriggers
findActivatedDecisionsInEvents hm evts = addDecisionTriggers hm (concatMap findInEvent evts)
    where
        findInEvent :: HOI4Event -> [(Text, HOI4DecisionSource)]
        findInEvent evt@HOI4Event{hoi4evt_id = Just eventId} =
            (case hoi4evt_options evt of
                Just opts -> findInOptions eventId opts
                _ -> []) ++
            (addDecisionSource (const (HOI4DecSrcImmediate eventId)) (maybe [] findInStmts (hoi4evt_immediate evt)))
        findInEvent _ = []

findActivatedDecisionsInDecisions :: HOI4DecisionTriggers -> [HOI4Decision] -> HOI4DecisionTriggers
findActivatedDecisionsInDecisions hm ds = addDecisionTriggers hm (concatMap findInDecision ds)
    where
        findInDecision :: HOI4Decision -> [(Text, HOI4DecisionSource)]
        findInDecision d =
            (addDecisionSource (const (HOI4DecSrcDecComplete (dec_name d) (dec_name_loc d))) (maybe [] findInStmts (dec_complete_effect d))) ++
            (addDecisionSource (const (HOI4DecSrcDecRemove (dec_name d) (dec_name_loc d))) (maybe [] findInStmts (dec_remove_effect d))) ++
            (addDecisionSource (const (HOI4DecSrcDecCancel (dec_name d) (dec_name_loc d))) (maybe [] findInStmts (dec_cancel_effect d))) ++
            (addDecisionSource (const (HOI4DecSrcDecTimeout (dec_name d) (dec_name_loc d))) (maybe [] findInStmts (dec_timeout_effect d)))

findActivatedDecisionsInOnActions :: HOI4DecisionTriggers -> [GenericStatement] -> HOI4DecisionTriggers
findActivatedDecisionsInOnActions hm scr = foldl' findInAction hm scr
    where
        findInAction :: HOI4DecisionTriggers -> GenericStatement -> HOI4DecisionTriggers
        findInAction hm [pdx|on_actions = @stmts |] = foldl' findInAction hm stmts
        findInAction hm stmt@[pdx| $lhs = @scr |] = addDecisionTriggers hm (addDecisionSource (HOI4DecSrcOnAction (actionName lhs)) (findInStmts scr))
        findInAction hm stmt = (trace $ "Unknown on_actions statement: " ++ show stmt) $ hm

        actionName :: Text -> Text
        actionName n = HM.lookupDefault ("<pre>" <> n <> "</pre>") n actionNameTable


        -- TODO: deal with on_weekly_<TAG> on_daily_<TAG> etc.
        actionNameTable :: HashMap Text Text
        actionNameTable = HM.fromList
            [("on_ace_killed","<!-- on_ace_killed -->On ace killed")
            ,("on_ace_killed_by_ace","<!-- on_ace_killed_by_ace -->On ace killed by ace")
            ,("on_ace_killed_other_ace","<!-- on_ace_killed_other_ace -->On ace kills ace")
            ,("on_aces_killed_each_other","<!-- on_aces_killed_each_other -->On aces killed each other")
            ,("on_ace_promoted","<!-- on_ace_promoted -->On ace promoted")
            ,("on_annex", "<!-- on_annex -->On nation annexed")
            ,("on_army_leader_daily","<!-- on_army_leader_daily -->On every day for army leader")
            ,("on_army_leader_lost_combat","<!-- on_army_leader_lost_combat -->On army leader loses combat")
            ,("on_army_leader_won_combat","<!-- on_army_leader_won_combat -->On army leader wins combat")
            ,("on_border_war_lost","<!-- on_border_war_lost -->On lost border conflict war")
            ,("on_capitulation","<!-- on_capitulation -->On nation capitulation")
            ,("on_civil_war_end","<!-- on_civil_war_end -->On civil war end")
            ,("on_civil_war_end_before_annexation","<!-- on_civil_war_end_before_annexation -->On civil war end before annexation")
            ,("on_daily","<!-- on_daily -->On every day")
            ,("on_declare_war","<!-- on_declare_war -->On declared war")
            ,("on_faction_formed","<!-- on_faction_formed -->On faction formed")
            ,("on_government_change","<!-- on_government_change -->On government changed")
            ,("on_government_exiled","<!-- on_government_exiled -->On government exiled")
            ,("on_join_faction","<!-- on_join_faction -->On faction joined")
            ,("on_justifying_wargoal_pulse","<!-- on_justifying_wargoal_pulse -->On justifying wargoal")
            ,("on_liberate","<!-- on_liberate -->On nation liberated")
            ,("on_new_term_election","<!-- on_new_term_election -->On new term election")
            ,("on_nuke_drop","<!-- on_nuke_drop -->On nuke dropped")
            ,("on_monthly","<!-- on_monthly -->On every month")
            ,("on_offer_join_faction","<!-- on_offer_join_faction -->On nation invited to faction")
            ,("on_operative_captured","<!-- on_operative_captured -->On operative captured")
            ,("on_operative_death","<!-- on_operative_death -->On operative death")
            ,("on_operative_detected_during_operation","<!-- on_operative_detected_during_operation -->On operative detected during operation")
            ,("on_peaceconference_ended","<!-- on_peaceconference_ended -->On peace conference ended")
            ,("on_puppet","<!-- on_puppet -->On nation puppeted")
            ,("on_release_as_free","<!-- on_release_as_free -->On nation released as free nation")
            ,("on_release_as_puppet","<!-- on_release_as_puppet -->On nation released as puppet")
            ,("on_ruling_party_change","<!-- on_ruling_party_change -->On ruling party change")
            ,("on_state_control_changed","<!-- on_state_control_changed -->On state control changed")
            ,("on_startup", "<!-- on_startup -->On startup")
            ,("on_subject_annexed","<!-- on_subject_annexed -->On subject nation annexed")
            ,("on_subject_free","<!-- on_subject_free -->On subject nation freed")
            ,("on_unit_leader_created","<!-- on_unit_leader_created -->On army leader created")
            ,("on_war_relation_added","<!-- on_war_relation_added -->On nation joined war")
            ,("on_wargoal_expire","<!-- on_wargoal_expire -->On wargoal expired")
            ]

findActivatedDecisionsInNationalFocus :: HOI4DecisionTriggers -> [HOI4NationalFocus] -> HOI4DecisionTriggers
findActivatedDecisionsInNationalFocus hm nf = addDecisionTriggers hm (concatMap findInFocus nf)
    where
        findInFocus :: HOI4NationalFocus -> [(Text, HOI4DecisionSource)]
        findInFocus f =
            (addDecisionSource (const (HOI4DecSrcNFComplete (nf_id f) (nf_name_loc f))) (maybe [] findInStmts (nf_completion_reward f))) ++
            (addDecisionSource (const (HOI4DecSrcNFSelect (nf_id f) (nf_name_loc f))) (maybe [] findInStmts (nf_select_effect f)))