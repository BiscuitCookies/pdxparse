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
    ,   findActivatedDecisionsInIdeas
    ,   findActivatedDecisionsInCharacters
    ,   findActivatedDecisionsInScriptedEffects
    ,   findActivatedDecisionsInBops
    ) where

import Debug.Trace (trace, traceM)

import Control.Arrow ((&&&))
import Control.Monad (foldM, forM, (<=<))
import Control.Monad.Except (ExceptT (..), MonadError (..))
import Control.Monad.State (gets)
import Control.Monad.Trans (MonadIO (..))

import Data.Maybe (catMaybes, fromMaybe, mapMaybe)
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
import MessageTools (iquotes, italicText, formatDays)
import HOI4.Handlers (flagText, getStateLoc)
import QQ (pdx)
import SettingsTypes ( PPT, Settings (..)
                     , IsGame (..), IsGameData (..), IsGameState (..)
                     , getGameL10n, getGameL10nIfPresent
                     , setCurrentFile, withCurrentFile
                     , hoistErrors, hoistExceptions
                     , getGameInterface, getGameInterfaceIfPresent)
import HOI4.Common -- everything

-- | Empty decision category. Starts off Nothing/empty everywhere, except id and name
-- (which should get filled in immediately).
newDecisionCat :: Text -> Maybe Text -> Maybe Text -> FilePath -> HOI4Decisioncat
newDecisionCat id locid locdesc = HOI4Decisioncat id locid locdesc "decision_category_generic" Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing

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
                Right (Just deccat) -> withCurrentFile $ \_file ->
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
            [pdx| icon           = $txt  |] -> decc { decc_icon = txt }
            [pdx| visible        = %rhs  |] -> case rhs of
                CompoundRhs [] -> decc -- empty, treat as if it wasn't there
                CompoundRhs scr -> decc { decc_visible = Just scr } -- can check from and root if target_root_trigger is true (or allowed if it's not present)
                _ -> trace "bade decision category allowed" decc
            [pdx| available      = %rhs  |] -> case rhs of
                CompoundRhs [] -> decc -- empty, treat as if it wasn't there
                CompoundRhs scr -> decc { decc_available = Just scr } -- checks visible, if it's false the decision is greyed out but still visible
                _ -> trace "bade decision category allowed" decc
            [pdx| picture        = $txt  |] -> decc { decc_picture = Just txt }
            [pdx| custom_icon    = %_    |] -> decc
            [pdx| visibility_type = %_   |] -> decc
            [pdx| priority       = %_    |] -> decc
            [pdx| allowed        = %rhs  |] -> case rhs of
                CompoundRhs [] -> decc -- empty, treat as if it wasn't there
                CompoundRhs scr -> decc { decc_allowed = Just scr } -- Checks only once on start/load an is used to restrict which countries have/not have it
                _ -> trace "bade decision category allowed" decc
            [pdx| visible_when_empty = %_ |] -> decc
            [pdx| scripted_gui   = %_    |] -> decc
            [pdx| highlight_states = %_  |] -> decc
            [pdx| on_map_area    = %_    |] -> decc
            [pdx| $other = %_ |] -> trace ("unknown decision category section: " ++ T.unpack other) decc
            _ -> trace "unrecognised form for decision category section" decc

-- | Present the parsed decision categoriess as wiki text and write them to the
-- appropriate files.
writeHOI4DecisionCats :: (HOI4Info g, MonadIO m) => PPT g m ()
writeHOI4DecisionCats = do
    decisionCats <- getDecisioncats
    let pathedDecisionCats :: [Feature HOI4Decisioncat]
        pathedDecisionCats = map (\decc -> Feature {
                                        featurePath = Just $ decc_path decc
                                    ,   featureId = Just (decc_name decc) <> Just ".txt"
                                    ,   theFeature = Right decc })
                              (HM.elems decisionCats)
    writeFeatures "decisions"
                  pathedDecisionCats
                  (scope HOI4Country . ppdecisioncat)

-- | Present a parsed decision category.
ppdecisioncat :: forall g m. (HOI4Info g, MonadError Text m) => HOI4Decisioncat -> PPT g m Doc
ppdecisioncat decc = setCurrentFile (decc_path decc) $ do
    version <- gets (gameVersion . getSettings)
    decc_text_loc <- getGameL10nIfPresent (decc_name decc <> "_desc")
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
    allow_pp'd  <- deccArg "allowed" decc_allowed ppScript
    visible_pp'd  <- deccArg "visible" decc_visible ppScript
    available_pp'd  <- deccArg "available" decc_available ppScript
    let name = decc_name decc
        nameD = Doc.strictText name
    name_loc <- getGameL10n name
    let icon = decc_icon decc
        deccpicture = decc_picture decc
    icon_pp <- do
        micon <- getGameInterfaceIfPresent ("GFX_decision_category_" <> decc_name decc)
        case micon of
            Nothing -> let iconcat = if not $ "GFX_decision_category_" `T.isPrefixOf` icon then "GFX_decision_category_" <> icon else icon in
                    getGameInterface "decision_category_generic" iconcat
            Just icond -> return icond
    picture_pp <- do
        case deccpicture of
            Nothing -> return mempty
            Just picd -> do
                let piccat = if not $ "GFX_decision_category_" `T.isPrefixOf` picd then "GFX_decision_category_" <> picd else picd
                mpic <- getGameInterfaceIfPresent piccat
                maybe (return mempty) (\p -> return $ mconcat ["<!-- picture: ", Doc.strictText p, " -->", PP.line]) mpic
    return . mconcat $
        ["== [[File:", Doc.strictText icon_pp, ".png]]" , "<!-- ", nameD, " --> ", Doc.strictText name_loc," ==", PP.line]++

        [maybe mempty
               (\txt -> mconcat [picture_pp, Doc.strictText $ italicText $ Doc.nl2br txt, PP.line, PP.line])
               decc_text_loc
        ] ++
        allow_pp'd ++
        visible_pp'd ++
        available_pp'd

-- | Empty decision. Starts off Nothing/empty everywhere, except id and name
-- (which should get filled in immediately).
newDecision :: HOI4Decision
newDecision = HOI4Decision undefined undefined Nothing Nothing Nothing Nothing Nothing Nothing False Nothing Nothing False Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing False Nothing Nothing False Nothing Nothing False Nothing undefined undefined

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
parseHOI4DecisionGroup (StatementBare _) = throwError "bare statement at top level"
parseHOI4DecisionGroup [pdx| $left = @scr |]
    = forM scr $ \stmt -> (Right <$> parseHOI4Decision stmt left)
                            `catchError` (return . Left)
parseHOI4DecisionGroup [pdx| %check = %_ |] = case check of
    AtLhs _ -> return [Right Nothing]
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
        decisionAddSection' dec stmt@[pdx| $lhs = %rhs |] = case T.toLower lhs of
            "icon" -> case rhs of
                GenericRhs txt _ ->
                    dec { dec_icon = Just (HOI4DecisionIconSimple txt) }
                CompoundRhs scr -> dec { dec_icon = Just (HOI4DecisionIconScript scr) }
                _ -> trace "DEBUG: bad decisions icon" dec
            "allowed" -> case rhs of -- Checks only once on start/load an is used to restrict which countries have/not have it
                CompoundRhs [] -> dec -- empty, treat as if it wasn't there
                CompoundRhs scr -> dec { dec_allowed = Just scr }
                _ -> trace "DEBUG: bad decisions allowed" dec
            "complete_effect" -> case rhs of -- effect when selecting decision, or when mission starts
                CompoundRhs [] -> dec -- empty, treat as if it wasn't there
                CompoundRhs scr -> dec { dec_complete_effect = Just scr }
                _ -> trace "DEBUG: bad decisions complete_effect" dec
            "ai_will_do" -> case rhs of
                CompoundRhs scr -> dec { dec_ai_will_do = Just (aiWillDo scr) }
                _ -> trace "DEBUG: bad decisions ai_will_do" dec
            "target_root_trigger" -> case rhs of -- can only check root for targeted decisions if allowed is true
                CompoundRhs [] -> dec -- empty, treat as if it wasn't there
                CompoundRhs scr -> dec { dec_target_root_trigger = Just scr }
                _ -> trace "DEBUG: bad decisions target_root_trigger" dec
            "visible" -> case rhs of -- can check from and root if target_root_trigger is true (or allowed if it's not present)
                CompoundRhs [] -> dec -- empty, treat as if it wasn't there
                CompoundRhs scr -> dec { dec_visible = Just scr }
                _ -> trace "DEBUG: bad decisions visible" dec
            "available" -> case rhs of -- checks visible, if it's false the decision is greyed out but still visible
                CompoundRhs [] -> dec -- empty, treat as if it wasn't there
                CompoundRhs scr -> dec { dec_available = Just scr }
                _ -> trace "DEBUG: bad decisions available" dec
            "priority" -> dec
            "highlight_states" -> dec
            "days_re_enable" -> case rhs of -- number of days it takes for decision to reapear after completion
                (floatRhs -> num) -> dec { dec_days_re_enable = num }
                --_ -> trace "DEBUG: bad decisions days_re_enable" dec
            "fire_only_once"  -> case rhs of --bool, standard false
                GenericRhs "yes" [] -> dec { dec_fire_only_once = True }
                -- no is the default, so I don't think this is ever used
                GenericRhs "no" [] -> dec { dec_fire_only_once = False }
                _ -> trace "DEBUG: bad decisions fire_only_once" dec
            "cost" -> case rhs of --var or num
                GenericRhs txt [] -> dec { dec_cost = Just (HOI4DecisionCostVariable txt) }
                GenericRhs _var [txt] -> dec { dec_cost = Just (HOI4DecisionCostVariable txt) }
                (floatRhs -> Just num)  -> dec { dec_cost = Just (HOI4DecisionCostSimple num) }
                _ -> trace "DEBUG: bad decisions costt" dec
            "custom_cost_trigger" -> case rhs of
                CompoundRhs [] -> dec -- empty, treat as if it wasn't there
                CompoundRhs scr -> dec { dec_custom_cost_trigger = Just scr }
                _ -> trace "DEBUG: bad decisions custom_cost_trigger" dec
            "custom_cost_text" -> case rhs of
                GenericRhs txt _ -> -- localizable
                    dec { dec_custom_cost_text = Just txt }
                _ -> trace "DEBUG: bad decisions custom_cost_text" dec
            "days_remove" -> case rhs of --number of days it takes to finish decision
                (floatRhs -> num) -> dec { dec_days_remove = num }
                --_ -> trace "DEBUG: bad decisions days_remove" dec
            "remove_effect" -> case rhs of -- effect when decision completes
                CompoundRhs [] -> dec -- empty, treat as if it wasn't there
                CompoundRhs scr -> dec { dec_remove_effect = Just scr }
                _ -> trace "DEBUG: bad decisions remove_effect" dec
            "cancel_trigger" -> case rhs of -- trigger for canceling missions
                CompoundRhs [] -> dec -- empty, treat as if it wasn't there
                CompoundRhs scr -> dec { dec_cancel_trigger = Just scr }
                _ -> trace "DEBUG: bad decisions cancel_trigger" dec
            "cancel_effect" -> case rhs of -- effect when mission is canceled
                CompoundRhs [] -> dec -- empty, treat as if it wasn't there
                CompoundRhs scr -> dec { dec_cancel_effect = Just scr }
                _ -> trace "DEBUG: bad decisions cancel_effect" dec
            "war_with_on_remove" -> dec -- used to inform if a decison declares war when finished
            "war_with_on_complete" -> dec -- used to inform if a decison declares war when selected
            "war_with_on_timeout" -> dec -- used to inform if a decison declares war when selected
            "fixed_random_seed" -> dec --bool, standard True
            "days_mission_timeout" -> case rhs of -- how long the mission takes to finish, and turns decision into mission
                (floatRhs -> num)  -> dec { dec_days_remove = num }
                --_ -> trace "DEBUG: bad decisions days_mission_timeout" dec
            "activation" -> dec -- checks for if a mission starts
            "selectable_mission" -> dec --bool, standard false
            "timeout_effect" -> case rhs of -- effect for mission completing
                CompoundRhs [] -> dec -- empty, treat as if it wasn't there
                CompoundRhs scr -> dec { dec_timeout_effect = Just scr }
                _ -> trace "DEBUG: bad decisions trimeout_effect" dec
            "is_good" ->  case rhs of --bool, standard false but not really, says wether finishing the mission is good or bad
                GenericRhs "yes" [] -> dec { dec_cancel_if_not_visible = True }
                GenericRhs "no" [] -> dec { dec_cancel_if_not_visible = False }
                _ -> trace "DEBUG: bad decisions cancel_if_not_visible" dec
            "targets" -> case rhs of -- weirdo array , checks countries for which decision can be targeted to, turn decisions into targeted decision
                CompoundRhs [] -> dec -- empty, treat as if it wasn't there
                CompoundRhs scr -> dec { dec_targets = Just scr }
                _ -> trace "DEBUG: bad decisions targets" dec
            "target_array" -> case rhs of -- uses variables to create targets for decision, turn decisions into targeted decision
                GenericRhs txt _ -> dec { dec_target_array = Just txt }
                _ -> trace "DEBUG: bad decisions target array" dec
            "targets_dynamic" -> case rhs of --bool, standard false , makes targets also check for orignal_tag
                GenericRhs "yes" [] -> dec { dec_targets_dynamic = True }
                -- no is the default, so I don't think this is ever used
                GenericRhs "no" [] -> dec { dec_targets_dynamic = False }
                _ -> trace "DEBUG: bad decisions targets_dynamic" dec
            "target_trigger" -> case rhs of -- alternate to visible for targeted decision
                CompoundRhs [] -> dec -- empty, treat as if it wasn't there
                CompoundRhs scr -> dec { dec_target_trigger = Just scr }
                _ -> trace "DEBUG: bad decisions target_trigger" dec
            "war_with_target_on_complete" -> dec --bool, standard false
            "war_with_target_on_remove" -> dec --bool, standard false
            "war_with_target_on_timeout" -> dec --bool, standard false
            "state_target" -> case rhs of --bool, standard false , targeted decison uses targets for states
                GenericRhs "yes" [] -> dec { dec_state_target = True }
                -- no is the default, so I don't think this is ever used
                GenericRhs "no" [] -> dec { dec_state_target = False }
                _ -> trace "DEBUG: bad decisions state_target" dec
            "on_map_mode" -> dec
            "modifier" -> case rhs of -- effects that apply when decision is active (timer/mission?)
                CompoundRhs [] -> dec -- empty, treat as if it wasn't there
                CompoundRhs _scr -> dec { dec_modifier = Just stmt }
                _ -> trace "DEBUG: bad decisions modifier" dec
            "targeted_modifier" -> case rhs of -- effects for country/state targeted and duration?
                CompoundRhs [] -> dec -- empty, treat as if it wasn't there
                CompoundRhs _scr -> let oldstmt = fromMaybe [] (dec_targeted_modifier dec) in
                    dec { dec_targeted_modifier = Just (oldstmt ++ [stmt]) }
                _ -> trace "DEBUG: bad decisions targeted_modifier" dec
            "cancel_if_not_visible" -> case rhs of -- cancels mission if visible is false
                GenericRhs "yes" [] -> dec { dec_cancel_if_not_visible = True }
                -- no is the default, so I don't think this is ever used
                GenericRhs "no" [] -> dec { dec_cancel_if_not_visible = False }
                _ -> trace "DEBUG: bad decisions cancel_if_not_visible" dec
            "name" -> case rhs of -- is used over the localized id
                GenericRhs txt _ -> dec {dec_name = txt}
                _ -> trace "DEBUG: bad decisions name" dec
            "ai_hint_pp_cost" -> dec
            "cosmetic_tag" -> dec -- no clue
            "cosmetic_ideology" -> dec -- no clue
            "remove_trigger" -> case rhs of -- used to cancel timed decision
                CompoundRhs [] -> dec -- empty, treat as if it wasn't there
                CompoundRhs scr -> dec { dec_remove_trigger = Just scr }
                _ -> trace "DEBUG: bad decisions remove_trigger" dec
            "target_non_existing" -> dec -- no clue
            "power_balance" -> dec -- no clue, only seen in debug so far
            other -> trace ("unknown decision section: " ++ show other ++ "  " ++ show stmt) dec
        decisionAddSection' dec _stmt = trace "unrecognised form for decision section" dec

-- | Present the parsed decisions as wiki text and write them to the
-- appropriate files.
writeHOI4Decisions :: (HOI4Info g, MonadIO m) => PPT g m ()
writeHOI4Decisions = do
    decisions <- getDecisions
    let pathedDecisions :: [Feature HOI4Decision]
        pathedDecisions = map (\dec -> Feature {
                                        featurePath = Just $ dec_path dec
                                    ,   featureId = Just (dec_name dec) <> Just ".txt"
                                    ,   theFeature = Right dec })
                              (HM.elems decisions)
    writeFeatures "decisions"
                  pathedDecisions
                  (scope HOI4Country . ppdecision)

-- | Present a parsed decision.
ppdecision :: forall g m. (HOI4Info g, MonadError Text m) => HOI4Decision -> PPT g m Doc
ppdecision dec = setCurrentFile (dec_path dec) $ do
    version <- gets (gameVersion . getSettings)
    dec_text_loc <- getGameL10nIfPresent (dec_name dec <> "_desc")
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
    let decNoArg :: (HOI4Decision -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
        decNoArg field fmt
            = maybe (return [])
                (\field_content -> do
                    content_pp'd <- fmt field_content
                    return
                        [content_pp'd
                        ,PP.line])
                (field dec)
    targets <- case (dec_targets dec, dec_target_array dec, dec_state_target dec) of
        (Just array, _, True) -> do
            let targetlist = mapMaybe extractTargetsStates array
            targetlistloc <- traverse getStateLoc targetlist
            let targetdoc = [Doc.ppString (intercalate ", " $ map T.unpack targetlistloc)]
            return $ ["| targets = "] ++ targetdoc ++ [PP.line]
        (Just array, _, False) -> do
            let targetlist = mapMaybe extractTargets array
            targetlistloc <- traverse (flagText (Just HOI4Country)) targetlist
            let targetdoc = [Doc.ppString (intercalate ", " $ map T.unpack targetlistloc)]
            return $ ["| targets = "] ++ targetdoc ++ [PP.line]
        (_, Just array, True) -> return ["| targets = States ",Doc.strictText array, PP.line]
        (_, Just array, False) -> return ["| targets = ",Doc.strictText array, PP.line]
        _ -> return [""]
    ------
    allow_pp'd <- decNoArg dec_allowed ppScript
    targetRootTrigger_pp'd <- decNoArg dec_target_root_trigger ppScript -- checks ROOT
    visible_pp'd <- decNoArg dec_visible ppScript
    targetTrigger_pp'd <- decNoArg dec_target_trigger ppScript --checks FROM and ROOT and makes decision visible if true
    available_pp'd <- decArg "available" dec_available ppScript
    removeTrigger_pp'd <- decArg "remove_trigger" dec_remove_trigger ppScript --removes decision? and ends modifier effect and triggers remove_effect?
    cancelTrigger_pp'd <- decArg "cancel_trigger" dec_cancel_trigger ppScript -- cancels missions, triggers canceleffect
    effect_pp'd <- setIsInEffect True (decArg "select_effect" dec_complete_effect ppScript)
    removeEffect_pp'd <- setIsInEffect True (decArg "remove_effect" dec_remove_effect ppScript)
    cancelEffect_pp'd <- setIsInEffect True (decArg "cancel_effect" dec_cancel_effect ppScript)
    timeoutEffect_pp'd <- setIsInEffect True (decArg "timeout_effect" dec_timeout_effect ppScript)
    mawd_pp'd   <- setIsInEffect True (mapM (imsg2doc <=< ppAiWillDo) (dec_ai_will_do dec))
    let name = dec_name dec
        nameD = Doc.strictText name
        cost_pp = case dec_cost dec of
            Just (HOI4DecisionCostSimple num) -> Just $ T.pack $ show num
            Just (HOI4DecisionCostVariable txt) -> Just txt
            _ -> Nothing
        isFireOnlyOnce = dec_fire_only_once dec
        isGood = dec_is_good dec
        cancelIfNotVisible = dec_cancel_if_not_visible dec
        targetsDynamic = dec_targets_dynamic dec
    custom_cost_loc_pp'd <- case dec_custom_cost_text dec of
            Just custom_cost_text -> do
                custom_cost_text_loc <- getGameL10n custom_cost_text
                return ["| cost = ", Doc.strictText custom_cost_text_loc, "<!-- custom cost -->" ,PP.line]
            _ -> return []
    custom_cost_trigger_pp'd  <- decArg "custom_cost_trigger" dec_custom_cost_trigger ppScript
    activation_pp'd <- decNoArg dec_activation ppScript
    modifier_pp'd <- setIsInEffect True (decNoArg dec_modifier ppStatement)
    targetedModifier_pp'd <- setIsInEffect True (decNoArg dec_targeted_modifier ppScript)
    name_loc <- getGameL10n name
    icon_pp'd <- case dec_icon dec of
        Just (HOI4DecisionIconSimple txt) -> do
            let icond = if not $ "GFX_decision_" `T.isPrefixOf` txt then "GFX_decision_" <> txt else txt
            micon <- getGameInterfaceIfPresent icond
            case micon of
                Just icondd -> return $ "| decision_icon = " <> icondd <> "\n"
                Nothing -> return mempty
        Just (HOI4DecisionIconScript _) -> return "| decision_icon = <!-- Check script -->\n"
        _ -> return mempty
    let days_remove = dec_days_remove dec
        days_re_enable = dec_days_re_enable dec
        days_mission_timeout = dec_days_mission_timeout dec
    ppActivatedBy_pp'd <- ppActivatedBy (dec_name dec)
    return . mconcat $
        ["<section begin=", nameD, "/>", PP.line
        ,"{{Decision", PP.line
        ,"| version = ", Doc.strictText version, PP.line
        ,"| decision_id = ", nameD, PP.line
        ,"| decision_name = ", Doc.strictText name_loc, PP.line
        , Doc.strictText icon_pp'd
        ,maybe mempty
               (\txt -> mconcat ["| decision_text = ", Doc.strictText $ Doc.nl2br txt, PP.line])
               dec_text_loc
        ] ++
        custom_cost_loc_pp'd ++
        custom_cost_trigger_pp'd ++
        [maybe mempty (\txt -> if txt /= "0" then mconcat ["| cost = ", Doc.strictText txt, PP.line] else mconcat [])
               cost_pp
        ,maybe mempty
               (\num -> mconcat ["| cooldown = ", Doc.strictText $ formatDays $ fromIntegral num, PP.line])
               days_re_enable
        ,maybe mempty
               (\num -> mconcat ["| days_mission_timeout = ", Doc.strictText $ formatDays $ fromIntegral num, PP.line])
               days_mission_timeout
        ,maybe mempty
               (\num -> mconcat ["| days_remove = ", Doc.strictText $ formatDays $ fromIntegral num, PP.line])
               days_remove] ++
        ( if isGood then
            ["| is_good = yes", PP.line]
        else []) ++
        ( if isFireOnlyOnce then
            ["| fire_only_once = yes", PP.line]
        else []) ++
        ( if cancelIfNotVisible then
            ["| cancel_if_not_visible = yes", PP.line]
        else []) ++
        ( if targetsDynamic then
            ["| targets_dynamic = yes", PP.line]
        else []) ++
        (if not $ all null [allow_pp'd
            ,targetRootTrigger_pp'd
            ,visible_pp'd
            ,activation_pp'd
            ,targetTrigger_pp'd] then
            ["| visible =", PP.line]
        else []) ++
        allow_pp'd ++
        targetRootTrigger_pp'd ++
        visible_pp'd ++
        activation_pp'd ++
        targetTrigger_pp'd ++

        available_pp'd ++
        ppActivatedBy_pp'd ++
        removeTrigger_pp'd ++
        cancelTrigger_pp'd ++
        targets ++
        effect_pp'd ++
        removeEffect_pp'd ++
        cancelEffect_pp'd ++
        timeoutEffect_pp'd ++

        (if not $ all null [modifier_pp'd, targetedModifier_pp'd] then
            ["| modifier =", PP.line]
        else []) ++
        modifier_pp'd ++
        targetedModifier_pp'd ++
        maybe [] (\awd_pp'd ->
            ["| comment = <!-- AI decision factors:", PP.line
            ,awd_pp'd, " -->", PP.line]) mawd_pp'd ++
        ["}}", PP.line
        ,"<section end=", nameD, "/>", PP.line
        ]
    where
        extractTargets (StatementBare (GenericLhs e [])) = Just e
        extractTargets stmt = trace ("Unknown in targets array statement: " ++ show stmt) Nothing
        extractTargetsStates (StatementBare (IntLhs e)) = Just e
        extractTargetsStates [pdx| state = !e |] = Just e
        extractTargetsStates stmt = trace ("Unknown in targets array statement: " ++ show stmt) Nothing


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
                    map (\d -> Doc.strictText $ "* " <> Doc.doc2text d) ts
            return [mconcat $ ["| activated_by = "] ++ [PP.line] ++ intersperse PP.line ts' ++ [PP.line]]
        _ -> return [Doc.strictText ""]

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
    actn <- actionName act
    return $ Doc.strictText $ actn <> formatWeight weight
    where
        actionName :: (HOI4Info g, Monad m) =>
            Text -> PPT g m Text
        actionName n
            | "on_monthly_" `T.isPrefixOf` n = do
                let tag = case T.stripPrefix "on_monthly_" n of
                        Just nc -> nc
                        _ -> "<!-- Check game Script -->"
                let actmsg = "<!-- " <> n <>  " -->On every month for "
                tagloc <- flagText (Just HOI4Country) tag
                return $ actmsg <> tagloc
            | "on_weekly_" `T.isPrefixOf` n = do
                let tag = case T.stripPrefix "on_weekly_" n of
                        Just nc -> nc
                        _ -> "<!-- Check game Script -->"
                let actmsg = "<!-- " <> n <>  " -->On every week for "
                tagloc <- flagText (Just HOI4Country) tag
                return $ actmsg <> tagloc
            | "on_daily_" `T.isPrefixOf` n = do
                let tag = case T.stripPrefix "on_daily_" n of
                        Just nc -> nc
                        _ -> "<!-- Check game Script -->"
                let actmsg = "<!-- " <> n <>  " -->On every day for "
                tagloc <- flagText (Just HOI4Country) tag
                return $ actmsg <> tagloc
            | otherwise =
                return $ HM.findWithDefault ("<pre>" <> n <> "</pre>") n actionNameTable

        actionNameTable :: HashMap Text Text
        actionNameTable = HM.fromList
            [("on_ace_killed","<!-- on_ace_killed -->On ace killed")
            ,("on_ace_killed_by_ace","<!-- on_ace_killed_by_ace -->On ace killed by enemy ace")
            ,("on_ace_killed_other_ace","<!-- on_ace_killed_other_ace -->On ace kills enemy ace")
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
            ,("on_weekly","<!-- on_weekly -->On every week")
            ]
ppDecisionSource (HOI4DecSrcNFComplete id loc icon) = do
    iconnf <- do
        iconname <- do
            micon <- getGameInterfaceIfPresent ("GFX_focus_" <> id)
            case micon of
                Nothing -> getGameInterface "goal_unknown" icon
                Just idicon -> return idicon
        return $ "[[File:" <> iconname <> ".png|28px]]"
    return $ Doc.strictText $ mconcat ["Completing the national focus "
        , iconnf
        , " <!-- "
        , id
        , " -->"
        , iquotes't loc
        ]
ppDecisionSource (HOI4DecSrcNFSelect id loc icon) = do
    iconnf <- do
        iconname <- do
            micon <- getGameInterfaceIfPresent ("GFX_focus_" <> id)
            case micon of
                Nothing -> getGameInterface "goal_unknown" icon
                Just idicon -> return idicon
        return $ "[[File:" <> iconname <> ".png|28px]]"
    return $ Doc.strictText $ mconcat ["Selecting the national focus "
        , iconnf
        , " <!-- "
        , id
        , " -->"
        , iquotes't loc
        ]
ppDecisionSource (HOI4DecSrcIdeaOnAdd id loc icon categ) = do
    iconnf <- do
        iconname <- do
            micon <- getGameInterfaceIfPresent ("GFX_idea_" <> id)
            case micon of
                Nothing -> getGameInterface "idea_unknown" icon
                Just idicon -> return idicon
        return $ "[[File:" <> iconname <> ".png|28px]]"
    catloc <- getGameL10n categ
    return $ Doc.strictText $ mconcat ["When the "
        , catloc
        , " "
        , iconnf
        , " <!-- "
        , id
        , " -->"
        , iquotes't loc
        , " is added"
        ]
ppDecisionSource (HOI4DecSrcIdeaOnRemove id loc icon categ) = do
    iconnf <- do
        iconname <- do
            micon <- getGameInterfaceIfPresent ("GFX_idea_" <> id)
            case micon of
                Nothing -> getGameInterface "idea_unknown" icon
                Just idicon -> return idicon
        return $ "[[File:" <> iconname <> ".png|28px]]"
    catloc <- getGameL10n categ
    return $ Doc.strictText $ mconcat ["When the "
        , catloc
        , " "
        , iconnf
        , " <!-- "
        , id
        , " -->"
        , iquotes't loc
        , " is removed"
        ]
ppDecisionSource (HOI4DecSrcCharacterOnAdd idtoken id name) = do
    loc <- do
        mloc <- getGameL10nIfPresent name
        case mloc of
            Just nloc -> return nloc
            _-> getGameL10n idtoken
    return $ Doc.strictText $ mconcat ["When the advisor "
        , " <!-- "
        , id
        , " "
        , idtoken
        , " -->"
        , iquotes't loc
        , " is added"
        ]
ppDecisionSource (HOI4DecSrcCharacterOnRemove idtoken id name) = do
    loc <- do
        mloc <- getGameL10nIfPresent name
        case mloc of
            Just nloc -> return nloc
            _-> getGameL10n idtoken
    return $ Doc.strictText $ mconcat ["When the advisor "
        , " <!-- "
        , id
        , " "
        , idtoken
        , " -->"
        , iquotes't loc
        , " is removed"
        ]
ppDecisionSource (HOI4DecSrcScriptedEffect id _weight) =
    return $ Doc.strictText $ mconcat ["When scripted effect "
        , iquotes't id
        , " is activated"
        ]
ppDecisionSource (HOI4DecSrcBopOnActivate id) = do
    loc <- getGameL10n id
    return $ Doc.strictText $ mconcat ["When reaching the "
        , "<!-- "
        , id
        , " -->"
        , iquotes't loc
        , " balance of power range"
        ]
ppDecisionSource (HOI4DecSrcBopOnDeactivate id) = do
    loc <- getGameL10n id
    return $ Doc.strictText $ mconcat ["When leaving the "
        , "<!-- "
        , id
        , " -->"
        , iquotes't loc
        , " balance of power range"
        ]


findInStmt :: GenericStatement -> [(HOI4DecisionWeight, Text)]
findInStmt [pdx| $lhs = $id |] | lhs == "activate_mission" = [(Nothing, id)]
findInStmt [pdx| activate_targeted_decision = @scr |] = concatMap findInStmt' scr
findInStmt [pdx| %_lhs = @scr |] = findInStmts scr
findInStmt _ = []

findInStmt' :: GenericStatement -> [(HOI4DecisionWeight, Text)]
findInStmt' [pdx| $lhs = $id |] | lhs == "decision" = [(Nothing, id)]
findInStmt' _ = []

findInStmts :: [GenericStatement] -> [(HOI4DecisionWeight, Text)]
findInStmts = concatMap findInStmt

addDecisionSource :: (HOI4DecisionWeight -> HOI4DecisionSource) -> [(HOI4DecisionWeight, Text)] -> [(Text, HOI4DecisionSource)]
addDecisionSource ds = map (\t -> (snd t, ds (fst t)))

findInOptions :: Text -> [HOI4Option] -> [(Text, HOI4DecisionSource)]
findInOptions decisionId = concatMap (\o ->
    (\optName -> addDecisionSource (const (HOI4DecSrcOption decisionId optName)) (maybe [] (concatMap findInStmt) (hoi4opt_effects o)))
    (fromMaybe "(Un-named option)" (hoi4opt_name o)))

addDecisionTriggers :: HOI4DecisionTriggers -> [(Text, HOI4DecisionSource)] -> HOI4DecisionTriggers
addDecisionTriggers hm l = foldl' ins hm l
    where
        ins :: HOI4DecisionTriggers -> (Text, HOI4DecisionSource) -> HOI4DecisionTriggers
        ins hm (k, v) = HM.alter (\case
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
            addDecisionSource (const (HOI4DecSrcImmediate eventId)) (maybe [] findInStmts (hoi4evt_immediate evt))
        findInEvent _ = []

findActivatedDecisionsInDecisions :: HOI4DecisionTriggers -> [HOI4Decision] -> HOI4DecisionTriggers
findActivatedDecisionsInDecisions hm ds = addDecisionTriggers hm (concatMap findInDecision ds)
    where
        findInDecision :: HOI4Decision -> [(Text, HOI4DecisionSource)]
        findInDecision d =
            addDecisionSource (const (HOI4DecSrcDecComplete (dec_name d) (dec_name_loc d))) (maybe [] findInStmts (dec_complete_effect d)) ++
            addDecisionSource (const (HOI4DecSrcDecRemove (dec_name d) (dec_name_loc d))) (maybe [] findInStmts (dec_remove_effect d)) ++
            addDecisionSource (const (HOI4DecSrcDecCancel (dec_name d) (dec_name_loc d))) (maybe [] findInStmts (dec_cancel_effect d)) ++
            addDecisionSource (const (HOI4DecSrcDecTimeout (dec_name d) (dec_name_loc d))) (maybe [] findInStmts (dec_timeout_effect d))

findActivatedDecisionsInOnActions :: HOI4DecisionTriggers -> [GenericStatement] -> HOI4DecisionTriggers
findActivatedDecisionsInOnActions hm scr = foldl' findInAction hm scr
    where
        findInAction :: HOI4DecisionTriggers -> GenericStatement -> HOI4DecisionTriggers
        findInAction hm [pdx|on_actions = @stmts |] = foldl' findInAction hm stmts
        findInAction hm [pdx| $lhs = @scr |] = addDecisionTriggers hm (addDecisionSource (HOI4DecSrcOnAction lhs) (findInStmts scr))
        findInAction hm stmt = trace ("Unknown on_actions statement: " ++ show stmt) hm

findActivatedDecisionsInNationalFocus :: HOI4DecisionTriggers -> [HOI4NationalFocus] -> HOI4DecisionTriggers
findActivatedDecisionsInNationalFocus hm nf = addDecisionTriggers hm (concatMap findInFocus nf)
    where
        findInFocus :: HOI4NationalFocus -> [(Text, HOI4DecisionSource)]
        findInFocus f =
            addDecisionSource (const (HOI4DecSrcNFComplete (nf_id f) (nf_name_loc f) (nf_icon f))) (maybe [] findInStmts (nf_completion_reward f)) ++
            addDecisionSource (const (HOI4DecSrcNFSelect (nf_id f) (nf_name_loc f) (nf_icon f))) (maybe [] findInStmts (nf_select_effect f))

findActivatedDecisionsInIdeas :: HOI4DecisionTriggers -> [HOI4Idea] -> HOI4DecisionTriggers
findActivatedDecisionsInIdeas hm idea = addDecisionTriggers hm (concatMap findInIdea idea)
    where
        findInIdea :: HOI4Idea -> [(Text, HOI4DecisionSource)]
        findInIdea idea =
            addDecisionSource (const (HOI4DecSrcIdeaOnAdd (id_id idea) (id_name_loc idea) (id_picture idea) (id_category idea))) (maybe [] findInStmts (id_on_add idea)) ++
            addDecisionSource (const (HOI4DecSrcIdeaOnRemove (id_id idea) (id_name_loc idea) (id_picture idea) (id_category idea))) (maybe [] findInStmts (id_on_remove idea))

findActivatedDecisionsInCharacters :: HOI4DecisionTriggers -> [HOI4Advisor] -> HOI4DecisionTriggers
findActivatedDecisionsInCharacters hm hChar = addDecisionTriggers hm (concatMap findInCharacter hChar)
    where
        findInCharacter :: HOI4Advisor -> [(Text, HOI4DecisionSource)]
        findInCharacter hChar =
            addDecisionSource (const (HOI4DecSrcCharacterOnAdd (adv_idea_token hChar) (adv_cha_id hChar) (adv_cha_name hChar))) (maybe [] findInStmts (adv_on_add hChar)) ++
            addDecisionSource (const (HOI4DecSrcCharacterOnRemove (adv_idea_token hChar) (adv_cha_id hChar) (adv_cha_name hChar))) (maybe [] findInStmts (adv_on_remove hChar))

findActivatedDecisionsInScriptedEffects :: HOI4DecisionTriggers -> [GenericStatement] -> HOI4DecisionTriggers
findActivatedDecisionsInScriptedEffects hm scr = foldl' findInScriptEffect hm scr -- needs editing
    where
        findInScriptEffect :: HOI4DecisionTriggers -> GenericStatement -> HOI4DecisionTriggers
        findInScriptEffect hm [pdx| $lhs = @scr |] = addDecisionTriggers hm (addDecisionSource (HOI4DecSrcScriptedEffect lhs) (findInStmts scr))
        findInScriptEffect hm stmt = trace ("Unknown on_actions statement: " ++ show stmt) hm

findActivatedDecisionsInBops :: HOI4DecisionTriggers -> [HOI4BopRange] -> HOI4DecisionTriggers
findActivatedDecisionsInBops hm hBop = addDecisionTriggers hm (concatMap findInCharacter hBop)
    where
        findInCharacter :: HOI4BopRange -> [(Text, HOI4DecisionSource)]
        findInCharacter hBop =
            addDecisionSource (const (HOI4DecSrcBopOnActivate (bop_id hBop))) (maybe [] findInStmts (bop_on_activate hBop)) ++
            addDecisionSource (const (HOI4DecSrcBopOnDeactivate (bop_id hBop))) (maybe [] findInStmts (bop_on_deactivate hBop))