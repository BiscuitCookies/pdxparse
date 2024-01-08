{-
Module      : HOI4.NationalFocus
Description : Feature handler for Hearts of Iron IV decisions
-}
module HOI4.NationalFocus (
        parseHOI4NationalFocuses
        ,writeHOI4NationalFocuses
    ) where

import Debug.Trace (trace, traceM)

import System.FilePath (takeBaseName)

import Control.Arrow ((&&&))
import Control.Monad (foldM, forM)
import Control.Monad.Except (MonadError (..))
import Control.Monad.State (gets)
import Control.Monad.Trans (MonadIO (..))

import Data.Char (toLower)
import Data.Maybe (catMaybes, fromMaybe, mapMaybe)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T
import Text.PrettyPrint.Leijen.Text (Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP

import Abstract -- everything
import qualified Doc
import FileIO (Feature (..), writeFeatures)
 -- everything
import QQ (pdx)
import SettingsTypes ( PPT, Settings (..)
                     , IsGame (..), IsGameData (..), IsGameState (..)
                     , getGameL10n, getGameL10nIfPresent
                     , setCurrentFile, withCurrentFile
                     , hoistErrors, hoistExceptions
                     , indentUp
                     , getGameInterface, getGameInterfaceIfPresent)
import HOI4.Common -- everything

-- | Empty national focus. Starts off Nothing/empty everywhere, except id and name
-- (which should get filled in immediately).
newHOI4NationalFocus :: HOI4NationalFocus
newHOI4NationalFocus = HOI4NationalFocus "(Unknown)" "(Unknown)" Nothing Nothing "GFX_goal_unknown" undefined Nothing [] Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing undefined

-- | Take the decisions scripts from game data and parse them into decision
-- data structures.
parseHOI4NationalFocuses :: (IsGameData (GameData g), IsGameState (GameState g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text HOI4NationalFocus)
parseHOI4NationalFocuses scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr ->
                setCurrentFile sourceFile $ mapM parseHOI4NationalFocus $ concatMap mapTree scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing national focus: " ++ T.unpack err
            return HM.empty
        Right nfFilesOrErrors ->
            flip HM.traverseWithKey nfFilesOrErrors $ \sourceFile enfs ->
                fmap (mkNfMap . catMaybes) . forM enfs $ \case
                    Left err -> do
                        traceM $ "Error parsing national focus in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right nfocus -> return nfocus
    where
        mkNfMap :: [HOI4NationalFocus] -> HashMap Text HOI4NationalFocus
        mkNfMap = HM.fromList . map (nf_id &&& id)

        mapTree scr = case scr of
            [pdx| focus_tree = @focus |] -> focus
            [pdx| shared_focus = @_ |] -> [scr]
            [pdx| joint_focus = @_ |] -> [scr]
            _ -> []

-- | Parse a statement in an national focus file. Some statements aren't
-- national focus'; for those, and for any obvious errors, return Right Nothing.
parseHOI4NationalFocus :: (IsGameState (GameState g), IsGameData (GameData g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe HOI4NationalFocus))
parseHOI4NationalFocus (StatementBare _) = throwError "bare statement at top level"
parseHOI4NationalFocus [pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] ->
            if not (id == "focus" || id == "shared_focus" || id == "joint_focus") then
                return (Right Nothing)
            else
                withCurrentFile $ \file -> do
                    nfNameLoc <- getGameL10n $ fromMaybe (getNFId parts) (getNFTxt parts)
                    nfNameDesc <- getGameL10nIfPresent $ fromMaybe (getNFId parts) (getNFTxt parts) <> "_desc"
                    nnf <- hoistErrors $ foldM nationalFocusAddSection
                                                (Just newHOI4NationalFocus {nf_path = file
                                                                            ,nf_name_loc = nfNameLoc
                                                                            ,nf_name_desc = nfNameDesc})
                                                parts
                    case nnf of
                        Left err -> return (Left err)
                        Right Nothing -> return (Right Nothing)
                        Right (Just nf) -> withCurrentFile $ \file ->
                            return (Right (Just nf))
        _ -> throwError "unrecognized form for national focus (LHS)"
    _ -> return (Right Nothing)
    where
        getNFId ([pdx| id = $nfname|]:_) = nfname
        getNFId (_:xs) = getNFId xs
        getNFId [] = "(unknown)"
        getNFTxt ([pdx| text = $nfname|]:_) = Just nfname
        getNFTxt (_:xs) = getNFTxt xs
        getNFTxt [] = Nothing
parseHOI4NationalFocus _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for national focus in " <> T.pack file)

-- | Interpret one section of an national focus. If understood, add it to the
-- event data. If not understood, throw an exception.
nationalFocusAddSection :: (IsGameState (GameState g), MonadError Text m) =>
    Maybe HOI4NationalFocus -> GenericStatement -> PPT g m (Maybe HOI4NationalFocus)
nationalFocusAddSection Nothing _ = return Nothing
nationalFocusAddSection nf stmt
    = return $ (`nationalFocusAddSection'` stmt) <$> nf
    where
        nationalFocusAddSection' nf stmt@[pdx| $lhs = %rhs |] = case T.map toLower lhs of
            "id" -> case rhs of
                GenericRhs txt [] -> nf { nf_id = txt}
                _-> trace ("bad nf id in: " ++ show stmt) nf
            "text" -> case rhs of
                GenericRhs txt [] -> nf { nf_text = Just txt}
                _-> trace ("bad nf id in: " ++ show stmt) nf
            "completion_reward" -> case rhs of
                CompoundRhs [] ->
                    nf
                CompoundRhs scr -> nf { nf_completion_reward = Just scr }
                _-> trace "bad nf completion_reward" nf
            "icon" -> case rhs of
                GenericRhs txt [] ->
                    let txtd = if "GFX_" `T.isPrefixOf` txt then txt else "GFX_" <> txt in
                    nf { nf_icon = txtd}
                StringRhs txt ->
                    let txtd = if "GFX_" `T.isPrefixOf` txt then txt else "GFX_" <> txt in
                    nf { nf_icon = txtd}
                CompoundRhs _ ->
                    nf { nf_icon = "Multiple Pictures possible, check script."}
                _-> trace ("bad nf icon in: " ++ show stmt) nf
            "cost" -> case rhs of
                (floatRhs -> Just num) -> nf {nf_cost = num}
                _ -> trace ("bad nf cost in: " ++ show stmt) nf
            "allow_branch" -> case rhs of
                CompoundRhs [] ->
                    nf
                CompoundRhs scr -> nf { nf_allow_branch = Just scr }
                _-> trace "bad nf allow_branch" nf
            "x" -> nf
            "y" -> nf
            "prerequisite" -> case rhs of
                CompoundRhs [] ->
                    nf
                CompoundRhs scr ->
                    nf { nf_prerequisite = nf_prerequisite nf ++ [Just scr] }
                _-> trace "bad nf prerequisite" nf
            "mutually_exclusive" -> case rhs of
                CompoundRhs [] ->
                    nf
                CompoundRhs scr ->
                    nf { nf_mutually_exclusive = Just scr }
                _-> trace "bad nf mutually_exclusive" nf
            "available" -> case rhs of
                CompoundRhs [] ->
                    nf
                CompoundRhs scr -> nf { nf_available = Just scr }
                _-> trace "bad nf available" nf
            "bypass" -> case rhs of
                CompoundRhs [] ->
                    nf
                CompoundRhs scr -> nf { nf_bypass = Just scr }
                _-> trace "bad nf bypass" nf
            "completion_reward_joint_originator" -> case rhs of
                CompoundRhs [] ->
                    nf
                CompoundRhs scr -> nf { nf_joint_complete_origin = Just scr }
                _-> trace "bad nf joint reward orginator" nf
            "completion_reward_joint_member" -> case rhs of
                CompoundRhs [] ->
                    nf
                CompoundRhs scr -> nf { nf_joint_complete_member = Just scr }
                _-> trace "bad nf joint reward member" nf
            "joint_trigger" -> case rhs of
                CompoundRhs [] ->
                    nf
                CompoundRhs scr -> nf { nf_joint_trigger = Just scr }
                _-> trace "bad nf joint trigger" nf
            "cancel" -> nf
            "cancelable" -> nf --bool
            "historical_ai" -> nf
            "available_if_capitulated" -> nf --bool
            "cancel_if_invalid" -> nf --bool
            "continue_if_invalid" -> nf --bool
            "will_lead_to_war_with" ->  nf
            "search_filters" -> nf
            "select_effect" -> case rhs of
                CompoundRhs [] ->
                    nf
                CompoundRhs scr -> nf {nf_select_effect = Just scr}
                _-> trace ("bad nf select_effect in: " ++ show stmt) nf
            "ai_will_do" -> nf --Do we want to deal with aistuff with focus' ?
            "complete_tooltip" ->  case rhs of
                CompoundRhs [] ->
                    nf
                CompoundRhs scr -> nf { nf_complete_tooltip = Just scr }
                _-> trace "bad nf complete tooltip" nf
            "offset" -> nf
            "relative_position_id" -> nf
            "text_icon" -> nf -- unknown what it does for now. AAT
            "dynamic" -> nf
            other -> trace ("unknown national focus section: " ++ show other ++ " for " ++ show stmt) nf
        nationalFocusAddSection' nf _
            = trace "unrecognised form for national focus section" nf



writeHOI4NationalFocuses :: (HOI4Info g, MonadIO m) => PPT g m ()
writeHOI4NationalFocuses = do
--    nationalFocuses <- getNationalFocus
    nationalFocuses <- getNationalFocusScripts
    pathNF <- parseHOI4NationalFocusesPath nationalFocuses --mkNfPathMap $ HM.elems nationalFocuses
    let pathedNationalFocus :: [Feature [HOI4NationalFocus]]
        pathedNationalFocus = map (\nf -> Feature {
                                        featurePath = Just $ nf_path $ head nf
                                    ,   featureId = Just (T.pack $ takeBaseName $ nf_path $ head nf) <> Just ".txt"
                                    ,   theFeature = Right nf })
                              (HM.elems pathNF)
    writeFeatures "national_focus"
                  pathedNationalFocus
                  ppNationalFocuses
--    where
--        mkNfPathMap :: [HOI4NationalFocus] -> HashMap FilePath [HOI4NationalFocus]
--        mkNfPathMap nf =
--            let xs = reverse $ map (nf_path &&& id) nf in
--            HM.fromListWith (++) [ (k, [v]) | (k, v) <- xs ]

parseHOI4NationalFocusesPath :: (IsGameData (GameData g), IsGameState (GameState g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap FilePath [HOI4NationalFocus])
parseHOI4NationalFocusesPath scripts = do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr ->
                setCurrentFile sourceFile $ mapM parseHOI4NationalFocus $ concatMap mapTree scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing national focus: " ++ T.unpack err
            return HM.empty
        Right nfFilesOrErrors ->
            return $ HM.filter (not . null) $ flip HM.mapWithKey nfFilesOrErrors $ \sourceFile enfs ->
                mapMaybe (\case
                    Left err -> do
                        traceM $ "Error parsing national focus in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        Nothing
                    Right nfocus -> nfocus)
                    enfs
    where
        mapTree scr = case scr of
            [pdx| focus_tree = @focus |] -> focus
            [pdx| shared_focus = @_ |] -> [scr]
            [pdx| joint_focus = @_ |] -> [scr]
            _ -> []

ppNationalFocuses :: forall g m. (HOI4Info g, Monad m) => [HOI4NationalFocus] -> PPT g m Doc
ppNationalFocuses nfs = do
    version <- gets (gameVersion . getSettings)
    nfDoc <- mapM (scope HOI4Country . ppNationalFocus) nfs -- Better to leave unsorted? (sortOn (sortName . nf_name_loc) nfs)
    return . mconcat $
        [ "{{Version|", Doc.strictText version, "}}", PP.line
        , "{| class=\"mildtable\" {{buffer}}", PP.line
        , "! style=\"width: 30%;\" | Focus", PP.line
        , "! style=\"width: 30%;\" | Prerequisites", PP.line
        , "! style=\"width: 40%;\" | Effects", PP.line
        ] ++ nfDoc ++
        [ "|}", PP.line
        ]

--sortName :: Text -> Text
--sortName n =
--    let ln = T.toLower n
--        nn = T.stripPrefix "the " ln
--    in fromMaybe ln nn

ppNationalFocus :: forall g m. (HOI4Info g, Monad m) => HOI4NationalFocus -> PPT g m Doc
ppNationalFocus nf = setCurrentFile (nf_path nf) $ do
    let nfArg :: (HOI4NationalFocus -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
        nfArg field fmt
            = maybe (return [])
                (\field_content -> do
                    content_pp'd <- fmt field_content
                    return
                        [content_pp'd
                        ,PP.line])
            (field nf)
        nfArgExtra :: Doc -> (HOI4NationalFocus -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
        nfArgExtra extra field fmt
            = maybe (return [])
                (\field_content -> do
                    content_pp'd <- fmt field_content
                    return
                        ["{{",extra,"|",PP.line
                        ,content_pp'd
                        ,"}}"
                        ,PP.line])
            (field nf)
        nfArgClari :: Doc -> (HOI4NationalFocus -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
        nfArgClari extra field fmt
            = maybe (return [])
                (\field_content -> do
                    content_pp'd <- fmt field_content
                    return
                        [extra, PP.line
                        ,content_pp'd
                        ,PP.line])
            (field nf)
    icon_pp <- do
        micon <- getGameInterfaceIfPresent ("GFX_focus_" <> nf_id nf)
        case micon of
            Nothing -> getGameInterface "goal_unknown" (nf_icon nf)
            Just idicon -> return idicon
    prerequisite_pp <- ppPrereq $ catMaybes $ nf_prerequisite nf
    allowBranch_pp <- ppAllowBranch $ nf_allow_branch nf
    mutuallyExclusive_pp <- ppMutuallyExclusive $ nf_mutually_exclusive nf
    available_pp <- nfArg nf_available ppScript
    joint_trigger_pp <- nfArgClari "<!-- joint_trigger -->Requirements for joint rewards:" nf_joint_trigger ppScript
    joint_reward_member_pp <- nfArgClari "Reward for joint member:" nf_joint_complete_member ppScript
    joint_reward_origin_pp <- nfArgClari "Reward for joint country that completed:" nf_joint_complete_origin ppScript
    complete_tool_pp <- nfArgClari "<!-- Tooltip shown for completion ->Completion tooltip:" nf_complete_tooltip ppScript
    bypass_pp <- nfArgExtra "bypass" nf_bypass ppScript
    completionReward_pp <- setIsInEffect True $ nfArg nf_completion_reward ppScript
    selectEffect_pp <- setIsInEffect True $ nfArgExtra "select" nf_select_effect ppScript
    return . mconcat $
        [ "|- id = \"", Doc.strictText (nf_name_loc nf),"\"" , PP.line
        , "| {{iconbox|image=", Doc.strictText icon_pp, ".png ", PP.line
        , "| ", Doc.strictText (nf_name_loc nf) , "<!-- ", Doc.strictText (nf_id nf), " -->", PP.line
        , "| ",maybe mempty (Doc.strictText . Doc.nl2br) (nf_name_desc nf), PP.line , "}}", PP.line
        , "| ", PP.line]++
        allowBranch_pp ++
        prerequisite_pp ++
        mutuallyExclusive_pp ++
        available_pp ++
        joint_trigger_pp ++
        bypass_pp ++
        [ "| ", PP.line]++
        completionReward_pp ++
        joint_reward_origin_pp ++
        joint_reward_member_pp ++
--        complete_tool_pp ++
        selectEffect_pp

ppPrereq :: (HOI4Info g, Monad m) => [GenericScript] -> PPT g m [Doc]
ppPrereq [] = return [""]
ppPrereq prereqs = mapM ppTitle prereqs
    where
        ppTitle prereq = do
            let reqfol = if length prereq == 1 then
                    [Doc.strictText "* Requires the following:", PP.line]
                else
                    [Doc.strictText "* Requires ''one'' of the following:", PP.line]
            reqs <- sequenceA
                [indentUp (ppScript prereq), pure PP.line
                ]
            return . mconcat $ reqfol ++ reqs

ppMutuallyExclusive :: (HOI4Info g, Monad m) => Maybe GenericScript -> PPT g m [Doc]
ppMutuallyExclusive Nothing = return [""]
ppMutuallyExclusive (Just mex) = ppTitle mex
    where
        ppTitle mexc = do
            let mexfol = mconcat [Doc.strictText "* {{icon|ExclusiveM}} Mutually exclusive with:", PP.line]
            mexcpp <- indentUp (ppScript mexc)
            let excl = [mexfol, mexcpp, PP.line]
            return excl

ppAllowBranch :: (HOI4Info g, Monad m) => Maybe GenericScript -> PPT g m [Doc]
ppAllowBranch Nothing = return [""]
ppAllowBranch (Just abr) = ppTitle abr
    where
        ppTitle awbr = do
            let awbrfol = mconcat [Doc.strictText "* Allow Branch if:", PP.line]
            awbrpp <- indentUp (ppScript awbr)
            let allwbr = [awbrfol, awbrpp, PP.line]
            return allwbr
