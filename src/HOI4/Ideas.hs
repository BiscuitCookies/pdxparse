{-|
Module      : HOI4.Ideas
Description : Feature handler for Hearts of Iron IV idea groups
-}
module HOI4.Ideas (
        HOI4Idea (..)
    ,   parseHOI4Ideas
    ,   writeHOI4Ideas
    ) where

import Debug.Trace (trace, traceM)

import Control.Arrow ((&&&))
import Control.Monad (foldM, forM)
import Control.Monad.Except (ExceptT (..), MonadError (..))
import Control.Monad.State (MonadState (..), gets)
import Control.Monad.Trans (MonadIO (..))

import Data.Char (toLower)
import Data.Maybe (catMaybes, fromMaybe, isJust, mapMaybe)
import Data.Monoid ((<>))
import Data.List (intersperse, foldl', intercalate)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T
import Text.PrettyPrint.Leijen.Text (Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP
import System.FilePath ((</>), takeBaseName)

import Abstract -- everything
import qualified Doc
import FileIO (Feature (..), writeFeatures)
import HOI4.Messages -- everything
-- everything
import MessageTools (iquotes, plainNum)
import HOI4.Handlers (flagText, getStateLoc, plainMsg')
import HOI4.SpecialHandlers (getLeaderTraits, getbaretraits)
import QQ (pdx)
import SettingsTypes ( PPT, Settings (..), Game (..)
                     , IsGame (..), IsGameData (..), IsGameState (..)
                     , getGameL10n, getGameL10nIfPresent
                     , setCurrentFile, withCurrentFile, withCurrentIndent
                     , hoistErrors, hoistExceptions
                     , concatMapM)
import HOI4.Common -- everything
import GHC.RTS.Flags (RTSFlags(costCentreFlags))

-- | Take the idea group scripts from game data and parse them into idea group
-- data structures.
parseHOI4Ideas :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text HOI4Idea)
parseHOI4Ideas scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr ->
                setCurrentFile sourceFile $ concat <$> mapM parseHOI4IdeaGroup (case scr of
                    [[pdx| ideas = @mods |]] -> mods
                    _ -> []))
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing ideas: " ++ T.unpack err
            return HM.empty
        Right ideasFilesOrErrors ->
            flip HM.traverseWithKey ideasFilesOrErrors $ \sourceFile eidea ->
                fmap (mkIdeaMap . catMaybes) . forM eidea $ \case
                    Left err -> do
                        traceM $ "Error parsing ideas in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right iidea -> return iidea
                where mkIdeaMap :: [HOI4Idea] -> HashMap Text HOI4Idea
                      mkIdeaMap = HM.fromList . map (id_id &&& id)

-- | Parse one file's idea groups scripts into idea data structures.
parseHOI4IdeaGroup :: (IsGameData (GameData g), IsGameState (GameState g), Monad m) =>
    GenericStatement -> PPT g (ExceptT Text m) [Either Text (Maybe HOI4Idea)]
parseHOI4IdeaGroup stmt@(StatementBare _) = throwError "bare statement at top level"
parseHOI4IdeaGroup [pdx| $left = @scr |]
    = forM scr $ \stmt -> (Right <$> parseHOI4Idea stmt left)
                            `catchError` (return . Left)
parseHOI4IdeaGroup [pdx| %check = %_ |] = case check of
    AtLhs _ -> return [Right Nothing]
    _-> throwError "unrecognized form for idea block (LHS)"
parseHOI4IdeaGroup _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for ideas in " <> T.pack file)

-- | Empty idea. Starts off Nothing everywhere, except id and name
-- (should get filled in immediately).
newIdea :: HOI4Idea
newIdea = HOI4Idea undefined undefined "<!-- Check Script -->" undefined "GFX_idea_unknown" Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing undefined undefined Nothing Nothing

-- | Parse one idea script into a idea data structure.
parseHOI4Idea :: (IsGameData (GameData g), IsGameState (GameState g), Monad m) =>
    GenericStatement -> Text -> PPT g (ExceptT Text m) (Maybe HOI4Idea)
parseHOI4Idea [pdx| $ideaName = %rhs |] category = case rhs of
    CompoundRhs parts -> do
        idName_loc <- getGameL10n ideaName
        let idPicture = "GFX_idea_" <> ideaName
        idDesc <- getGameL10nIfPresent $ ideaName <> "_desc"
        withCurrentFile $ \sourcePath ->
            foldM ideaAddSection
                  (Just (newIdea { id_id = ideaName
                              , id_name = ideaName
                              , id_name_loc = idName_loc
                              , id_desc_loc = idDesc
                              , id_picture = idPicture
                              , id_path = sourcePath </> T.unpack category -- so ideas are divided into maps for the cateogry, should I loc or not?
                              , id_category = category}))
                  parts
    GenericRhs txt [] -> if ideaName == "designer" || ideaName == "use_list_view" || ideaName == "law" then return Nothing else throwError "unrecognized form for idea (RHS) "
    _ -> throwError "unrecognized form for idea (RHS)"
parseHOI4Idea [pdx| %check = %_ |] _ = case check of
    AtLhs _ -> return Nothing
    _-> throwError "unrecognized form for idea block (LHS)"
parseHOI4Idea _ _ = throwError "unrecognized form for idea (LHS)"

-- | Interpret one section of an opinion modifier. If understood, add it to the
-- event data. If not understood, throw an exception.
ideaAddSection :: (IsGameState (GameState g), MonadError Text m) =>
    Maybe HOI4Idea -> GenericStatement -> PPT g m (Maybe HOI4Idea)
ideaAddSection Nothing _ = return Nothing
ideaAddSection iidea stmt
    = return $ (`ideaAddSection'` stmt) <$> iidea
    where
        ideaAddSection' iidea stmt@[pdx| $lhs = %rhs |] = case T.map toLower lhs of
            "picture"   -> case rhs of
                GenericRhs txt [] ->
                    let txtd = if "GFX_idea_" `T.isPrefixOf` txt then txt else "GFX_idea_" <> txt in
                    iidea { id_picture = txtd }
                _-> trace "bad idea picture" iidea
            "name"      -> case rhs of
                GenericRhs txt [] -> iidea { id_name = txt }
                _-> trace "bad idea name" iidea
            "modifier"  -> case rhs of
                CompoundRhs [] -> iidea
                CompoundRhs scr -> iidea { id_modifier = Just stmt }
                _-> trace "bad idea modifer" iidea
            "targeted_modifier" -> case rhs of
                CompoundRhs [] -> iidea
                CompoundRhs scr -> let oldstmt = fromMaybe [] (id_targeted_modifier iidea) in
                    iidea { id_targeted_modifier = Just (oldstmt ++ [stmt]) }
                _-> trace "bad idea targeted_modifier" iidea
            "research_bonus" -> case rhs of
                CompoundRhs [] -> iidea
                CompoundRhs scr -> iidea { id_research_bonus = Just stmt }
                _-> trace "bad idea reearch_bonus" iidea
            "equipment_bonus" -> case rhs of
                CompoundRhs [] -> iidea
                CompoundRhs scr -> iidea { id_equipment_bonus = Just stmt }
                _-> trace "bad idea equipment_bonus" iidea
            "allowed" -> case rhs of
                CompoundRhs [] -> iidea
                CompoundRhs scr -> iidea { id_allowed = Just scr }
                _-> trace "bad idea allowed" iidea
            "visible" -> case rhs of
                CompoundRhs [] -> iidea
                CompoundRhs scr -> iidea { id_visible = Just scr }
                _-> trace "bad idea visible" iidea
            "available" -> case rhs of
                CompoundRhs [] -> iidea
                CompoundRhs scr -> iidea { id_available = Just scr }
                _-> trace "bad idea available" iidea
            "on_add" -> case rhs of
                CompoundRhs [] -> iidea
                CompoundRhs scr -> iidea { id_on_add = Just scr }
                _-> trace "bad idea on_add" iidea
            "on_remove" -> case rhs of
                CompoundRhs [] -> iidea
                CompoundRhs scr -> iidea { id_on_remove = Just scr }
                _-> trace "bad idea on_remove" iidea
            "cancel" -> case rhs of --removes idea if true
                CompoundRhs [] -> iidea
                CompoundRhs scr -> iidea { id_cancel = Just scr }
                _-> trace "bad idea cancel" iidea
            "do_effect" -> case rhs of --disabled modifiers if False
                CompoundRhs [] -> iidea
                CompoundRhs scr -> iidea { id_do_effect = Just scr }
                _-> trace "bad idea do_effect" iidea
            "rule" -> case rhs of
                CompoundRhs [] -> iidea
                CompoundRhs scr -> iidea { id_rule = Just scr }
                _-> trace "bad idea rule" iidea
            "allowed_civil_war" -> case rhs of
                CompoundRhs [] -> iidea
                CompoundRhs scr -> iidea { id_allowed_civil_war = Just scr }
                _-> trace "bad idea allowed_civil_war" iidea
            "ai_will_do"        -> iidea
            "cancel_if_invalid" -> iidea
            "removal_cost"      -> iidea
            "level"             -> iidea
            "allowed_to_remove" -> iidea
            "cost"              -> case rhs of
                (floatRhs -> Just num) -> iidea { id_cost = Just num }
                _-> trace "bad idea cost" iidea
            "traits"            -> case rhs of
                CompoundRhs [] -> iidea
                CompoundRhs scr -> iidea { id_traits = Just stmt }
                _-> trace "bad idea traits" iidea
            "ledger"            -> iidea
            "default"           -> iidea
            other               -> trace ("unknown idea section: " ++ T.unpack other) iidea
        ideaAddSection' iidea _
            = trace "unrecognised form for idea section" iidea

writeHOI4Ideas :: (HOI4Info g, MonadIO m) => PPT g m ()
writeHOI4Ideas = do
    ideas <- getIdeaScripts
    interface <- getInterfaceGFX
    pathIDS <- parseHOI4IdeasPath ideas
    let pathedIdea :: [Feature [HOI4Idea]]
        pathedIdea = map (\ids -> Feature {
                                        featurePath = Just $ id_path $ head ids
                                    ,   featureId = Just (T.pack $ takeBaseName $ id_path $ head ids) <> Just ".txt"
                                    ,   theFeature = Right ids })
                              (HM.elems pathIDS)
    writeFeatures "ideas"
                  pathedIdea
                  (ppIdeas interface)

parseHOI4IdeasPath :: (IsGameData (GameData g), IsGameState (GameState g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap FilePath [HOI4Idea])
parseHOI4IdeasPath scripts = do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr ->
                setCurrentFile sourceFile $ concat <$> mapM parseHOI4IdeaGroup (case scr of
                    [[pdx| ideas = @mods |]] -> mods
                    _ -> []))
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

ppIdeas :: forall g m. (HOI4Info g, Monad m) => HashMap Text Text -> [HOI4Idea] -> PPT g m Doc
ppIdeas gfx nfs = do
    version <- gets (gameVersion . getSettings)
    nfDoc <- mapM (scope HOI4Country . ppIdea gfx) nfs -- Better to leave unsorted? (sortOn (sortName . nf_name_loc) nfs)
    return . mconcat $
        [ "{{Version|", Doc.strictText version, "}}", PP.line
        , "{| class=\"mildtable\" ", PP.line
        , "! style=\"width: 30%;\" | Category", PP.line
        , "! style=\"width: 30%;\" | idea", PP.line
        , "! style=\"width: 30%;\" | image", PP.line
        , "! style=\"width: 30%;\" | desc", PP.line
        , "! style=\"width: 40%;\" | Prerequisites", PP.line
        , "! style=\"width: 40%;\" | Effects", PP.line
        , "! style=\"width: 40%;\" | costs", PP.line
        ] ++ nfDoc ++
        [ "|}", PP.line
        ]

ppIdea :: forall g m. (HOI4Info g, Monad m) => HashMap Text Text -> HOI4Idea -> PPT g m Doc
ppIdea gfx id = setCurrentFile (id_path id) $ do
    let nfArg :: (HOI4Idea -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
        nfArg field fmt
            = maybe (return [])
                (\field_content -> do
                    content_pp'd <- fmt field_content
                    return
                        [content_pp'd
                        ,PP.line])
            (field id)
    let nfArgExtra :: Doc -> (HOI4Idea -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
        nfArgExtra extra field fmt
            = maybe (return [])
                (\field_content -> do
                    content_pp'd <- fmt field_content
                    return
                        ["{{",extra,"|",PP.line
                        ,content_pp'd
                        ,"}}"
                        ,PP.line])
            (field id)
        icon_pp = HM.findWithDefault "idea_unknown" (id_picture id) gfx
    name_pp <- getGameL10n $ id_name id
    prerequisite_pp <- nfArg id_available ppScript
    allowBranch_pp <- nfArg id_allowed ppScript
    visible_pp <- nfArg id_visible ppScript
    mod <- nfArg id_modifier ppStatement
    equipmod <- nfArg id_equipment_bonus ppStatement
    resmod <- nfArg id_research_bonus ppStatement
    tarmod <- nfArg id_targeted_modifier ppScript
    available_pp <- nfArg id_available ppScript
    traitmsg <- case id_traits id of
        Just [pdx| %_ = @arr |] -> do
            let traitbare = mapMaybe getbaretraits arr
            concatMapM getLeaderTraits traitbare
        _-> return []
    traitmsg_pp <- imsg2doc traitmsg
    return . mconcat $
        [ "|- ", PP.line
        , "| ", Doc.strictText $ id_category id, PP.line
        , "| [[File:", Doc.strictText icon_pp, ".png]]", PP.line
        , "| ", Doc.strictText name_pp, "<!-- ", Doc.strictText (id_id id), " -->", PP.line
        , "| ",maybe mempty (Doc.strictText . Doc.nl2br) (id_desc_loc id), PP.line
        , "| ",PP.line]++
        allowBranch_pp ++
        prerequisite_pp ++
        available_pp ++
        [ "| ",PP.line]++
        mod ++
        equipmod ++
        tarmod ++
        resmod ++
        [traitmsg_pp, PP.line
        , "| ", if id_category id == "country" then mempty else maybe "150" plainNum (id_cost id), PP.line]
