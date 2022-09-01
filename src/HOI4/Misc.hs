{-
Module      : HOI4.Misc
Description : Feature handler for miscellaneous features in Hearts of Iron IV
-}
module HOI4.Misc (
         parseHOI4CountryHistory
        ,parseHOI4Interface
        ,parseHOI4Characters
        ,parseHOI4CountryLeaderTraits
        ,parseHOI4UnitLeaderTraits
        ,parseHOI4Terrain
        ,parseHOI4Ideology
        ,parseHOI4Effects
        ,parseHOI4Triggers
    ) where

import Debug.Trace (trace, traceM)

import Control.Arrow ((&&&))
import Control.Monad (foldM, forM)
import Control.Monad.Except (ExceptT (..), MonadError (..))
import Control.Monad.State (MonadState (..), gets)
import Control.Monad.Trans (MonadIO (..))

import Data.Char (toLower)
import Data.List (foldl')
import Data.Maybe (catMaybes, fromMaybe, mapMaybe)
import Data.Monoid ((<>))

import System.FilePath (takeFileName, takeBaseName)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T
import Text.PrettyPrint.Leijen.Text (Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP

import Abstract -- everything
import qualified Doc
import FileIO (Feature (..), writeFeatures)
import HOI4.Messages -- everything
import QQ (pdx)
import SettingsTypes ( PPT, Settings (..), Game (..)
                     , IsGame (..), IsGameData (..), IsGameState (..)
                     , getGameL10n, getGameL10nIfPresent
                     , setCurrentFile, withCurrentFile
                     , hoistErrors, hoistExceptions)
import HOI4.Common -- everything
import EU4.Common (Idea(idea_name_loc))

newHOI4CountryHistory :: Text -> HOI4CountryHistory
newHOI4CountryHistory chtag = HOI4CountryHistory chtag undefined

parseHOI4CountryHistory :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text HOI4CountryHistory)
parseHOI4CountryHistory scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr -> setCurrentFile sourceFile $ mapM processPolitics $ concatMap mapHisto scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing country history: " ++ T.unpack err
            return HM.empty
        Right countryHistoryFilesOrErrors ->
            flip HM.traverseWithKey countryHistoryFilesOrErrors $ \sourceFile echist ->
                fmap (mkCHMap . catMaybes) . forM echist $ \case
                    Left err -> do
                        traceM $ "Error parsing country history in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right cchist -> return cchist
    where
        mkCHMap :: [HOI4CountryHistory] -> HashMap Text HOI4CountryHistory
        mkCHMap = HM.fromList . map (chTag &&& id)

        mapHisto scr = case scr of
            stmt@[pdx| set_politics = @pol |] -> [stmt]
            _ -> []

processPolitics :: (IsGameState (GameState g), IsGameData (GameData g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe HOI4CountryHistory))
processPolitics (StatementBare _) = throwError "bare statement at top level"
processPolitics [pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] -> withCurrentFile $ \file -> do
            let chtag = T.pack $ take 3 $ takeFileName file
            cchist <- hoistErrors $ foldM processPoliticsAddSection
                                        (Just (newHOI4CountryHistory chtag))
                                        parts
            case cchist of
                Left err -> return (Left err)
                Right Nothing -> return (Right Nothing)
                Right (Just chist) -> withCurrentFile $ \file ->
                    return (Right (Just chist ))
        _ -> throwError "unrecognized form for set_politics"
    _ -> throwError "unrecognized form for set_politics@content"
processPolitics _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for set_politics in " <> T.pack file)

processPoliticsAddSection :: (IsGameState (GameState g), MonadError Text m) =>
    Maybe HOI4CountryHistory -> GenericStatement -> PPT g m (Maybe HOI4CountryHistory)
processPoliticsAddSection Nothing _ = return Nothing
processPoliticsAddSection cohi stmt
    = sequence (processPoliticsAddSection' <$> cohi <*> pure stmt)
    where
        processPoliticsAddSection' cohi stmt@[pdx| ruling_party = $id |] =
            let tag = chTag cohi in
            return cohi { chRulingTag = T.pack (concat[T.unpack tag , "_" , T.unpack id])}
        processPoliticsAddSection' cohi stmt@[pdx| last_election = %_ |]
            = return cohi
        processPoliticsAddSection' cohi stmt@[pdx| election_frequency = %_ |]
            = return cohi
        processPoliticsAddSection' cohi stmt@[pdx| elections_allowed = %_ |]
            = return cohi
        processPoliticsAddSection' cohi [pdx| $other = %_ |]
            = trace ("unknown set_politics in history: " ++ T.unpack other) $ return cohi
        processPoliticsAddSection' cohi _
            = trace "unrecognised form for set_politics in history" $ return cohi


parseHOI4Interface :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text Text)
parseHOI4Interface scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr -> setCurrentFile sourceFile $ mapM processInterface $ concatMap (\case
                [pdx| $spriteTypes = @spr |] | T.toLower spriteTypes == "spritetypes" -> spr
                _ -> []) scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing interface: " ++ T.unpack err
            return HM.empty
        Right interfaceFilesOrErrors ->
            flip HM.traverseWithKey interfaceFilesOrErrors $ \sourceFile einterface ->
                fmap (mkInterMap . catMaybes) . forM einterface $ \case
                    Left err -> do
                        traceM $ "Error parsing interface in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right iinterface -> return iinterface
    where
        mkInterMap :: [(Text,Text)] -> HashMap Text Text
        mkInterMap interfacelist = HM.fromList interfacelist

processInterface :: (IsGameState (GameState g), MonadError Text m) => GenericStatement -> PPT g m (Either Text  (Maybe (Text, Text)))
processInterface stmt@[pdx| $spriteType = @spr |] | T.toLower spriteType == "spritetype"
    =  case (getId spr, getPic spr) of
        (Just id, Just pic) -> withCurrentFile $ \file -> return $ Right $ Just (id, pic)
        (Nothing, Just pic) -> return (Right Nothing)
        (Just id, Nothing) -> return (Right Nothing)
        _ -> return (Right Nothing)
    where
        getId :: [GenericStatement] -> Maybe Text
        getId [] = Nothing
        getId (stmt@[pdx| $name = $id |] : _)
            | T.toLower name == "name" = Just id
        getId (stmt@[pdx| $name = ?id |] : _)
            | T.toLower name == "name" = Just id
        getId (_ : ss) = getId ss
        getPic :: [GenericStatement] -> Maybe Text
        getPic [] = Nothing
        getPic (stmt@[pdx| $texturefile = $id |] : _)
            | T.toLower texturefile == "texturefile" = Just $ T.pack $ takeBaseName $ T.unpack id
        getPic (stmt@[pdx| $texturefile = ?id |] : _)
            | T.toLower texturefile == "texturefile" = Just $ T.pack $ takeBaseName $ T.unpack id
        getPic (_ : ss) = getPic ss
processInterface stmt = return (Right Nothing)

----------------
-- Characters --
----------------

newHOI4Character :: Text -> Text -> FilePath -> HOI4Character
newHOI4Character chatag locname = HOI4Character chatag locname Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing

parseHOI4Characters :: (HOI4Info g, IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text HOI4Character, HashMap Text HOI4Character)
parseHOI4Characters scripts = do
    charmap <- HM.unions . HM.elems <$> do
        tryParse <- hoistExceptions $
            HM.traverseWithKey
                (\sourceFile scr -> setCurrentFile sourceFile $ mapM character $ concatMap (\case
                    [pdx| characters = @chars |] -> chars
                    _ -> scr) scr)
                scripts
        case tryParse of
            Left err -> do
                traceM $ "Completely failed parsing characters: " ++ T.unpack err
                return HM.empty
            Right characterFilesOrErrors ->
                flip HM.traverseWithKey characterFilesOrErrors $ \sourceFile ecchar ->
                    fmap (mkChaMap . catMaybes) . forM ecchar $ \case
                        Left err -> do
                            traceM $ "Error parsing characters in " ++ sourceFile
                                     ++ ": " ++ T.unpack err
                            return Nothing
                        Right cchar -> return cchar
    chartokmap <- parseCharToken charmap
    return (charmap, chartokmap)
    where
        mkChaMap :: [HOI4Character] -> HashMap Text HOI4Character
        mkChaMap = HM.fromList . map (chaTag &&& id)
        parseCharToken :: (HOI4Info g, IsGameData (GameData g), Monad m) =>
            HashMap Text HOI4Character ->  PPT g m (HashMap Text HOI4Character)
        parseCharToken chas = do
            let chaselem = HM.elems chas
                chastoken = mapMaybe (\c -> case cha_idea_token c of
                    Just txt -> Just (txt, c)
                    _ -> Nothing)
                    chaselem
            return $ HM.fromList chastoken

character :: (HOI4Info g, IsGameData (GameData g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe HOI4Character))
character (StatementBare _) = throwError "bare statement at top level"
character [pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] -> withCurrentFile $ \file -> do
            locname <- getGameL10n id
            cchar <- hoistErrors $ foldM characterAddSection
                                        (Just (newHOI4Character id locname file))
                                        parts
            case cchar of
                Left err -> return (Left err)
                Right Nothing -> return (Right Nothing)
                Right (Just char) -> withCurrentFile $ \file ->
                    return (Right (Just char))
        _ -> throwError "unrecognized form for characters"
    _ -> throwError "unrecognized form for characters@content"
character _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for characters in " <> T.pack file)

characterAddSection :: (HOI4Info g, MonadError Text m) =>
    Maybe HOI4Character -> GenericStatement -> PPT g m (Maybe HOI4Character)
characterAddSection Nothing _ = return Nothing
characterAddSection hChar stmt
    = sequence (characterAddSection' <$> hChar <*> pure stmt)
    where
        characterAddSection' hChar stmt@[pdx| name = %name |] = case name of
            StringRhs name -> do
                nameLoc <- getGameL10n name
                return hChar {chaName = nameLoc}
            GenericRhs name [] -> do
                nameLoc <- getGameL10n name
                return hChar {chaName = nameLoc}
            _ -> trace "Bad name in characters" $ return hChar
        characterAddSection' hChar stmt@[pdx| advisor = @adv |] = do
            ai <- getAdvinfo adv
            return hChar {chaAdvisorTraits = ai_traits ai, chaOn_add = ai_on_add ai,
                         chaOn_remove = ai_on_remove ai, cha_idea_token = ai_idea_token ai,
                         cha_advisor_slot = ai_slot ai, cha_adv_modifier = ai_modifier ai,
                         cha_adv_research_bonus = ai_research_bonus ai}
        characterAddSection' hChar stmt@[pdx| country_leader = @clead |] =
            let cleadtraits = concatMap getTraits clead
                ideo = getLeaderIdeo clead in
            return hChar {chaLeaderTraits = Just cleadtraits, cha_leader_ideology = ideo}
        characterAddSection' hChar [pdx| portraits = %_ |] =
            return hChar
        characterAddSection' hChar [pdx| corps_commander = %_ |] =
            return hChar
        characterAddSection' hChar [pdx| field_marshal = %_ |] =
            return hChar
        characterAddSection' hChar [pdx| navy_leader = %_ |] =
            return hChar
        characterAddSection' hChar [pdx| gender = %_ |] =
            return hChar
        characterAddSection' hChar [pdx| instance = %_ |] =
            return hChar
        characterAddSection' hChar [pdx| allowed_civil_war = %_ |] =
            return hChar
        characterAddSection' hChar [pdx| $other = %_ |]
            = trace ("unknown section in character: " ++ T.unpack other) $ return hChar
        characterAddSection' hChar _
            = trace "unrecognised form for in character" $ return hChar

        getTraits stmt@[pdx| traits = @traits |] = map
            (\case
                StatementBare (GenericLhs trait []) -> trait
                _ -> trace ("different trait list in" ++ show stmt) "")
            traits
        getTraits stmt = []
        getLeaderIdeo stmt = do
            let (ideo, _) = extractStmt (matchLhsText "ideology") stmt
            case ideo of
                Just [pdx| %_ = $ideot |] -> Just ideot
                _ -> Nothing
traitFromArray :: GenericStatement -> Maybe Text
traitFromArray (StatementBare (GenericLhs e [])) = Just e
traitFromArray stmt = trace ("Unknown in character trait array: " ++ show stmt) Nothing

data AdvisorInfo = AdvisorInfo
        {   ai_slot         :: Maybe Text
        ,   ai_idea_token   :: Maybe Text
        ,   ai_on_add       :: Maybe GenericScript
        ,   ai_on_remove    :: Maybe GenericScript
        ,   ai_traits       :: Maybe [Text]
        ,   ai_modifier     :: Maybe GenericStatement
        ,   ai_research_bonus :: Maybe GenericStatement
        }

newAI :: AdvisorInfo
newAI = AdvisorInfo Nothing Nothing Nothing Nothing Nothing Nothing Nothing
getAdvinfo :: forall g m. (HOI4Info g, Monad m) =>
    [GenericStatement] -> PPT g m AdvisorInfo
getAdvinfo = foldM addLine newAI
    where
        addLine :: AdvisorInfo -> GenericStatement -> PPT g m AdvisorInfo
        addLine ai [pdx| slot = $txt |] = return ai { ai_slot = Just txt }
        addLine ai [pdx| idea_token = $txt |] = return ai { ai_idea_token = Just txt}
        addLine ai [pdx| on_add = %rhs |] = case rhs of
                CompoundRhs [] -> return ai
                CompoundRhs scr -> return ai { ai_on_add = Just scr }
                _-> return ai
        addLine ai [pdx| on_remove = %rhs |] = case rhs of
                CompoundRhs [] -> return ai
                CompoundRhs scr -> return ai { ai_on_remove = Just scr }
                _-> return ai
        addLine ai [pdx| traits = @rhs |] = do
            let traits = Just (mapMaybe traitFromArray rhs)
            return ai {ai_traits = traits}
        addLine ai stmt@[pdx| modifier = %rhs |] = case rhs of
                CompoundRhs [] -> return ai
                CompoundRhs scr -> return ai { ai_modifier = Just stmt }
                _-> return ai
        addLine ai stmt@[pdx| research_bonus = %rhs |] = case rhs of
                CompoundRhs [] -> return ai
                CompoundRhs scr -> return ai { ai_research_bonus = Just stmt }
                _-> return ai
        addLine ai stmt@[pdx| allowed = %_|] = return ai
        addLine ai stmt@[pdx| available = %_|] = return ai
        addLine ai stmt@[pdx| visible = %_|] = return ai
        addLine ai stmt@[pdx| ledger = %_|] = return ai
        addLine ai stmt@[pdx| cost = %_|] = return ai
        addLine ai stmt@[pdx| ai_will_do = %_|] = return ai
        addLine ai stmt@[pdx| removal_cost = %_|] = return ai
        addLine ai stmt@[pdx| do_effect = %_|] = return ai
        addLine ai stmt@[pdx| desc = %_|] = return ai
        addLine ai stmt@[pdx| picture = %_|] = return ai
        addLine ai stmt@[pdx| name = %_|] = return ai
        addLine ai [pdx| $other = %_ |] = trace ("unknown section in advisor info: " ++ show other) $ return ai
        addLine ai stmt = trace ("unknown form in advisor info: " ++ show stmt) $ return ai

parseHOI4CountryLeaderTraits :: (IsGameData (GameData g), IsGameState (GameState g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text HOI4CountryLeaderTrait)
parseHOI4CountryLeaderTraits scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr ->
                setCurrentFile sourceFile $ mapM parseHOI4CountryLeaderTrait $ concatMap (\case
                [pdx| leader_traits = @traits |] -> traits
                _ -> [])
                scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing countryleadertraits: " ++ T.unpack err
            return HM.empty
        Right countryleadertraitsFilesOrErrors ->
            flip HM.traverseWithKey countryleadertraitsFilesOrErrors $ \sourceFile eclts ->
                fmap (mkCltMap . catMaybes) . forM eclts $ \case
                    Left err -> do
                        traceM $ "Error parsing countryleadertraits in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right cclt -> return cclt
                where mkCltMap :: [HOI4CountryLeaderTrait] -> HashMap Text HOI4CountryLeaderTrait
                      mkCltMap = HM.fromList . map (clt_id &&& id)

parseHOI4CountryLeaderTrait :: (IsGameData (GameData g), IsGameState (GameState g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe HOI4CountryLeaderTrait))
parseHOI4CountryLeaderTrait [pdx| $id = @effects |]
    = withCurrentFile $ \file -> do
        mlocid <- getGameL10nIfPresent id
        let cclt = foldl' addSection (HOI4CountryLeaderTrait {
                clt_id = id
            ,   clt_loc_name = mlocid
            ,   clt_path = file
            ,   clt_targeted_modifier = Nothing
            ,   clt_equipment_bonus = Nothing
            ,   clt_hidden_modifier = Nothing
            ,   clt_modifier = Nothing
            }) effects
        return $ Right (Just cclt)
    where
        addSection :: HOI4CountryLeaderTrait -> GenericStatement -> HOI4CountryLeaderTrait
        addSection clt stmt@[pdx| $lhs = @scr |] = case lhs of
            "targeted_modifier" -> let oldstmt = fromMaybe [] (clt_targeted_modifier clt) in
                    clt { clt_targeted_modifier = Just (oldstmt ++ [stmt]) }
            "equipment_bonus" -> clt { clt_equipment_bonus = Just stmt }
            "hidden_modifier" -> clt { clt_hidden_modifier = Just stmt }
            "ai_strategy" -> clt
            "ai_will_do" -> clt
            "random" -> clt
            _ -> trace ("Urecognized statement in country_leader: " ++ show stmt) clt
         -- Must be an effect
        addSection clt stmt@[pdx| random = %_ |] = clt
        addSection clt stmt =
            let oldmod = fromMaybe [] (clt_modifier clt) in
            clt { clt_modifier = Just (oldmod ++ [stmt]) }
parseHOI4CountryLeaderTrait stmt = trace (show stmt) $ withCurrentFile $ \file ->
    throwError ("unrecognised form for country_leader in " <> T.pack file)

parseHOI4UnitLeaderTraits :: (IsGameData (GameData g), IsGameState (GameState g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text HOI4UnitLeaderTrait)
parseHOI4UnitLeaderTraits scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr ->
                setCurrentFile sourceFile $ mapM parseHOI4UnitLeaderTrait $ concatMap (\case
                [pdx| leader_traits = @traits |] -> traits
                _ -> [])
                scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing unitleadertraits: " ++ T.unpack err
            return HM.empty
        Right unitleadertraitsFilesOrErrors ->
            flip HM.traverseWithKey unitleadertraitsFilesOrErrors $ \sourceFile eults ->
                fmap (mkUltMap . catMaybes) . forM eults $ \case
                    Left err -> do
                        traceM $ "Error parsing unitleadertraits in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right cult -> return cult
                where mkUltMap :: [HOI4UnitLeaderTrait] -> HashMap Text HOI4UnitLeaderTrait
                      mkUltMap = HM.fromList . map (ult_id &&& id)

parseHOI4UnitLeaderTrait :: (IsGameData (GameData g), IsGameState (GameState g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe HOI4UnitLeaderTrait))
parseHOI4UnitLeaderTrait [pdx| $id = @effects |]
    = withCurrentFile $ \file -> do
        mlocid <- getGameL10nIfPresent id
        let cult = foldl' addSection (HOI4UnitLeaderTrait {
                ult_id = id
            ,   ult_loc_name = mlocid
            ,   ult_path = file
            ,   ult_modifier = Nothing
            ,   ult_non_shared_modifier = Nothing
            ,   ult_corps_commander_modifier = Nothing
            ,   ult_field_marshal_modifier = Nothing
            ,   ult_sub_unit_modifiers = Nothing
            ,   ult_attack_skill = Nothing
            ,   ult_defense_skill = Nothing
            ,   ult_planning_skill = Nothing
            ,   ult_logistics_skill = Nothing
            ,   ult_maneuvering_skill = Nothing
            ,   ult_coordination_skill = Nothing
            }) effects
        return $ Right (Just cult)
    where
        addSection :: HOI4UnitLeaderTrait -> GenericStatement -> HOI4UnitLeaderTrait
        addSection ult stmt@[pdx| $lhs = @scr |] = case lhs of
            "modifier" -> ult { ult_modifier = Just stmt }
            "non_shared_modifier" -> ult { ult_non_shared_modifier = Just stmt }
            "corps_commander_modifier" -> ult { ult_corps_commander_modifier = Just stmt }
            "field_marshal_modifier" -> ult { ult_field_marshal_modifier = Just stmt }
            "sub_unit_modifiers" -> ult { ult_sub_unit_modifiers = Just stmt }
            "new_commander_weight" -> ult
            "on_add" -> ult
            "on_remove " -> ult
            "daily_effect" -> ult
            "num_parents_needed" -> ult
            "prerequisites" -> ult
            "gain_xp" -> ult
            "gain_xp_leader" -> ult
            "gain_xp_on_spotting" -> ult
            "trait_xp_factor" -> ult
            "show_in_combat" -> ult
            "allowed" -> ult
            "ai_will_do" -> ult
            "type" -> ult
            _ -> trace ("Urecognized statement in unit_leader lhs -> scr: " ++ show stmt) ult
         -- Must be an effect
        addSection ult stmt@[pdx| $lhs = !num |] = case lhs of
            "attack_skill" -> ult { ult_attack_skill = Just num}
            "defense_skill" -> ult { ult_defense_skill = Just num}
            "planning_skill" -> ult { ult_planning_skill = Just num}
            "logistics_skill" -> ult { ult_logistics_skill = Just num}
            "maneuvering_skill" -> ult { ult_maneuvering_skill = Just num}
            "coordination_skill" -> ult { ult_coordination_skill = Just num}
            "attack_skill_factor" -> ult
            "defense_skill_factor" -> ult
            "planning_skill_factor" -> ult
            "logistics_skill_factor" -> ult
            "maneuvering_skill_factor" -> ult
            "coordination_skill_factor" -> ult
            "gui_row" -> ult
            "gui_column" -> ult
            "cost" -> ult
            "num_parents_needed" -> ult
            "gain_xp_on_spotting" -> ult
            _ -> trace ("Urecognized statement in unit_leader lhs -> Double: " ++ show stmt) ult
        addSection ult stmt@[pdx| $lhs = !num |] = let numd = num ::Int in trace ("Urecognized statement in unit_leader lhs -> Int: " ++ show stmt) ult
        addSection ult stmt@[pdx| $lhs = $_ |] = case lhs of
            "type" -> ult
            "trait_type" -> ult
            "slot" -> ult
            "specialist_advisor_trait" -> ult
            "expert_advisor_trait" -> ult
            "genius_advisor_trait" -> ult
            "custom_gain_xp_trigger_tooltip" -> ult
            "custom_prerequisite_tooltip" -> ult
            "parent" -> ult
            "mutually_exclusive" -> ult
            "enable_ability" -> ult
            "custom_effect_tooltip" -> ult
            "override_effect_tooltip" -> ult
            _ -> trace ("Urecognized statement in unit_leader lhs -> txt: " ++ show stmt) ult
        addSection ult stmt = trace ("Urecognized statement form in unit_leader: " ++ show stmt) ult
parseHOI4UnitLeaderTrait stmt = trace (show stmt) $ withCurrentFile $ \file ->
    throwError ("unrecognised form for unit_leader in " <> T.pack file)

-------------
-- terrain --
-------------

parseHOI4Terrain :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m [Text]
parseHOI4Terrain scripts = do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr -> setCurrentFile sourceFile $ mapM processTerrain $ concatMap getcat scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing terrain: " ++ T.unpack err
            return []
        Right terrainFilesOrErrors ->
            return $ catMaybes $ concat $ concat $ HM.elems (HM.mapWithKey (\sourceFile eterrain -> -- probably better ways to this
                map (\case
                    Left err -> do
                        traceM $ "Error parsing terrain in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right tterrain -> return tterrain) eterrain) terrainFilesOrErrors)
    where
        getcat = \case
            [pdx| categories = @cat |] -> cat
            _ -> []

processTerrain :: (IsGameState (GameState g), IsGameData (GameData g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe Text))
processTerrain (StatementBare _) = throwError "bare statement at top level"
processTerrain [pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] -> withCurrentFile $ \file -> return (Right (Just id))
        _ -> throwError "unrecognized form for terrain"
    _ -> throwError "unrecognized form for terrain@content"
processTerrain _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for terrain in " <> T.pack file)

----------------
-- ideologies --
----------------

parseHOI4Ideology :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text Text)
parseHOI4Ideology scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr -> setCurrentFile sourceFile $ mapM processIdeology $ concatMap getideo scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing ideology: " ++ T.unpack err
            return HM.empty
        Right ideologyFilesOrErrors ->
            flip HM.traverseWithKey ideologyFilesOrErrors $ \sourceFile eideology ->
                fmap (mkIdeoMap . catMaybes) . forM eideology $ \case
                    Left err -> do
                        traceM $ "Error parsing ideology in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right iideology -> return iideology
    where
        mkIdeoMap :: [(Text,[Text])] -> HashMap Text Text
        mkIdeoMap subideolist = HM.fromList $ concatMap switchideos subideolist
        switchideos :: (Text,[Text]) -> [(Text, Text)]
        switchideos (ideo, subideo) = map (switcheroo ideo) subideo
        switcheroo :: Text -> Text -> (Text, Text)
        switcheroo ideo subideo = (subideo, ideo)

        getideo = \case
            [pdx| ideologies = @cat |] -> cat
            _ -> []

processIdeology :: (IsGameState (GameState g), IsGameData (GameData g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe (Text,[Text])))
processIdeology (StatementBare _) = throwError "bare statement at top level"
processIdeology [pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] -> withCurrentFile $ \file -> do
            let subideos = concat $ mapMaybe (\case
                    [pdx| types = @scr |] -> Just $ mapMaybe getsubs scr
                    _-> Nothing) parts
            return (Right (Just (id , subideos)))
        _ -> throwError "unrecognized form for ideology"
    _ -> throwError "unrecognized form for ideology@content"
    where
        getsubs [pdx| $subideo = @_|] = Just subideo
        getsubs stmt = Nothing
processIdeology _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for ideology in " <> T.pack file)


-----------------
-- scripted_<> --
-----------------

parseHOI4Effects :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text GenericStatement)
parseHOI4Effects scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr -> setCurrentFile sourceFile $ mapM parseHOI4Effect $ concatMap onlyscripts scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing scripted effects: " ++ T.unpack err
            return HM.empty
        Right effectFilesOrErrors ->
            flip HM.traverseWithKey effectFilesOrErrors $ \sourceFile eeffect ->
                fmap (mkEffectMap . catMaybes) . forM eeffect $ \case
                    Left err -> do
                        traceM $ "Error parsing scripted effects in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right feffect -> return feffect
    where
        mkEffectMap :: [(Text,GenericStatement)] -> HashMap Text GenericStatement
        mkEffectMap = HM.fromList
        onlyscripts = \case
            stmt@[pdx| %_ = @_|] -> [stmt]
            _ -> []

parseHOI4Effect :: (IsGameState (GameState g), IsGameData (GameData g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe (Text, GenericStatement)))
parseHOI4Effect (StatementBare _) = throwError "bare statement at top level"
parseHOI4Effect stmt@[pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] -> withCurrentFile $ \file ->
            return (Right (Just (id , stmt)))
        _ -> throwError "unrecognized form for scripted effect"
    _ -> throwError "unrecognized form for scripted effect@content"
parseHOI4Effect _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for scripted effect in " <> T.pack file)

parseHOI4Triggers :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text GenericStatement)
parseHOI4Triggers scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr -> setCurrentFile sourceFile $ mapM parseHOI4Trigger $ concatMap onlyscripts scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing scripted triggers: " ++ T.unpack err
            return HM.empty
        Right triggerFilesOrErrors ->
            flip HM.traverseWithKey triggerFilesOrErrors $ \sourceFile etrigger ->
                fmap (mkTriggerMap . catMaybes) . forM etrigger $ \case
                    Left err -> do
                        traceM $ "Error parsing scripted triggers in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right ttrigger -> return ttrigger
    where
        mkTriggerMap :: [(Text,GenericStatement)] -> HashMap Text GenericStatement
        mkTriggerMap = HM.fromList
        onlyscripts = \case
            stmt@[pdx| %_ = @_|] -> [stmt]
            _ -> []

parseHOI4Trigger :: (IsGameState (GameState g), IsGameData (GameData g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe (Text, GenericStatement)))
parseHOI4Trigger (StatementBare _) = throwError "bare statement at top level"
parseHOI4Trigger stmt@[pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] -> withCurrentFile $ \file ->
            return (Right (Just (id , stmt)))
        _ -> throwError "unrecognized form for scripted trigger"
    _ -> throwError "unrecognized form for scripted trigger@content"
parseHOI4Trigger _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for scripted trigger in " <> T.pack file)
