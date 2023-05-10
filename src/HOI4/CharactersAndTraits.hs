{-
Module      : HOI4.CharactersAndTraits
Description : Feature handler for characetr and trait features in Hearts of Iron IV
-}
module HOI4.CharactersAndTraits (
         parseHOI4Characters
        ,parseHOI4CountryLeaderTraits
        ,parseHOI4UnitLeaderTraits
    ) where

import Debug.Trace (trace, traceM)

import Control.Arrow ((&&&))
import Control.Monad (foldM, forM)
import Control.Monad.Except (MonadError (..))

import Data.List ( foldl' )
import Data.Maybe (catMaybes, fromMaybe, mapMaybe)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T

import Abstract -- everything
 -- everything
import QQ (pdx)
import SettingsTypes ( PPT
                     , IsGame (..), IsGameData (..), IsGameState (..)
                     , getGameL10n, getGameL10nIfPresent
                     , setCurrentFile, withCurrentFile
                     , hoistErrors, hoistExceptions)
import HOI4.Common -- everything
----------------
-- Characters --
----------------

newHOI4Character :: Text -> Text -> FilePath -> HOI4Character
newHOI4Character chatag locname = HOI4Character chatag chatag locname Nothing Nothing Nothing Nothing

parseHOI4Characters :: (HOI4Info g, IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text HOI4Character, HashMap Text HOI4Advisor)
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
        mkChaMap = HM.fromList . map (cha_id &&& id)
        parseCharToken :: (HOI4Info g, IsGameData (GameData g), Monad m) =>
            HashMap Text HOI4Character ->  PPT g m (HashMap Text HOI4Advisor)
        parseCharToken chas = do
            let chaselem = HM.elems chas
                chastoken = mapMaybe (\c -> case cha_advisor c of
                    Just adv ->
                        let a = a { adv_cha_name = cha_name c,adv_cha_id = cha_id c, adv_cha_portrait = cha_portrait c} in
                        Just $ map (\a -> (adv_idea_token a, a)) adv
                    _ -> Nothing)
                    chaselem
            return $ HM.fromList $ concat chastoken

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
                Right (Just char) -> withCurrentFile $ \_ ->
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
        characterAddSection' hChar [pdx| name = %name |] = case name of
            StringRhs name -> do
                nameLoc <- getGameL10n name
                return hChar {cha_loc_name = nameLoc, cha_name = name}
            GenericRhs name [] -> do
                nameLoc <- getGameL10n name
                return hChar {cha_loc_name  = nameLoc, cha_name = name}
            _ -> trace "Bad name in characters" $ return hChar
        characterAddSection' hChar [pdx| advisor = @adv |] = do
            let oldadv = fromMaybe [] (cha_advisor hChar )
            advif <- getAdvinfo hChar adv
            return hChar { cha_advisor = Just  (oldadv ++ [advif])}
        characterAddSection' hChar [pdx| country_leader = @clead |] =
            let cleadtraits = concatMap getTraits clead
                ideo = getLeaderIdeo clead in
            return hChar {cha_leader_traits = Just cleadtraits, cha_leader_ideology = ideo}
        characterAddSection' hChar [pdx| portraits = @scr |] =
            let port = getSmallPortrait scr in
            return hChar { cha_portrait = port }
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
        getTraits _ = []
        getLeaderIdeo stmt = do
            let (ideo, _) = extractStmt (matchLhsText "ideology") stmt
            case ideo of
                Just [pdx| %_ = $ideot |] -> Just ideot
                _ -> Nothing

--getSmallPortrait :: GenericStatement -> HOI4Character -> HOI4Character
getSmallPortrait scr = getPortrait scr
    where
        getPortrait [] = Nothing
        getPortrait ([pdx| $_ = @scr |]:can) = getPortrait' scr can
        getPortrait (x:can) = getPortrait can
        getPortrait' x can = getSmall x can
        getSmall [] can = getPortrait can
        getSmall (x:xs) can = getSmall' x xs can
        getSmall' [pdx| small = $port |] _ _ = Just port
        getSmall' [pdx| small = ?port |] _ _ = Just port
        getSmall' _ x can = getSmall x can


traitFromArray :: GenericStatement -> Maybe Text
traitFromArray (StatementBare (GenericLhs e [])) = Just e
traitFromArray stmt = trace ("Unknown in character trait array: " ++ show stmt) Nothing


newAI :: HOI4Advisor
newAI = HOI4Advisor "" "" "" "" Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing True ""
getAdvinfo :: forall g m. (HOI4Info g, Monad m) => HOI4Character ->
    [GenericStatement] -> PPT g m HOI4Advisor
getAdvinfo cha = foldM addLine newAI
    where
        addLine :: HOI4Advisor -> GenericStatement -> PPT g m HOI4Advisor
        addLine ai [pdx| slot = $txt |] = return ai { adv_advisor_slot = txt }
        addLine ai [pdx| idea_token = $txt |] = return ai { adv_idea_token = txt}
        addLine ai [pdx| on_add = %rhs |] = case rhs of
                CompoundRhs [] -> return ai
                CompoundRhs scr -> return ai { adv_on_add = Just scr }
                _-> return ai
        addLine ai [pdx| on_remove = %rhs |] = case rhs of
                CompoundRhs [] -> return ai
                CompoundRhs scr -> return ai { adv_on_remove = Just scr }
                _-> return ai
        addLine ai [pdx| traits = @rhs |] = do
            let traits = Just (mapMaybe traitFromArray rhs)
            return ai {adv_traits = traits}
        addLine ai stmt@[pdx| modifier = %rhs |] = case rhs of
                CompoundRhs [] -> return ai
                CompoundRhs _ -> return ai { adv_modifier = Just stmt }
                _-> return ai
        addLine ai stmt@[pdx| research_bonus = %rhs |] = case rhs of
                CompoundRhs [] -> return ai
                CompoundRhs _ -> return ai { adv_research_bonus = Just stmt }
                _-> return ai
        addLine ai [pdx| allowed = %rhs |] = case rhs of
                CompoundRhs [] -> return ai
                CompoundRhs scr -> return ai { adv_allowed = Just scr }
                _-> return ai
        addLine ai [pdx| available = %rhs|] = case rhs of
                CompoundRhs [] -> return ai
                CompoundRhs scr -> return ai { adv_available = Just scr }
                _-> return ai
        addLine ai [pdx| visible = %rhs|] = case rhs of
                CompoundRhs [] -> return ai
                CompoundRhs scr -> return ai { adv_visible = Just scr }
                _-> return ai
        addLine ai [pdx| ledger = %_|] = return ai
        addLine ai [pdx| cost = %rhs|] = case rhs of
                (floatRhs -> Just num) -> return ai { adv_cost = Just num }
                _-> return $ trace "bad advisor cost" ai
        addLine ai [pdx| ai_will_do = %_|] = return ai
        addLine ai [pdx| removal_cost = %_|] = return ai
        addLine ai [pdx| do_effect = %_|] = return ai
        addLine ai [pdx| desc = %_|] = return ai
        addLine ai [pdx| picture = %_|] = return ai
        addLine ai [pdx| name = %_|] = return ai
        addLine ai [pdx| can_be_fired = %rhs|]
            | GenericRhs "no" [] <- rhs = return ai { adv_can_be_fired = True }
            | GenericRhs "yes" [] <- rhs = return ai { adv_can_be_fired = False }
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
            ,   clt_name = id
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
        addSection clt stmt@[pdx| $lhs = @_ |] = case lhs of
            "targeted_modifier" -> let oldstmt = fromMaybe [] (clt_targeted_modifier clt) in
                    clt { clt_targeted_modifier = Just (oldstmt ++ [stmt]) }
            "equipment_bonus" -> clt { clt_equipment_bonus = Just stmt }
            "hidden_modifier" -> clt { clt_hidden_modifier = Just stmt }
            "ai_strategy" -> clt
            "ai_will_do" -> clt
            "random" -> clt
            _ -> trace ("Urecognized statement in country_leader: " ++ show stmt) clt
         -- Must be an effect
        addSection clt [pdx| random = %_ |] = clt
        addSection clt [pdx| command_cap = %_ |] = clt
        addSection clt [pdx| sprite = %_ |] = clt
        addSection clt [pdx| name = $txt |] = clt { clt_name = txt }
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
            ,   ult_trait_xp_factor = Nothing
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
        addSection ult stmt@[pdx| $lhs = @_ |] = case lhs of
            "modifier" -> ult { ult_modifier = Just stmt }
            "non_shared_modifier" -> ult { ult_non_shared_modifier = Just stmt }
            "corps_commander_modifier" -> ult { ult_corps_commander_modifier = Just stmt }
            "field_marshal_modifier" -> ult { ult_field_marshal_modifier = Just stmt }
            "sub_unit_modifiers" -> ult { ult_sub_unit_modifiers = Just stmt }
            "trait_xp_factor" -> ult { ult_trait_xp_factor = Just stmt }
            "new_commander_weight" -> ult
            "on_add" -> ult
            "on_remove " -> ult
            "daily_effect" -> ult
            "num_parents_needed" -> ult
            "prerequisites" -> ult
            "gain_xp" -> ult
            "gain_xp_leader" -> ult
            "gain_xp_on_spotting" -> ult
            "show_in_combat" -> ult
            "allowed" -> ult
            "ai_will_do" -> ult
            "type" -> ult
            "unit_trigger" -> ult -- what triggers are needed for it to gain xp?
            "unit_type" -> ult -- what unit types it applies to?
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
        addSection ult stmt@[pdx| $_ = !num |] = let _ = num ::Int in trace ("Urecognized statement in unit_leader lhs -> Int: " ++ show stmt) ult
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