{-
Module      : HOI4.CharactersAndTraits
Description : Feature handler for characetr and trait features in Hearts of Iron IV
-}
module HOI4.CharactersAndTraits (
         parseHOI4Characters, writeHOI4Characters
        ,parseHOI4CountryLeaderTraits, writeHOI4CountryLeaderTraits
        ,parseHOI4UnitLeaderTraits, writeHOI4UnitLeaderTraits
    ) where

import Debug.Trace (trace, traceM)

import Control.Arrow ((&&&))
import Control.Monad (foldM, forM)
import Control.Monad.Except (ExceptT (..), MonadError (..))
import Control.Monad.State (MonadState (..), gets)
import Control.Monad.Trans (MonadIO (..))

import Data.List ( foldl', sortOn )
import Data.Maybe (catMaybes, fromMaybe, mapMaybe, isJust)

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
import MessageTools
import HOI4.SpecialHandlers (modifierMSG', modifiersTable, getLeaderTraits, getbaretraits)
import QQ (pdx)
import SettingsTypes ( PPT, Settings (..)
                     , IsGame (..), IsGameData (..), IsGameState (..)
                     , withCurrentIndent, getGameInterface
                     , getGameL10n, getGameL10nIfPresent
                     , setCurrentFile, withCurrentFile
                     , hoistErrors, hoistExceptions, getGameInterfaceIfPresent, concatMapM, indentUp)
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
            | GenericRhs "no" [] <- rhs = return ai { adv_can_be_fired = False }
            | GenericRhs "yes" [] <- rhs = return ai { adv_can_be_fired = True }
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
            "any_parent" -> ult -- unknown what it does for now. AAT
            "parent" -> ult -- unknown what it does for now. AAT
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


writeHOI4CountryLeaderTraits :: (HOI4Info g, MonadIO m) => PPT g m ()
writeHOI4CountryLeaderTraits = do
    countryLeaderTraits <- getCountryLeaderTraits
    writeFeatures "country_leader_traits"
                  [Feature { featurePath = Just "traits"
                           , featureId = Just "country_leader_traits.txt"
                           , theFeature = Right (HM.elems countryLeaderTraits)
                           }]
                  ppCountryLeaderTraits

ppCountryLeaderTraits :: (HOI4Info g, Monad m) => [HOI4CountryLeaderTrait] -> PPT g m Doc
ppCountryLeaderTraits cTraits = do
    version <- gets (gameVersion . getSettings)
    ctraits_pp'd <- mapM ppCountryLeaderTrait (sortOn (T.toCaseFold . clt_id) cTraits)
    return . mconcat $ ["return {", PP.line]
        ++ ctraits_pp'd ++
        ["}"]

ppCountryLeaderTrait :: forall g m. (HOI4Info g, Monad m) => HOI4CountryLeaderTrait -> PPT g m Doc
ppCountryLeaderTrait cTrait = do
    locName <- getGameL10n (clt_id cTrait)
    let nfArg :: (HOI4CountryLeaderTrait -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
        nfArg field fmt
            = maybe (return [])
                (\field_content -> do
                    content_pp'd <- fmt field_content
                    return
                        [content_pp'd
                        ,PP.line])
            (field cTrait)
    mod_pp <- withCurrentIndent $ \_ -> do
        case clt_modifier cTrait of
            Just trait -> modifierMSG' trait
            Nothing -> return []
    mod_pp' <- imsg2doc mod_pp
    tarmod_pp <- nfArg clt_targeted_modifier ppScript
    equmod_pp <- nfArg clt_equipment_bonus ppStatement
    hidmod_pp <- nfArg clt_hidden_modifier ppStatement
    --trait_desc <- getGameL10nIfPresent $ clt_id cTrait <> "_desc"
    --let trait_desc' = case trait_desc of
    --        Just desc -> if not (T.null desc) then mconcat [", [\"desc\"] = [[" <> (Doc.strictText . Doc.nl2br) desc, "]]"] else mempty
    --        Nothing -> mempty
    return . mconcat $
        [ "[\"", Doc.strictText $ T.toLower (clt_id cTrait), "\"] = { [\"name\"] = \"",Doc.strictText locName, "\""
        --, trait_desc'
        , if not (null mod_pp) || not (all null [tarmod_pp, equmod_pp, hidmod_pp]) then
             ", [\"mods\"] = [===[" else "", mod_pp', if not (null mod_pp) && not (all null [tarmod_pp, equmod_pp, hidmod_pp]) then PP.line else ""
        ] ++
        tarmod_pp ++
        equmod_pp ++
        hidmod_pp ++
        [ if not (null mod_pp) || not (all null [tarmod_pp, equmod_pp, hidmod_pp]) then
            "]===]" else ""," },", PP.line] -- ++
        --if T.toLower locName /= T.toLower (clt_id cTrait) then ["[\"", Doc.strictText $ T.toLower locName, "\"] = \"", Doc.strictText $ T.toLower (clt_id cTrait), "\",", PP.line] else []



writeHOI4UnitLeaderTraits :: (HOI4Info g, MonadIO m) => PPT g m ()
writeHOI4UnitLeaderTraits = do
    unitLeaderTraits <- getUnitLeaderTraits
    writeFeatures "unit_leader_traits"
                  [Feature { featurePath = Just "traits"
                           , featureId = Just "unit_leader_traits.txt"
                           , theFeature = Right (HM.elems unitLeaderTraits)
                           }]
                  ppUnitLeaderTraits

ppUnitLeaderTraits :: (HOI4Info g, Monad m) => [HOI4UnitLeaderTrait] -> PPT g m Doc
ppUnitLeaderTraits uTraits = do
    version <- gets (gameVersion . getSettings)
    utraits_pp'd <- mapM ppUnitLeaderTrait (sortOn (T.toCaseFold . ult_id) uTraits)
    return . mconcat $ ["return {", PP.line]
        ++ utraits_pp'd ++
        ["}"]

ppUnitLeaderTrait :: forall g m. (HOI4Info g, Monad m) => HOI4UnitLeaderTrait -> PPT g m Doc
ppUnitLeaderTrait uTrait = do
    locName <- getGameL10n (ult_id uTrait)
    let nfArg :: (HOI4UnitLeaderTrait -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
        nfArg field fmt
            = maybe (return [])
                (\field_content -> do
                    content_pp'd <- fmt field_content
                    return
                        [content_pp'd
                        ,PP.line])
            (field uTrait)
        mods = case ult_modifier  uTrait of
            Just [pdx| %_ = @scr|] -> scr
            _ -> []
        nsmod = case ult_non_shared_modifier uTrait of
            Just [pdx| %_ = @scr|] -> scr
            _ -> []
        ccmod  = case ult_corps_commander_modifier uTrait of
            Just [pdx| %_ = @scr|] -> scr
            _ -> []
        fmmod = case ult_field_marshal_modifier uTrait of
            Just [pdx| %_ = @scr|] -> scr
            _ -> []
        allmod = mods ++ nsmod ++ ccmod ++ fmmod
    traiticon <- do
        gfx <- getGameInterfaceIfPresent ("GFX_trait_" <> ult_id uTrait)
        case gfx of
            Just icon -> return ""
            Nothing -> return ", [\"icon\"] = \"Trait unknown\""
    mod_pp <- if null allmod then return [] else do
        mod_pp' <- withCurrentIndent $ \_ -> modifierMSG' allmod
        a <- imsg2doc mod_pp'
        return [a,PP.line]
    sumod <- nfArg ult_sub_unit_modifiers ppStatement
    traitxp <- case ult_trait_xp_factor uTrait of
        Just [pdx| %_ = @trxp|] -> concatMapM (\case
            [pdx| $trait = !factor |] -> do
                traitloc <- getGameL10n trait
                let traitdoc = Doc.strictText traitloc
                return ["* ",traitdoc ," experience factor: ", reducedNum (colourPcSign True) factor, PP.line]
            _ -> return []) trxp
        _ -> return []
    trait_desc <- getGameL10nIfPresent $ ult_id uTrait <> "_desc"
    let trait_desc' = case trait_desc of
            Just desc -> if not (T.null desc) then mconcat [", [\"desc\"] = [===[" <> (Doc.strictText . Doc.nl2br) desc, "]===]"] else mempty
            Nothing -> mempty
        attack = case ult_attack_skill uTrait of
            Just att -> ["* Attack: ", colourNumSign True att, PP.line]
            Nothing -> []
        defense = case ult_defense_skill uTrait of
            Just def -> ["* Defense: ", colourNumSign True def, PP.line]
            Nothing -> []
        plan = case ult_planning_skill uTrait of
            Just plan -> ["* Planning: ", colourNumSign True plan, PP.line]
            Nothing -> []
        logi = case ult_logistics_skill uTrait of
            Just logi -> ["* Logistics: ", colourNumSign True logi, PP.line]
            Nothing -> []
        maneuv = case ult_maneuvering_skill uTrait of
            Just man -> ["* Maneuvering: ", colourNumSign True man, PP.line]
            Nothing -> []
        coord = case ult_coordination_skill uTrait of
            Just coo -> ["* Coordination: ", colourNumSign True coo, PP.line]
            Nothing -> []
    return . mconcat $
        [ "[\"", Doc.strictText $ T.toLower (ult_id uTrait), "\"] = { [\"name\"] = \"",Doc.strictText locName, "\""
        , trait_desc'
        , traiticon
        , if (not . all null) [mod_pp, sumod, attack, defense, plan, logi, maneuv, coord, traitxp] then
             ", [\"mods\"] = [===[" else ""
        ] ++
        traitxp ++
        mod_pp ++
        sumod ++
        attack ++
        defense ++
        plan ++
        logi ++
        maneuv ++
        coord ++
        [ if (not . all null) [mod_pp, sumod, attack, defense, plan, logi, maneuv, coord, traitxp] then
            "]===]" else ""," },", PP.line] -- ++
        --if T.toLower locName /= T.toLower (ult_id uTrait) then ["[\"", Doc.strictText $ T.toLower locName, "\"] = \"", Doc.strictText $ T.toLower (ult_id uTrait), "\",", PP.line] else []


writeHOI4Characters :: (HOI4Info g, MonadIO m) => PPT g m ()
writeHOI4Characters = do
    ideas <- getCharacterScripts
    pathIDS <- parseHOI4CharactersPath ideas
    let pathedIdea :: [Feature [HOI4Character]]
        pathedIdea = map (\ids -> Feature {
                                        featurePath = Just "characters"
                                    ,   featureId = Just (T.pack $ takeBaseName $ cha_path $ head ids) <> Just ".txt"
                                    ,   theFeature = Right ids })
                              (HM.elems pathIDS)
    writeFeatures "ideas"
                  pathedIdea
                  ppIdeas

parseHOI4CharactersPath :: (HOI4Info g, IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap FilePath [HOI4Character])
parseHOI4CharactersPath scripts = do
    tryParse <- hoistExceptions $
            HM.traverseWithKey
                (\sourceFile scr -> setCurrentFile sourceFile $ mapM character $ concatMap (\case
                    [pdx| characters = @chars |] -> chars
                    _ -> scr) scr)
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

ppIdeas :: forall g m. (HOI4Info g, Monad m) =>  [HOI4Character] -> PPT g m Doc
ppIdeas nfs = do
    version <- gets (gameVersion . getSettings)
    let filesource = cha_path $ head nfs
        advisors = concat $ mapMaybe (\x -> case cha_advisor x of
                Just adv -> Just $ map (,x) adv
                _-> Nothing ) nfs
    nfDoc <- traverse (scope HOI4Country . ppIdea filesource) advisors -- Better to leave unsorted? (sortOn (sortName . nf_name_loc) nfs)
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
    where
        traverseIf f = traverse (\x -> if pred x then f x else return mempty)
        pred x = isJust $ cha_advisor x

ppIdea :: forall g m. (HOI4Info g, Monad m) => FilePath -> (HOI4Advisor, HOI4Character) -> PPT g m Doc
ppIdea fp (id, cha) = setCurrentFile fp $ do
    let nfArg :: (HOI4Advisor -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
        nfArg field fmt
            = maybe (return [])
                (\field_content -> do
                    content_pp'd <- fmt field_content
                    return
                        [content_pp'd
                        ,PP.line])
            (field id)
    let nfArgExtra :: Doc -> (HOI4Advisor -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
        nfArgExtra extra field fmt
            = maybe (return [])
                (\field_content -> do
                    content_pp'd <- fmt field_content
                    return
                        ["<!-- ",extra, " -->"
                        ,content_pp'd
                        ,PP.line])
            (field id)
    let idArg :: Text -> (HOI4Advisor -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
        idArg fieldname field fmt
            = maybe (return [])
                (\field_content -> do
                    content_pp'd <- fmt field_content
                    return
                        ["* When ", Doc.strictText fieldname, ": "
                        ,PP.line
                        ,content_pp'd
                        ,PP.line])
                (field id)
    icon_pp <- do
        case cha_portrait cha of
            Just port -> do
                micon <- getGameInterfaceIfPresent port
                case micon of
                    Just icond -> return $ Just icond
                    _ -> return $ Just $ T.pack $ takeBaseName $ T.unpack port
            _-> return Nothing
    name_pp <- do
        mloc <- getGameL10nIfPresent $ cha_name cha
        case mloc of
            Just name -> return name
            Nothing -> getGameL10n $ adv_idea_token id
    desc_pp <- getGameL10nIfPresent $ adv_idea_token id <> "_desc"
    allowed_pp <- nfArgExtra "allowed" adv_allowed ppScript
    visible_pp <- nfArgExtra "visible" adv_visible ppScript
    available_pp <- nfArgExtra "available" adv_available ppScript
    onadd <- idArg "added" adv_on_add (indentUp . ppScript)
    onremove <- idArg "removed" adv_on_remove (indentUp . ppScript)
    mod <- nfArg adv_modifier ppStatement
    --equipmod <- nfArg adv_equipment_bonus ppStatement
    resmod <- nfArg adv_research_bonus ppStatement
    --tarmod <- nfArg adv_targeted_modifier ppScript
    traitmsg <- case adv_traits id of
        Just arr -> do
            --let traitbare = mapMaybe getbaretraits arr
            concatMapM getLeaderTraits arr
        _-> return []
    (traitids, traitloc) <- case adv_traits id of
        Just arr -> do
            let --traitbare = mapMaybe getbaretraits arr
                traitlist = map (\t-> "{{countrytrait|"<> t <> "|noname=1}}") arr
                traitids = T.intercalate "\n" traitlist
                traitids' = Doc.strictText traitids
            traitloc <- do
                tloc <- traverse getGameL10n arr
                let tloc' = map (T.replace "\n" " ") tloc
                return $ T.intercalate "<br>" tloc'
            return  (traitids', traitloc)
        _-> return ("","")
    traitmsg_pp <- imsg2doc traitmsg
    return . mconcat $
        [ "|- ", PP.line
        , "| ", Doc.strictText $ adv_advisor_slot id, PP.line
        , "{{advisors/row", PP.line
        , "| advisor = ", maybe mempty (\i -> "<!-- " <> Doc.strictText i <> " -->") icon_pp, "{{image title|", Doc.strictText $ name_pp <> " (advisor)"
        , "|", Doc.strictText name_pp, "}}<!-- ", Doc.strictText (if cha_id cha == adv_idea_token id then adv_idea_token id else cha_id cha <> " " <> adv_idea_token id), " -->", PP.line
        , "| trait = ",Doc.strictText traitloc,PP.line
        , "| desc = ",maybe mempty (Doc.strictText . Doc.nl2br) desc_pp, PP.line
        , "| prereq =",PP.line]++
        allowed_pp ++
        visible_pp ++
        available_pp ++
        [ "| effect = ",PP.line]++
--        (if id_category id `elem` ["tank_manufacturer", "naval_manufacturer", "aircraft_manufacturer", "materiel_manufacturer", "industrial_concern"] then
--            resmod ++
--            mod -- ++
--            tarmod
--        else
            mod ++
--            tarmod ++
            resmod++
--        equipmod ++
        [ traitids,--traitmsg_pp,
        PP.line]++
        (if adv_can_be_fired id then [""] else ["* {{color|R|Advisor can't be fired}}",PP.line])++
        onadd ++
        onremove ++
        [ "| cost = ",  maybe (if adv_advisor_slot id == "political_advisor" || adv_advisor_slot id == "theorist" then "{{icon|political power|150}} }}" else "{{icon|political power|50}} }}") (\c -> "{{icon|political power|"<> plainNum c <>"}} }}") (adv_cost id), PP.line]
