
{-# LANGUAGE TupleSections #-}
module HOI4.SpecialHandlers (
        handleIdeas
    ,   handleTimedIdeas
    ,   handleSwapIdeas
    ,   handleModifier
    ,   showIdea
    ,   plainmodifiermsg
    ,   modifierMSG
    ,   handleResearchBonus
    ,   handleTargetedModifier
    ,   handleEquipmentBonus
    ,   addDynamicModifier
    ,   removeDynamicModifier
    ,   hasDynamicModifier
    ,   addFieldMarshalRole
    ,   addAdvisorRole
    ,   removeAdvisorRole
    ,   addLeaderRole
    ,   createLeader
    ,   promoteCharacter
    ,   setCharacterName
    ,   withCharacter
    ,   createOperativeLeader
    ,   handleTrait
    ,   addRemoveLeaderTrait
    ,   addRemoveUnitTrait
    ,   addTimedTrait
    ,   swapLeaderTrait
    ) where

import Data.Char (toUpper, toLower, isUpper)
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Encoding as TE

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
--import Data.Set (Set)
import qualified Data.Set as S
import Data.Trie (Trie)
import qualified Data.Trie as Tr

import qualified Text.PrettyPrint.Leijen.Text as PP

import Data.List (foldl', intersperse, intercalate)
import Data.Maybe

import Control.Applicative (liftA2)
import Control.Arrow (first)
import Control.Monad (foldM, mplus, forM, join, when)
import Data.Foldable (fold)
import Data.Monoid ((<>))

import Abstract -- everything
import Doc (Doc)
import qualified Doc -- everything
import HOI4.Messages -- everything
import MessageTools (plural, iquotes, italicText, boldText
                    , colourNumSign, plainNumSign, plainPc, colourPc, reducedNum
                    , formatDays, formatHours)
import QQ -- everything
import SettingsTypes ( PPT, IsGameData (..), GameData (..), IsGameState (..), GameState (..)
                     , indentUp, indentDown, getCurrentIndent, withCurrentIndent, withCurrentIndentZero, withCurrentIndentCustom, alsoIndent, alsoIndent'
                     , getGameL10n, getGameL10nIfPresent, getGameL10nDefault, withCurrentFile
                     , unfoldM, unsnoc, concatMapM)
import HOI4.Templates
import {-# SOURCE #-} HOI4.Common (ppScript, ppMany, ppOne, extractStmt, matchLhsText)
import HOI4.Types -- everything
import Debug.Trace
import HOI4.Handlers -- everything
import System.Posix.Internals (st_mtime)

-----------------
-- handle idea --
-----------------

handleSwapIdeas :: forall g m. (HOI4Info g, Monad m) =>
        StatementHandler g m
handleSwapIdeas stmt@[pdx| %_ = @scr |]
    = pp_si (parseTA "add_idea" "remove_idea" scr)
    where
        pp_si :: TextAtom -> PPT g m IndentedMessages
        pp_si ta = case (ta_what ta, ta_atom ta) of
            (Just what, Just atom) -> do
                add_loc <- handleIdea True what
                remove_loc <- handleIdea False atom
                case (add_loc, remove_loc) of
                    (Just (addcategory, addideaIcon, addideaKey, addidea_loc, Just addeffectbox),
                     Just (category, ideaIcon, ideaKey, idea_loc, _)) ->
                        if addidea_loc == idea_loc then do
                                idmsg <- msgToPP $ MsgModifyIdea category ideaIcon ideaKey idea_loc
                                                    addcategory addideaIcon addideaKey addidea_loc
                                return $ idmsg ++ addeffectbox
                        else do
                            idmsg <- msgToPP $ MsgReplaceIdea category ideaIcon ideaKey idea_loc
                                                addcategory addideaIcon addideaKey addidea_loc
                            return $ idmsg ++ addeffectbox
                    (Just (addcategory, addideaIcon, addideaKey, addidea_loc, Nothing),
                     Just (category, ideaIcon, ideaKey, idea_loc, _)) ->
                        if addidea_loc == idea_loc then
                            msgToPP $ MsgModifyIdea category ideaIcon ideaKey idea_loc
                                addcategory addideaIcon addideaKey addidea_loc
                        else
                            msgToPP $ MsgReplaceIdea category ideaIcon ideaKey idea_loc
                                addcategory addideaIcon addideaKey addidea_loc
                    _ -> preStatement stmt
            _ -> preStatement stmt
handleSwapIdeas stmt = preStatement stmt

handleTimedIdeas :: forall g m. (HOI4Info g, Monad m) =>
        (Text -> Text -> Text -> Text -> Double -> ScriptMessage) -- ^ Message constructor, if abs value >= 1
        -> StatementHandler g m
handleTimedIdeas msg stmt@[pdx| %_ = @scr |]
    = pp_idda (parseTV "idea" "days" scr)
    where
        pp_idda :: TextValue -> PPT g m IndentedMessages
        pp_idda tv = case (tv_what tv, tv_value tv) of
            (Just what, Just value) -> do
                ideashandled <- handleIdea True what
                case ideashandled of
                    Just (category, ideaIcon, ideaKey, idea_loc, Just effectbox) -> do
                        idmsg <- msgToPP $ msg category ideaIcon ideaKey idea_loc value
                        return $ idmsg ++ effectbox
                    Just (category, ideaIcon, ideaKey, idea_loc, Nothing) -> msgToPP $ msg category ideaIcon ideaKey idea_loc value
                    Nothing -> preStatement stmt
            _ -> preStatement stmt
handleTimedIdeas _ stmt = preStatement stmt

handleIdeas :: forall g m. (HOI4Info g, Monad m) =>
    Bool ->
    (Text -> Text -> Text -> Text -> ScriptMessage)
        -> StatementHandler g m
handleIdeas addIdea msg stmt@[pdx| $lhs = %idea |] = case idea of
    CompoundRhs ideas -> if length ideas == 1 then do
                ideashandled <- handleIdea addIdea (mconcat $ map getbareidea ideas)
                case ideashandled of
                    Just (category, ideaIcon, ideaKey, idea_loc, Just effectbox) -> do
                        idmsg <- msgToPP $ msg category ideaIcon ideaKey idea_loc
                        return $ idmsg ++ effectbox
                    Just (category, ideaIcon, ideaKey, idea_loc, Nothing) -> msgToPP $ msg category ideaIcon ideaKey idea_loc
                    Nothing -> preStatement stmt
            else do
                ideashandle <- mapM (handleIdea addIdea . getbareidea) ideas
                let ideashandled = catMaybes ideashandle
                    ideasmsgd :: [(Text, Text, Text, Text, Maybe IndentedMessages)] -> PPT g m [IndentedMessages]
                    ideasmsgd ihs = mapM (\ih ->
                            let (category, ideaIcon, ideaKey, idea_loc, effectbox) = ih in
                            withCurrentIndent $ \i -> case effectbox of
                                    Just boxNS -> return ((i, msg category ideaIcon ideaKey idea_loc):boxNS)
                                    _-> return [(i, msg category ideaIcon ideaKey idea_loc)]
                                ) ihs
                ideasmsgdd <- ideasmsgd ideashandled
                return $ mconcat ideasmsgdd
    GenericRhs txt [] -> do
        ideashandled <- handleIdea addIdea txt
        case ideashandled of
            Just (category, ideaIcon, ideaKey, idea_loc, Just effectbox) -> do
                idmsg <- msgToPP $ msg category ideaIcon ideaKey idea_loc
                return $ idmsg ++ effectbox
            Just (category, ideaIcon, ideaKey, idea_loc, Nothing) -> msgToPP $ msg category ideaIcon ideaKey idea_loc
            Nothing -> preStatement stmt
    _ -> preStatement stmt
handleIdeas _ _ stmt = preStatement stmt

getbareidea :: GenericStatement -> Text
getbareidea (StatementBare (GenericLhs e [])) = e
getbareidea _ = "<!-- Check Script -->"

handleIdea :: (HOI4Info g, Monad m) =>
        Bool -> Text ->
           PPT g m (Maybe (Text, Text, Text, Text, Maybe IndentedMessages))
handleIdea addIdea ide = do
    ides <- getIdeas
    charto <- getCharToken
    gfx <- getInterfaceGFX
    let midea = HM.lookup ide ides
    case midea of
        Just iidea -> do
            let ideaKey = id_name iidea
                ideaIcon = HM.findWithDefault "GFX_idea_unknown" (id_picture iidea) gfx
            idea_loc <- getGameL10n ideaKey
            category <- if id_category iidea == "country" then getGameL10n "FE_COUNTRY_SPIRIT" else getGameL10n $ id_category iidea
            effectbox <- modmessage iidea idea_loc ideaKey ideaIcon
            effectboxNS <- if id_category iidea == "country" && addIdea then return $ Just effectbox else return Nothing
            return $ Just (category, ideaIcon, ideaKey, idea_loc, effectboxNS)
        Nothing -> case HM.lookup ide charto of
            Nothing -> return Nothing
            Just cchat -> do
                let name_loc = chaName cchat
                    namekey = chaTag cchat
                slot <- maybe (return "<!-- Check Script -->") getGameL10n (cha_advisor_slot cchat)
                return $ Just (slot, "", namekey, name_loc, Nothing)


showIdea :: (HOI4Info g, Monad m) => StatementHandler g m
showIdea stmt@[pdx| $lhs = $idea |] = do
    ides <- getIdeas
    charto <- getCharToken
    case HM.lookup idea ides of
        Just iidea -> do
            modifier <- maybe (return []) (indentUp . ppOne) (id_modifier iidea)
            targeted_modifier <-
                maybe (return []) (indentUp . fmap concat . mapM handleTargetedModifier) (id_targeted_modifier iidea)
            research_bonus <- maybe (return []) (indentUp . ppOne) (id_research_bonus iidea)
            equipment_bonus <- maybe (return []) (indentUp . ppOne) (id_equipment_bonus iidea)
            let ideamods = modifier ++ targeted_modifier ++ research_bonus ++ equipment_bonus
            idea_loc <- getGameL10n (id_name iidea)
            basemsg <- msgToPP $ MsgShowIdea idea_loc idea
            return $ basemsg ++ ideamods
        Nothing -> case HM.lookup idea charto of
            Nothing -> preStatement stmt
            Just ccharto -> do
                let name_loc = chaName ccharto
                    traits = case chaAdvisorTraits ccharto of
                        Just trts -> trts
                        _-> []
                modmsg <- maybe (return []) (indentUp .handleModifier) (cha_adv_modifier ccharto)
                resmsg <- maybe (return []) (indentUp .handleResearchBonus) (cha_adv_research_bonus ccharto)
                traitmsg <- concatMapM ppHt traits
                basemsg <- msgToPP $ MsgShowIdea name_loc idea
                return $ basemsg ++ traitmsg ++ modmsg ++ resmsg
showIdea stmt = preStatement stmt

modmessage :: forall g m. (HOI4Info g, Monad m) => HOI4Idea -> Text -> Text -> Text -> PPT g m IndentedMessages
modmessage iidea idea_loc ideaKey ideaIcon = do
        curind <- getCurrentIndent
        curindent <- case curind of
            Just curindt -> return curindt
            _ -> return 1
        withCurrentIndentCustom 1 $ \_ -> do
            ideaDesc <- case id_desc_loc iidea of
                Just desc -> return $ Doc.nl2br desc
                _ -> return ""
            modifier <- maybe (return []) ppOne (id_modifier iidea)
            targeted_modifier <-
                maybe (return []) (fmap concat . mapM handleTargetedModifier) (id_targeted_modifier iidea)
            research_bonus <- maybe (return []) ppOne (id_research_bonus iidea)
            equipment_bonus <- maybe (return []) ppOne (id_equipment_bonus iidea)
            let boxend = [(0, MsgEffectBoxEnd)]
            withCurrentIndentCustom curindent $ \_ -> do
                let ideamods = modifier ++ targeted_modifier ++ research_bonus ++ equipment_bonus ++ boxend
                return $ (0, MsgEffectBox idea_loc ideaKey ideaIcon ideaDesc) : ideamods


-----------------------
-- modifier handlers --
-----------------------
plainmodifiermsg :: forall g m. (HOI4Info g, Monad m) =>
        ScriptMessage -> StatementHandler g m
plainmodifiermsg msg stmt@[pdx| %_ = @scr |] = do
    let (mmod, _) = extractStmt (matchLhsText "modifier") scr
    modmsg <- case mmod of
        Just stmt@[pdx| modifier = @_ |] -> indentUp $ handleModifier stmt
        _ -> preStatement stmt
    basemsg <- msgToPP msg
    return $ basemsg ++ modmsg
plainmodifiermsg _ stmt = preStatement stmt

handleModifier :: forall g m. (HOI4Info g, Monad m) =>
        StatementHandler g m
handleModifier [pdx| %_ = @scr |] = fold <$> traverse (modifierMSG False) scr
handleModifier stmt = preStatement stmt

modifierMSG :: forall g m. (HOI4Info g, Monad m) =>
        Bool -> StatementHandler g m
modifierMSG _ stmt@[pdx| $specmod = @scr|]
    | specmod == "hidden_modifier" = fold <$> traverse (modifierMSG True) scr
    | otherwise = do
        --terrain <- getTerrain
        --if specmod `elem` terrain
        --then do
            termsg <- plainMsg' . (<> ":") . boldText =<< getGameL10n specmod
            modmsg <- fold <$> indentUp (traverse (modifierMSG False) scr)
            return $ termsg : modmsg
        --else trace ("unknown modifier type: " ++ show specmod ++ " IN: " ++ show stmt) $ preStatement stmt
modifierMSG hidden stmt@[pdx| $mod = !num|] = let lmod = T.toLower mod in case HM.lookup lmod modifiersTable of
    Just (loc, msg) ->
        let bonus = num :: Double
            loc' = locprep hidden loc in
        numericLoc loc' msg stmt
    Nothing
        | "cat_" `T.isPrefixOf` lmod -> do
            mloc <- getGameL10nIfPresent lmod
            case mloc of
                Just loc ->
                    let loc' = locprep hidden loc in
                    numericLoc loc' MsgModifierPcNegReduced stmt
                Nothing -> preStatement stmt
        | ("production_speed_" `T.isPrefixOf` lmod && "_factor" `T.isSuffixOf` lmod) ||
            ("experience_gain_" `T.isPrefixOf` lmod && "_combat_factor" `T.isSuffixOf` lmod) ||
            ("trait_" `T.isPrefixOf` lmod && "_xp_gain_factor" `T.isSuffixOf` lmod) -> do
            mloc <- getGameL10nIfPresent ("modifier_" <> lmod)
            case mloc of
                Just loc ->
                    let loc' = locprep hidden loc in
                    numericLoc loc' MsgModifierPcPosReduced stmt
                Nothing -> preStatement stmt
        | "unit_" `T.isPrefixOf` lmod && "_design_cost_factor" `T.isSuffixOf` lmod -> do
            mloc <- getGameL10nIfPresent ("modifier_" <> lmod)
            case mloc of
                Just loc ->
                    let loc' = locprep hidden loc in
                    numericLoc loc' MsgModifierPcNegReduced stmt
                Nothing -> preStatement stmt
        | "modifier_army_sub_" `T.isPrefixOf` lmod -> do
            mloc <- getGameL10nIfPresent lmod
            case mloc of
                Just loc ->
                    let loc' = locprep hidden loc in
                    numericLoc loc' MsgModifierPcPosReduced stmt
                Nothing -> preStatement stmt
        | lmod == "no_compliance_gain" && num == 1 -> do
            comploc <- getGameL10n "MODIFIER_NO_COMPLIANCE_GAIN"
            plainMsg comploc
        | lmod == "disabled_ideas" && num == 1 -> do
            idloc <- getGameL10n "MODIFIER_DISABLE_IDEA_TAKING"
            plainMsg idloc
        | lmod == "cannot_use_abilities" && num == 1 -> do
            abloc <- getGameL10n "MODIFIER_CANNOT_USE_ABILITIES"
            plainMsg abloc
        | otherwise -> preStatement stmt
modifierMSG _ stmt@[pdx| custom_modifier_tooltip = $key|] = do
    loc <- getGameL10nIfPresent key
    maybe (preStatement stmt)
        (msgToPP . MsgCustomModifierTooltip)
        loc
modifierMSG hidden stmt@[pdx| $mod = $var|] =  let lmod = T.toLower mod in case HM.lookup lmod modifiersTable of
    Just (loc, msg) -> do
        locced <- getGameL10n loc
        let loc' = locprep hidden locced
        msgToPP $ MsgModifierVar loc' var
    Nothing
        | "cat_" `T.isPrefixOf` lmod -> do
            mloc <- getGameL10nIfPresent lmod
            case mloc of
                Just loc ->
                    let loc' = locprep hidden loc in
                    msgToPP $ MsgModifierVar loc' var
                Nothing -> preStatement stmt
        | ("production_speed_" `T.isPrefixOf` lmod && "_factor" `T.isSuffixOf` lmod) ||
            ("unit_" `T.isPrefixOf` lmod && "_design_cost_factor" `T.isSuffixOf` lmod) ||
            ("experience_gain_" `T.isPrefixOf` lmod && "_combat_factor" `T.isSuffixOf` lmod) ||
            ("trait_" `T.isPrefixOf` lmod && "_xp_gain_factor" `T.isSuffixOf` lmod) -> do
            mloc <- getGameL10nIfPresent ("modifier_" <> lmod)
            case mloc of
                Just loc ->
                    let loc' = locprep hidden loc in
                    msgToPP $ MsgModifierVar loc' var
                Nothing -> preStatement stmt
        | "modifier_army_sub_" `T.isPrefixOf` lmod -> do
            mloc <- getGameL10nIfPresent lmod
            case mloc of
                Just loc ->
                    let loc' = locprep hidden loc in
                    msgToPP $ MsgModifierVar loc' var
                Nothing -> preStatement stmt
        | otherwise -> preStatement stmt
modifierMSG _ stmt = preStatement stmt

locprep :: Bool -> Text -> Text
locprep hidden loc = do
    let loc' = if ": " `T.isSuffixOf` loc then T.dropEnd 2 loc else loc
    if hidden then "(Hidden)" <> loc' else loc'

handleResearchBonus :: forall g m. (HOI4Info g, Monad m) =>
        StatementHandler g m
handleResearchBonus [pdx| %_ = @scr |] = fold <$> traverse handleResearchBonus' scr
    where
        handleResearchBonus' stmt@[pdx| $tech = !num |] = let bonus = num :: Double in numericLoc (T.toLower tech <> "_research") MsgModifierPcPosReduced stmt
        handleResearchBonus' scr = preStatement scr
handleResearchBonus stmt = preStatement stmt

handleTargetedModifier :: forall g m. (HOI4Info g, Monad m) =>
        StatementHandler g m
handleTargetedModifier stmt@[pdx| %_ = @scr |] = do
    let (tag, rest) = extractStmt (matchLhsText "tag") scr
    tagmsg <- case tag of
        Just [pdx| tag = $country |] -> flagText (Just HOI4Country) country
        _ -> return "CHECK SCRIPT"
    fold <$> traverse (modifierTagMSG tagmsg) rest
        where
            modifierTagMSG tagmsg stmt@[pdx| $mod = !num |] = let bonus = num :: Double in case HM.lookup (T.toLower mod) modifiersTable of
                Just (loc, msg) -> do
                    locced <- getGameL10n loc
                    let locced' = if ": " `T.isSuffixOf` locced then T.dropEnd 2 locced else locced
                    numericLoc ("(" <> tagmsg <> ")" <> locced') msg stmt
                Nothing -> preStatement stmt
            modifierTagMSG _ stmt = preStatement stmt
handleTargetedModifier stmt = preStatement stmt


handleEquipmentBonus :: forall g m. (HOI4Info g, Monad m) =>
        StatementHandler g m
handleEquipmentBonus stmt@[pdx| %_ = @scr |] = fold <$> traverse modifierEquipMSG scr
        where
            modifierEquipMSG [pdx| $tech = @scr |] = do
                let (_, rest) = extractStmt (matchLhsText "instant") scr
                techmsg <- plainMsg' . (<> ":") . boldText =<< getGameL10n tech
                modmsg <- fold <$> indentUp (traverse modifierEquipMSG' rest)
                return $ techmsg : modmsg
            modifierEquipMSG stmt = preStatement stmt

            modifierEquipMSG' stmt@[pdx| $mod = !num |] = case HM.lookup (T.toLower mod) modifiersTable of
                Just (loc, msg) -> do
                    let bonus = num :: Double
                    locced <- getGameL10n loc
                    let locced' = if ": " `T.isSuffixOf` locced then T.dropEnd 2 locced else locced
                    numericLoc locced' msg stmt
                Nothing -> preStatement stmt
            modifierEquipMSG' stmt = preStatement stmt
handleEquipmentBonus stmt = preStatement stmt


-- | Handlers for numeric statements with icons
modifiersTable :: HashMap Text (Text, Text -> Double -> ScriptMessage)
modifiersTable = HM.fromList
        [
        --general modifiers
         ("monthly_population"              , ("MODIFIER_GLOBAL_MONTHLY_POPULATION", MsgModifierPcPosReduced))
        ,("nuclear_production_factor"       , ("MODIFIER_NUCLEAR_PRODUCTION_FACTOR", MsgModifierPcPosReduced))
        ,("research_sharing_per_country_bonus" , ("MODIFIER_RESEARCH_SHARING_PER_COUNTRY_BONUS", MsgModifierPcPosReduced))
        ,("research_sharing_per_country_bonus_factor" , ("MODIFIER_RESEARCH_SHARING_PER_COUNTRY_BONUS_FACTOR", MsgModifierPcPosReduced))
        ,("research_speed_factor"           , ("MODIFIER_RESEARCH_SPEED_FACTOR", MsgModifierPcPosReduced))
        ,("local_resources_factor"          , ("MODIFIER_LOCAL_RESOURCES_FACTOR", MsgModifierPcPosReduced))

            -- Politics modifiers
        ,("min_export"                      , ("MODIFIER_MIN_EXPORT_FACTOR", MsgModifierPcReducedSign)) -- yellow
        ,("trade_opinion_factor"            , ("MODIFIER_TRADE_OPINION_FACTOR", MsgModifierPcReducedSign))
        ,("economy_cost_factor"             , ("economy_cost_factor", MsgModifierPcNegReduced))
        ,("mobilization_laws_cost_factor"   , ("mobilization_laws_cost_factor", MsgModifierPcNegReduced))
        ,("political_advisor_cost_factor"   , ("political_advisor_cost_factor", MsgModifierPcNegReduced))
        ,("trade_laws_cost_factor"          , ("trade_laws_cost_factor", MsgModifierPcNegReduced))
        ,("tank_manufacturer_cost_factor"   , ("tank_manufacturer_cost_factor", MsgModifierPcNegReduced))
        ,("naval_manufacturer_cost_factor"  , ("naval_manufacturer_cost_factor", MsgModifierPcNegReduced))
        ,("aircraft_manufacturer_cost_factor" , ("aircraft_manufacturer_cost_factor", MsgModifierPcNegReduced))
        ,("materiel_manufacturer_cost_factor" , ("materiel_manufacturer_cost_factor", MsgModifierPcNegReduced))
        ,("industrial_concern_cost_factor"  , ("industrial_concern_cost_factor", MsgModifierPcNegReduced))
        ,("theorist_cost_factor"            , ("theorist_cost_factor", MsgModifierPcNegReduced))
        ,("army_chief_cost_factor"          , ("army_chief_cost_factor", MsgModifierPcNegReduced))
        ,("navy_chief_cost_factor"          , ("navy_chief_cost_factor", MsgModifierPcNegReduced))
        ,("air_chief_cost_factor"           , ("air_chief_cost_factor", MsgModifierPcNegReduced))
        ,("high_command_cost_factor"        , ("high_command_cost_factor", MsgModifierPcNegReduced))
        ,("offensive_war_stability_factor"  , ("MODIFIER_STABILITY_OFFENSIVE_WAR_FACTOR", MsgModifierPcPosReduced))
        ,("defensive_war_stability_factor"  , ("MODIFIER_STABILITY_DEFENSIVE_WAR_FACTOR", MsgModifierPcPosReduced))
        ,("improve_relations_maintain_cost_factor" , ("MODIFIER_IMPROVE_RELATIONS_MAINTAIN_COST_FACTOR", MsgModifierPcNegReduced))
        ,("party_popularity_stability_factor" , ("MODIFIER_STABILITY_POPULARITY_FACTOR", MsgModifierPcPosReduced))
        ,("political_power_cost"            , ("MODIFIER_POLITICAL_POWER_COST", MsgModifierColourNeg))
        ,("political_power_gain"            , ("MODIFIER_POLITICAL_POWER_GAIN", MsgModifierColourPos))
        ,("political_power_factor"          , ("MODIFIER_POLITICAL_POWER_FACTOR", MsgModifierPcPosReduced))
        ,("stability_factor"                , ("MODIFIER_STABILITY_FACTOR", MsgModifierPcPosReduced))
        ,("stability_weekly"                , ("MODIFIER_STABILITY_WEEKLY", MsgModifierPcPosReduced))
        ,("stability_weekly_factor"         , ("MODIFIER_STABILITY_WEEKLY_FACTOR", MsgModifierPcPosReduced))
        ,("war_stability_factor"            , ("MODIFIER_STABILITY_WAR_FACTOR", MsgModifierPcPosReduced))
        ,("war_support_factor"              , ("MODIFIER_WAR_SUPPORT_FACTOR", MsgModifierPcPosReduced))
        ,("war_support_weekly"              , ("MODIFIER_WAR_SUPPORT_WEEKLY", MsgModifierPcPosReduced))
        ,("war_support_weekly_factor"       , ("MODIFIER_WAR_SUPPORT_WEEKLY_FACTOR", MsgModifierPcPosReduced))
        ,("drift_defence_factor"            , ("MODIFIER_DRIFT_DEFENCE_FACTOR", MsgModifierPcPosReduced))
        ,("communism_drift"                 , ("communism_drift", MsgModifierColourPos))
        ,("democratic_drift"                , ("democratic_drift", MsgModifierColourPos))
        ,("fascism_drift"                   , ("fascism_drift", MsgModifierColourPos))
        ,("neutrality_drift"                , ("neutrality_drift", MsgModifierColourPos))
        ,("communism_acceptance"            , ("communism_acceptance", MsgModifierColourPos))
        ,("democratic_acceptance"           , ("democratic_acceptance", MsgModifierColourPos))
        ,("fascism_acceptance"              , ("fascism_acceptance", MsgModifierColourPos))
        ,("neutrality_acceptance"           , ("neutrality_acceptance", MsgModifierColourPos))

            -- Diplomacy
        ,("enemy_justify_war_goal_time"     , ("MODIFIER_ENEMY_JUSTIFY_WAR_GOAL_TIME", MsgModifierPcPosReduced))
        ,("generate_wargoal_tension"        , ("MODIFIER_GENERATE_WARGOAL_TENSION_LIMIT", MsgModifierPcReduced)) -- yellow
        ,("guarantee_cost"                  , ("MODIFIER_GUARANTEE_COST", MsgModifierPcNegReduced))
        ,("guarantee_tension"               , ("MODIFIER_GUARANTEE_TENSION_LIMIT", MsgModifierPcNegReduced))
        ,("join_faction_tension"            , ("MODIFIER_JOIN_FACTION_TENSION_LIMIT", MsgModifierPcNegReduced))
        ,("justify_war_goal_time"           , ("MODIFIER_JUSTIFY_WAR_GOAL_TIME", MsgModifierPcNegReduced))
        ,("justify_war_goal_when_in_major_war_time" , ("MODIFIER_JUSTIFY_WAR_GOAL_WHEN_IN_MAJOR_WAR_TIME", MsgModifierPcNegReduced))
        ,("lend_lease_tension"              , ("MODIFIER_LEND_LEASE_TENSION_LIMIT", MsgModifierPcNegReduced))
        --,("opinion_gain_monthly"            , ("MODIFIER_OPINION_GAIN_MONTHLY", MsgModifier)) -- flat pos
        ,("opinion_gain_monthly_factor"     , ("MODIFIER_OPINION_GAIN_MONTHLY_FACTOR", MsgModifierPcPosReduced))
        ,("opinion_gain_monthly_same_ideology_factor" , ("MODIFIER_OPINION_GAIN_MONTHLY_SAME_IDEOLOGY_FACTOR", MsgModifierPcPosReduced))
        ,("request_lease_tension"           , ("MODIFIER_REQUEST_LEASE_TENSION_LIMIT", MsgModifierPcNegReduced))
        ,("annex_cost_factor"               , ("MODIFIER_ANNEX_COST_FACTOR", MsgModifierPcNegReduced))
        ,("surrender_limit"                 , ("MODIFIER_SURRENDER_LIMIT", MsgModifierPcPosReduced))
        ,("send_volunteer_divisions_required" , ("MODIFIER_SEND_VOLUNTEER_DIVISIONS_REQUIRED", MsgModifierPcNegReduced))
        ,("send_volunteer_size"             , ("MODIFIER_SEND_VOLUNTEER_SIZE", MsgModifierColourPos))
        ,("send_volunteers_tension"         , ("MODIFIER_SEND_VOLUNTEERS_TENSION_LIMIT", MsgModifierPcNegReduced))

            -- autonomy
        ,("subjects_autonomy_gain"          , ("MODIFIER_AUTONOMY_SUBJECT_GAIN", MsgModifierColourPos))
        ,("master_ideology_drift"           , ("MODIFIER_MASTER_IDEOLOGY_DRIFT", MsgModifierColourPos))

            -- Governments in exile

        ,("dockyard_donations "             , ("MODIFIER_DOCKYARD_DONATIONS", MsgModifierColourPos))
        ,("industrial_factory_donations"    , ("MODIFIER_INDUSTRIAL_FACTORY_DONATIONS", MsgModifierColourPos))
        ,("military_factory_donations"     , ("MODIFIER_MILITARY_FACTORY_DONATIONS", MsgModifierColourPos))
        ,("exile_manpower_factor"           , ("MODIFIER_EXILED_MAPOWER_GAIN_FACTOR", MsgModifierPcPosReduced))
        ,("exiled_government_weekly_manpower" , ("MODIFIER_EXILED_GOVERNMENT_WEEKLY_MANPOWER", MsgModifierColourPos))
        ,("legitimacy_daily"                , ("MODIFIER_LEGITIMACY_DAILY", MsgModifierColourPos))

            -- Equipment
        ,("equipment_capture_factor"        , ("MODIFIER_EQUIPMENT_CAPTURE_FACTOR", MsgModifierPcPosReduced))
        ,("equipment_conversion_speed"      , ("EQUIPMENT_CONVERSION_SPEED_MODIFIERS", MsgModifierPcPosReduced))
        ,("equipment_upgrade_xp_cost"       , ("MODIFIER_EQUIPMENT_UPGRADE_XP_COST", MsgModifierPcNegReduced))
        ,("license_purchase_cost"           , ("MODIFIER_LICENSE_PURCHASE_COST", MsgModifierPcNegReduced))
        ,("license_tech_difference_speed"   , ("MODIFIER_LICENSE_TECH_DIFFERENCE_SPEED", MsgModifierPcPosReduced))
        ,("license_production_speed"        , ("MODIFIER_LICENSE_PRODUCTION_SPEED", MsgModifierPcPosReduced))
        ,("license_armor_purchase_cost"     , ("MODIFIER_LICENSE_ARMOR_PURCHASE_COST", MsgModifierPcNegReduced))
        ,("license_air_purchase_cost"       , ("MODIFIER_LICENSE_AIR_PURCHASE_COST", MsgModifierPcNegReduced))
        ,("license_naval_purchase_cost"     , ("MODIFIER_LICENSE_NAVAL_PURCHASE_COST", MsgModifierPcNegReduced))
        ,("production_factory_efficiency_gain_factor" , ("MODIFIER_PRODUCTION_FACTORY_EFFICIENCY_GAIN_FACTOR", MsgModifierPcPosReduced))
        ,("production_factory_max_efficiency_factor" , ("MODIFIER_PRODUCTION_FACTORY_MAX_EFFICIENCY_FACTOR", MsgModifierPcPosReduced))
        ,("production_factory_start_efficiency_factor" , ("MODIFIER_PRODUCTION_FACTORY_START_EFFICIENCY_FACTOR", MsgModifierPcPosReduced))

            -- Military outside of combat
        ,("command_power_gain"              , ("MODIFIER_COMMAND_POWER_GAIN", MsgModifierColourPos))
        ,("command_power_gain_mult"         , ("MODIFIER_COMMAND_POWER_GAIN_MULT", MsgModifierPcPosReduced))
        ,("conscription"                    , ("MODIFIER_CONSCRIPTION_FACTOR", MsgModifierPcReducedSign)) --yellow
        ,("conscription_factor"             , ("MODIFIER_CONSCRIPTION_TOTAL_FACTOR", MsgModifierPcPosReduced))
        ,("dig_in_speed_factor"             , ("MODIFIER_DIG_IN_SPEED_FACTOR", MsgModifierPcPosReduced))
        ,("experience_gain_air"             , ("MODIFIER_XP_GAIN_AIR", MsgModifierColourPos))
        ,("experience_gain_air_factor"      , ("MODIFIER_XP_GAIN_AIR_FACTOR", MsgModifierPcPosReduced))
        ,("experience_gain_army"            , ("MODIFIER_XP_GAIN_ARMY", MsgModifierColourPos))
        ,("experience_gain_army_factor"     , ("MODIFIER_XP_GAIN_ARMY_FACTOR", MsgModifierPcPosReduced))
        ,("experience_gain_navy"            , ("MODIFIER_XP_GAIN_NAVY", MsgModifierColourPos))
        ,("experience_gain_navy_factor"     , ("MODIFIER_XP_GAIN_NAVY_FACTOR", MsgModifierPcPosReduced))
        ,("land_reinforce_rate"             , ("MODIFIER_LAND_REINFORCE_RATE", MsgModifierPcPosReduced))
        ,("training_time_factor"            , ("MODIFIER_TRAINING_TIME_FACTOR", MsgModifierPcNegReduced))
        ,("minimum_training_level"          , ("MODIFIER_MINIMUM_TRAINING_LEVEL", MsgModifierPcNegReduced))
        ,("air_doctrine_cost_factor"        , ("MODIFIER_AIR_DOCTRINE_COST_FACTOR", MsgModifierPcNegReduced))
        ,("land_doctrine_cost_factor"       , ("MODIFIER_LAND_DOCTRINE_COST_FACTOR", MsgModifierPcNegReduced))
        ,("naval_doctrine_cost_factor"      , ("MODIFIER_NAVAL_DOCTRINE_COST_FACTOR", MsgModifierPcNegReduced))
        ,("max_command_power"               , ("MODIFIER_MAX_COMMAND_POWER", MsgModifierColourPos))
--        ,("max_command_power_mult"          , ("MODIFIER_MAX_COMMAND_POWER_MULT", MsgModifier))  -- % pos
        ,("training_time_army_factor"       , ("MODIFIER_TRAINING_TIME_ARMY_FACTOR", MsgModifierPcReducedSign)) --yellow
        ,("weekly_manpower"                 , ("MODIFIER_WEEKLY_MANPOWER", MsgModifierColourPos))

            -- Fuel and supplies
        ,("base_fuel_gain"                  , ("MODIFIER_BASE_FUEL_GAIN_ADD", MsgModifierColourPos))
        ,("base_fuel_gain_factor"           , ("MODIFIER_BASE_FUEL_GAIN_FACTOR", MsgModifierPcPosReduced))
        --,("fuel_cost"                       , ("MODIFIER_FUEL_COST", MsgModifier)) -- flat neg
        --,("fuel_gain"                       , ("MODIFIER_FUEL_GAIN_ADD", MsgModifier)) -- flat pos
        ,("fuel_gain_factor"                , ("MODIFIER_MAX_FUEL_FACTOR", MsgModifierPcPosReduced))
        --,("max_fuel"                        , ("MODIFIER_MAX_FUEL_ADD", MsgModifier)) -- flat
        ,("max_fuel_factor"                 , ("MODIFIER_MAX_FUEL_FACTOR", MsgModifierPcPosReduced))
        ,("army_fuel_consumption_factor"    , ("MODIFIER_ARMY_FUEL_CONSUMPTION_FACTOR", MsgModifierPcNegReduced))
        ,("air_fuel_consumption_factor"     , ("MODIFIER_AIR_FUEL_CONSUMPTION_FACTOR", MsgModifierPcNegReduced))
        ,("navy_fuel_consumption_factor"    , ("MODIFIER_NAVY_FUEL_CONSUMPTION_FACTOR", MsgModifierPcNegReduced))
        ,("attrition"                       , ("MODIFIER_ATTRITION", MsgModifierPcNegReduced))
        ,("heat_attrition_factor"           , ("MODIFIER_HEAT_ATTRITION_FACTOR", MsgModifierPcNegReduced))
        ,("winter_attrition_factor"         , ("MODIFIER_WINTER_ATTRITION_FACTOR", MsgModifierPcNegReduced))
        ,("supply_combat_penalties_on_core_factor" , ("supply_combat_penalties_on_core_factor", MsgModifierPcNegReduced))
        ,("supply_consumption_factor"       , ("MODIFIER_SUPPLY_CONSUMPTION_FACTOR", MsgModifierPcNegReduced))
        ,("no_supply_grace"                 , ("MODIFIER_NO_SUPPLY_GRACE", MsgModifierColourPos))
        ,("out_of_supply_factor"            , ("MODIFIER_OUT_OF_SUPPLY_FACTOR", MsgModifierPcNegReduced))

            -- buildings
        ,("civilian_factory_use"            , ("MODIFIER_CIVILIAN_FACTORY_USE", MsgModifierColourNeg))
        ,("industry_free_repair_factor"     , ("MODIFIER_INDUSTRY_FREE_REPAIR_FACTOR", MsgModifierPcPosReduced))
        ,("consumer_goods_factor"           , ("MODIFIER_CONSUMER_GOODS_FACTOR", MsgModifierPcReducedSign))
        ,("conversion_cost_civ_to_mil_factor" , ("MODIFIER_CONVERSION_COST_CIV_TO_MIL_FACTOR", MsgModifierPcNegReduced))
        ,("conversion_cost_mil_to_civ_factor" , ("MODIFIER_CONVERSION_COST_MIL_TO_CIV_FACTOR", MsgModifierPcNegReduced))
        --,("global_building_slots"           , ("MODIFIER_GLOBAL_BUILDING_SLOTS", MsgModifierPcPosReduced)) -- flat
        ,("global_building_slots_factor"    , ("MODIFIER_GLOBAL_BUILDING_SLOTS_FACTOR", MsgModifierPcPosReduced))
        ,("industrial_capacity_dockyard"    , ("MODIFIER_INDUSTRIAL_CAPACITY_DOCKYARD_FACTOR", MsgModifierPcPosReduced))
        ,("industrial_capacity_factory"     , ("MODIFIER_INDUSTRIAL_CAPACITY_FACTOR", MsgModifierPcPosReduced))
        ,("industry_repair_factor"          , ("MODIFIER_INDUSTRY_REPAIR_FACTOR", MsgModifierPcPosReduced))
        ,("line_change_production_efficiency_factor" , ("MODIFIER_LINE_CHANGE_PRODUCTION_EFFICIENCY_FACTOR", MsgModifierPcPosReduced))
        ,("production_oil_factor"           , ("MODIFIER_PRODUCTION_OIL_FACTOR", MsgModifierPcPosReduced))
        ,("production_speed_buildings_factor" , ("MODIFIER_PRODUCTION_SPEED_BUILDINGS_FACTOR", MsgModifierPcPosReduced))

            -- resistance and compliance
        ,("occupation_cost"                 , ("MODIFIER_OCCUPATION_COST", MsgModifierColourNeg))
        ,("required_garrison_factor"        , ("MODIFIER_REQUIRED_GARRISON_FACTOR", MsgModifierPcNegReduced))
        ,("resistance_activity"             , ("MODIFIER_RESISTANCE_ACTIVITY_FACTOR", MsgModifierPcNegReduced))
        ,("resistance_damage_to_garrison_on_our_occupied_states" , ("MODIFIER_RESISTANCE_DAMAGE_TO_GARRISONS_ON_OUR_OCCUPIED_STATES", MsgModifierPcPosReduced))
        ,("resistance_growth_on_our_occupied_states" , ("MODIFIER_RESISTANCE_GROWTH_ON_OUR_OCCUPIED_STATES", MsgModifierPcPosReduced))

            -- Intelligence
        ,("decryption"                      , ("MODIFIER_DECRYPTION", MsgModifierColourPos))
        ,("decryption_factor"               , ("MODIFIER_DECRYPTION_FACTOR", MsgModifierPcPosReduced))
        ,("encryption"                      , ("MODIFIER_ENCRYPTION", MsgModifierColourPos))
        ,("encryption_factor"               , ("MODIFIER_ENCRYPTION_FACTOR", MsgModifierPcPosReduced))
        ,("civilian_intel_factor"           , ("MODIFIER_CIVILIAN_INTEL_FACTOR", MsgModifierPcPosReduced))
        ,("army_intel_factor"               , ("MODIFIER_ARMY_INTEL_FACTOR", MsgModifierPcPosReduced))
        ,("navy_intel_factor"               , ("MODIFIER_NAVY_INTEL_FACTOR", MsgModifierPcPosReduced))
        ,("airforce_intel_factor"           , ("MODIFIER_AIRFORCE_INTEL_FACTOR", MsgModifierPcPosReduced))
        ,("civilian_intel_to_others"        , ("MODIFIER_CIVILIAN_INTEL_TO_OTHERS", MsgModifierPcNeg))
        ,("army_intel_to_others"            , ("MODIFIER_ARMY_INTEL_TO_OTHERS", MsgModifierPcNeg))
        ,("navy_intel_to_others"            , ("MODIFIER_NAVY_INTEL_TO_OTHERS", MsgModifierPcNeg))
        ,("airforce_intel_to_others"        , ("MODIFIER_AIRFORCE_INTEL_TO_OTHERS", MsgModifierPcNeg))
        ,("intel_network_gain"              , ("MODIFIER_INTEL_NETWORK_GAIN", MsgModifierColourPos))
        ,("intel_network_gain_factor"       , ("MODIFIER_INTEL_NETWORK_GAIN_FACTOR", MsgModifierPcPosReduced))
        ,("subversive_activites_upkeep"     , ("MODIFIER_SUBVERSIVE_ACTIVITES_UPKEEP", MsgModifierPcNegReduced))
        ,("diplomatic_pressure_mission_factor" , ("MODIFIER_DIPLOMATIC_PRESSURE_MISSION_FACTOR", MsgModifierPcPosReduced))
        ,("control_trade_mission_factor"    , ("MODIFIER_CONTROL_TRADE_MISSION_FACTOR", MsgModifierPcPosReduced))
        ,("boost_ideology_mission_factor"   , ("MODIFIER_BOOST_IDEOLOGY_MISSION_FACTOR", MsgModifierPcPosReduced))
        ,("propaganda_mission_factor"       , ("MODIFIER_PROPAGANDA_MISSION_FACTOR", MsgModifierPcPosReduced))
        ,("crypto_strength"                 , ("MODIFIER_CRYPTO_STRENGTH", MsgModifierColourPos))
        ,("decryption_power_factor"         , ("MODIFIER_DECRYPTION_POWER_FACTOR", MsgModifierPcPosReduced))
        ,("civilian_intel_to_others"        , ("MODIFIER_CIVILIAN_INTEL_TO_OTHERS", MsgModifierPcNeg))
        ,("foreign_subversive_activites"    , ("MODIFIER_FOREIGN_SUBVERSIVE_ACTIVITIES", MsgModifierPcNegReduced))

            -- Operatives
        ,("own_operative_detection_chance_factor" , ("MODIFIER_OWN_OPERATIVE_DETECTION_CHANCE_FACTOR", MsgModifierPcNegReduced))
        ,("enemy_operative_detection_chance_factor" , ("MODIFIER_ENEMY_OPERATIVE_DETECTION_CHANCE_FACTOR", MsgModifierPcPosReduced))
        ,("operative_slot"                  , ("MODIFIER_OPERATIVE_SLOT", MsgModifierColourPos))

            -- AI
        ,("ai_badass_factor"                , ("MODIFIER_AI_BADASS_FACTOR", MsgModifierPcReduced))
        ,("ai_join_ally_desire_factor"      , ("MODIFIER_AI_JOIN_ALLY_DESIRE_FACTOR", MsgModifierSign))
        ,("ai_focus_aggressive_factor"      , ("MODIFIER_AI_FOCUS_AGGRESSIVE_FACTOR", MsgModifierPcReducedSign))
        ,("ai_focus_defense_factor"         , ("MODIFIER_AI_FOCUS_DEFENSE_FACTOR", MsgModifierPcReducedSign))
        ,("ai_focus_military_advancements_factor" , ("MODIFIER_AI_FOCUS_MILITARY_ADVANCEMENTS_FACTOR", MsgModifierPcReducedSign))
        ,("ai_focus_peaceful_factor"        , ("MODIFIER_AI_FOCUS_PEACEFUL_FACTOR", MsgModifierPcReducedSign))
        ,("ai_call_ally_desire_factor"      , ("MODIFIER_AI_GET_ALLY_DESIRE_FACTOR", MsgModifierSign))
        ,("ai_get_ally_desire_factor"       , ("MODIFIER_AI_GET_ALLY_DESIRE_FACTOR", MsgModifierSign))

            -- Unit Leaders
        ,("military_leader_cost_factor"     , ("MODIFIER_MILITARY_LEADER_COST_FACTOR", MsgModifierPcNegReduced))

            -- General Combat
        ,("offence"                         , ("MODIFIER_OFFENCE", MsgModifierPcPosReduced))
        ,("defence"                         , ("MODIFIER_DEFENCE", MsgModifierPcPosReduced))

            -- Land Combat
        ,("acclimatization_cold_climate_gain_factor", ("MODIFIER_ACCLIMATIZATION_COLD_CLIMATE_GAIN_FACTOR", MsgModifierPcPosReduced))
        ,("acclimatization_hot_climate_gain_factor", ("MODIFIER_ACCLIMATIZATION_HOT_CLIMATE_GAIN_FACTOR", MsgModifierPcPosReduced))
        ,("army_attack_factor"              , ("MODIFIERS_ARMY_ATTACK_FACTOR", MsgModifierPcPosReduced))
        ,("army_core_attack_factor"         , ("MODIFIERS_ARMY_CORE_ATTACK_FACTOR", MsgModifierPcPosReduced))
        ,("army_defence_factor"             , ("MODIFIERS_ARMY_DEFENCE_FACTOR", MsgModifierPcPosReduced))
        ,("army_core_defence_factor"        , ("MODIFIERS_ARMY_CORE_DEFENCE_FACTOR", MsgModifierPcPosReduced))
        ,("army_infantry_attack_factor"     , ("MODIFIERS_ARMY_INFANTRY_ATTACK_FACTOR", MsgModifierPcPosReduced))
        ,("army_infantry_defence_factor"    , ("MODIFIERS_ARMY_INFANTRY_DEFENCE_FACTOR", MsgModifierPcPosReduced))
        ,("army_armor_attack_factor"        , ("MODIFIERS_ARMY_ARMOR_ATTACK_FACTOR", MsgModifierPcPosReduced))
        ,("army_armor_defence_factor"       , ("MODIFIERS_ARMY_ARMOR_DEFENCE_FACTOR", MsgModifierPcPosReduced))
        ,("army_army_artillery_attack_factor" , ("MODIFIERS_ARMY_ARTILLERY_ATTACK_FACTOR", MsgModifierPcPosReduced))
        ,("army_artillery_defence_factor"   , ("MODIFIERS_ARMY_ARTILLERY_DEFENCE_FACTOR", MsgModifierPcPosReduced))
        ,("special_forces_attack_factor"    , ("MODIFIER_SPECIAL_FORCES_ATTACK_FACTOR", MsgModifierPcPosReduced))
        ,("special_forces_defence_factor"   , ("MODIFIER_SPECIAL_FORCES_DEFENCE_FACTOR", MsgModifierPcPosReduced))
        ,("motorized_attack_factor"         , ("MODIFIER_MOTORIZED_ATTACK_FACTOR", MsgModifierPcPosReduced))
        ,("motorized_defence_factor"        , ("MODIFIER_MOTORIZED_DEFENCE_FACTOR", MsgModifierPcPosReduced))
        ,("mechanized_attack_factor"        , ("MODIFIER_MECHANIZED_ATTACK_FACTOR", MsgModifierPcPosReduced))
        ,("mechanized_defence_factor"       , ("MODIFIER_MECHANIZED_DEFENCE_FACTOR", MsgModifierPcPosReduced))
        ,("cavalry_attack_factor"           , ("MODIFIER_CAVALRY_ATTACK_FACTOR", MsgModifierPcPosReduced))
        ,("cavalry_defence_factor"          , ("MODIFIER_CAVALRY_DEFENCE_FACTOR", MsgModifierPcPosReduced))
        ,("army_speed_factor"               , ("MODIFIER_ARMY_SPEED_FACTOR", MsgModifierPcPosReduced))
        ,("army_morale_factor"              , ("MODIFIER_ARMY_MORALE_FACTOR", MsgModifierPcPosReduced))
        ,("army_org"                        , ("MODIFIER_ARMY_ORG", MsgModifierColourPos))
        ,("army_org_factor"                 , ("MODIFIER_ARMY_ORG_FACTOR", MsgModifierPcPosReduced))
        ,("breakthrough_factor"             , ("MODIFIER_BREAKTHROUGH", MsgModifierPcPosReduced))
        ,("combat_width_factor"             , ("MODIFIER_COMBAT_WIDTH_FACTOR", MsgModifierPcNegReduced))
        ,("max_dig_in"                      , ("MODIFIER_MAX_DIG_IN", MsgModifierColourPos))
        ,("max_dig_in_factor"               , ("MODIFIER_MAX_DIG_IN_FACTOR", MsgModifierPcPosReduced))
        ,("land_night_attack"               , ("MODIFIER_LAND_NIGHT_ATTACK", MsgModifierPcPosReduced))
        ,("max_planning"                    , ("MODIFIER_MAX_PLANNING", MsgModifierPcPosReduced))
        ,("recon_factor"                    , ("MODIFIER_RECON_FACTOR", MsgModifierPcPosReduced))
        ,("special_forces_cap"              , ("MODIFIER_SPECIAL_FORCES_CAP", MsgModifierPcPosReduced))
        ,("terrain_penalty_reduction"       , ("MODIFIER_TERRAIN_PENALTY_REDUCTION", MsgModifierPcPosReduced))
        ,("planning_speed"                  , ("MODIFIER_PLANNING_SPEED", MsgModifierPcPosReduced))

            -- naval invasions
        ,("amphibious_invasion"             , ("MODIFIER_AMPHIBIOUS_INVASION", MsgModifierPcPosReduced))
        ,("amphibious_invasion_defence"     , ("MODIFIER_NAVAL_INVASION_DEFENSE", MsgModifierPcPosReduced))
        ,("invasion_preparation"            , ("MODIFIER_NAVAL_INVASION_PREPARATION", MsgModifierPcNegReduced))

            -- Naval combat
        ,("naval_coordination"              , ("MODIFIER_NAVAL_COORDINATION", MsgModifierPcPosReduced))
        ,("naval_hit_chance"                , ("MODIFIER_NAVAL_HIT_CHANCE", MsgModifierPcPosReduced))
        ,("ships_at_battle_start"           , ("MODIFIER_SHIPS_AT_BATTLE_START_FACTOR", MsgModifierPcPosReduced))
        ,("spotting_chance"                 , ("MODIFIER_SPOTTING_CHANCE", MsgModifierPcPosReduced))

            -- carriers and their planes
        ,("sortie_efficiency"               , ("MODIFIER_STAT_CARRIER_SORTIE_EFFICIENCY", MsgModifierPcPosReduced))

            -- Air combat
        ,("air_accidents_factor"            , ("MODIFIER_AIR_ACCIDENTS_FACTOR", MsgModifierPcNegReduced))
        ,("air_ace_generation_chance_factor" , ("MODIFIER_AIR_ACE_GENERATION_CHANCE_FACTOR", MsgModifierPcPosReduced))
        ,("air_agility"                     , ("MODIFIER_AIR_AGILITY", MsgModifierPcPosReduced))
        ,("air_attack"                      , ("MODIFIER_AIR_ATTACK", MsgModifierPcPosReduced))
        ,("air_attack_factor"               , ("MODIFIER_AIR_ATTACK_FACTOR", MsgModifierPcPosReduced))
        ,("air_defence_factor"              , ("MODIFIER_AIR_DEFENCE_FACTOR", MsgModifierPcPosReduced))
        ,("air_close_air_support_agility_factor" , ("MODIFIER_CAS_AGILITY_FACTOR", MsgModifierPcPosReduced))
        ,("air_close_air_support_attack_factor" , ("MODIFIER_CAS_ATTACK_FACTOR", MsgModifierPcPosReduced))
        ,("air_close_air_support_defence_factor" , ("MODIFIER_CAS_DEFENCE_FACTOR", MsgModifierPcPosReduced))
        ,("air_strategic_bomber_agility_factor" , ("MODIFIER_STRATEGIC_BOMBER_AGILITY_FACTOR", MsgModifierPcPosReduced))
        ,("air_strategic_bomber_attack_factor" , ("MODIFIER_STRATEGIC_BOMBER_ATTACK_FACTOR", MsgModifierPcPosReduced))
        ,("air_strategic_bomber_defence_factor" , ("MODIFIER_STRATEGIC_BOMBER_DEFENCE_FACTOR", MsgModifierPcPosReduced))
        ,("air_bombing_targetting"          , ("MODIFIER_AIR_BOMBING_TARGETTING", MsgModifierPcPosReduced))
        ,("air_cas_present_factor"          , ("MODIFIER_AIR_CAS_PRESENT_FACTOR", MsgModifierPcPosReduced))
        ,("air_night_penalty"               , ("MODIFIER_AIR_NIGHT_PENALTY", MsgModifierPcNegReduced))
        ,("air_range_factor"                , ("MODIFIER_AIR_RANGE_FACTOR", MsgModifierPcPosReduced))
        ,("air_strategic_bomber_bombing_factor" , ("MODIFIER_STRATEGIC_BOMBER_BOMBING_FACTOR", MsgModifierPcPosReduced))
        ,("air_weather_penalty"             , ("MODIFIER_AIR_WEATHER_PENALTY", MsgModifierPcNegReduced))
        ,("army_bonus_air_superiority_factor" , ("MODIFIER_ARMY_BONUS_AIR_SUPERIORITY_FACTOR", MsgModifierPcPosReduced))

            -- targeted

        -- State Scope
        ,("army_speed_factor_for_controller" , ("MODIFIER_ARMY_SPEED_FACTOR_FOR_CONTROLLER", MsgModifierPcPosReduced))
        ,("compliance_gain"                 , ("MODIFIER_COMPLIANCE_GAIN_ADD", MsgModifierPcPos))
        ,("compliance_growth"               , ("MODIFIER_COMPLIANCE_GROWTH", MsgModifierPcPosReduced))
        ,("local_factories"                 , ("MODIFIER_LOCAL_FACTORIES", MsgModifierPcPosReduced))
        ,("local_intel_to_enemies"          , ("MODIFIER_LOCAL_INTEL_TO_ENEMIES", MsgModifierPcNegReduced))
        ,("local_non_core_manpower"         , ("MODIFIER_LOCAL_NON_CORE_MANPOWER", MsgModifierPcPosReduced))
        ,("local_resources_factor"          , ("MODIFIER_LOCAL_RESOURCES_FACTOR", MsgModifierPcPosReduced))
        ,("non_core_manpower"               , ("MODIFIER_GLOBAL_NON_CORE_MANPOWER", MsgModifierPcPosReduced))
        ,("mobilization_speed"              , ("MODIFIER_MOBILIZATION_SPEED", MsgModifierPcPosReduced))
        ,("non_core_manpower"               , ("MODIFIER_GLOBAL_NON_CORE_MANPOWER", MsgModifierPcPosReduced))
        --,("recruitable_population_factor"   , ("MODIFIER_RECRUITABLE_POPULATION_FACTOR", MsgModifierPcReduced))
        ,("resistance_damage_to_garrison"   , ("MODIFIER_RESISTANCE_DAMAGE_TO_GARRISONS", MsgModifierPcNegReduced))
        ,("resistance_decay"                , ("MODIFIER_RESISTANCE_DECAY", MsgModifierPcPosReduced))
        ,("resistance_garrison_penetration_chance" , ("MODIFIER_RESISTANCE_GARRISON_PENETRATION_CHANCE", MsgModifierPcNegReduced))
        ,("resistance_growth"               , ("MODIFIER_RESISTANCE_GROWTH", MsgModifierPcNegReduced))
        ,("resistance_target"               , ("MODIFIER_RESISTANCE_TARGET", MsgModifierPcNegReduced))
        ,("starting_compliance"             , ("MODIFIER_COMPLIANCE_STARTING_VALUE", MsgModifierPcPosReduced))

        -- Unit Leader Scope
        ,("army_leader_cost_factor"         , ("MODIFIER_ARMY_LEADER_COST_FACTOR", MsgModifierPcNegReduced))
        ,("army_leader_start_level"         , ("MODIFIER_ARMY_LEADER_START_LEVEL", MsgModifierColourPos))
        ,("army_leader_start_attack_level"  , ("MODIFIER_ARMY_LEADER_START_ATTACK_LEVEL", MsgModifierColourPos))
        ,("army_leader_start_defense_level" , ("MODIFIER_ARMY_LEADER_START_DEFENSE_LEVEL", MsgModifierColourPos))
        ,("army_leader_start_logistics_level" , ("MODIFIER_ARMY_LEADER_START_LOGISTICS_LEVEL", MsgModifierColourPos))
        ,("army_leader_start_planning_level" , ("MODIFIER_ARMY_LEADER_START_PLANNING_LEVEL", MsgModifierColourPos))
        ,("experience_gain_factor"          , ("MODIFIER_XP_GAIN_FACTOR", MsgModifierPcPosReduced))
        ,("promote_cost_factor"             , ("MODIFIER_UNIT_LEADER_PROMOTE_COST_FACTOR", MsgModifierPcNegReduced))
        ,("reassignment_duration_factor"    , ("MODIFIER_REASSIGNMENT_DURATION_FACTOR", MsgModifierPcNegReduced))
        ,("skill_bonus_factor"              , ("MODIFIER_UNIT_LEADER_SKILL_BONUS_FACTOR", MsgModifierPcPosReduced))
        ,("wounded_chance_factor"           , ("MODIFIER_WOUNDED_CHANCE_FACTOR", MsgModifierPcNegReduced))
        ,("shore_bombardment_bonus"         , ("MODIFIER_SHORE_BOMBARDMENT", MsgModifierPcPosReduced))

        -- targeted
        ,("extra_trade_to_target_factor"    , ("MODIFIER_TRADE_TO_TARGET_FACTOR", MsgModifierPcPosReduced))
        ,("trade_cost_for_target_factor"    , ("MODIFIER_TRADE_COST_TO_TARGET_FACTOR", MsgModifierPcNegReduced))
        ,("attack_bonus_against"            , ("MODIFIER_ATTACK_BONUS_AGAINST_A_COUNTRY", MsgModifierPcPosReduced))
        ,("attack_bonus_against_cores"      , ("MODIFIER_ATTACK_BONUS_AGAINST_A_COUNTRY_ON_ITS_CORES", MsgModifierPcPosReduced))
        ,("cic_to_target_factor"            , ("MODIFIER_CIC_TO_TARGET_FACTOR", MsgModifierPcNegReduced))
        ,("mic_to_target_factor"            , ("MODIFIER_MIC_TO_TARGET_FACTOR", MsgModifierPcNegReduced))
        ,("targeted_legitimacy_daily"       , ("MODIFIER_TARGETED_LEGITIMACY_DAILY", MsgModifierColourPos))
        ,("defense_bonus_against"           , ("MODIFIER_DEFENSE_BONUS_AGAINST_A_COUNTRY", MsgModifierPcPosReduced))

        -- equipment/stats
        ,("build_cost_ic"           , ("STAT_COMMON_BUILD_COST_IC", MsgModifierPcNegReduced))
        ,("reliability"             , ("STAT_COMMON_RELIABILITY", MsgModifierPcPosReduced))
        ,("defense"                 , ("STAT_ARMY_DEFENSE", MsgModifierPcPosReduced))
        ,("breakthrough"            , ("STAT_ARMY_BREAKTHROUGH", MsgModifierPcPosReduced))
        ]

-------------------------------------------------
-- Handler for add_dynamic_modifier --
-------------------------------------------------
data AddDynamicModifier = AddDynamicModifier
    { adm_modifier :: Text
    , adm_scope :: Either Text (Text, Text)
    , adm_days :: Maybe Double
    }
newADM :: AddDynamicModifier
newADM = AddDynamicModifier undefined (Left "THIS") Nothing
addDynamicModifier :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
addDynamicModifier stmt@[pdx| %_ = @scr |] =
    pp_adm (foldl' addLine newADM scr)
    where
        addLine adm [pdx| modifier = $mod |] = adm { adm_modifier = mod }
        addLine adm [pdx| scope = $tag |] = adm { adm_scope = Left tag }
        addLine adm [pdx| scope = $vartag:$var |] = adm { adm_scope = Right (vartag, var) }
        addLine adm [pdx| days = !amt |] = adm { adm_days = Just amt }
        addLine adm stmt = trace ("Unknown in add_dynamic_modifier: " ++ show stmt) adm
        pp_adm adm = do
            let days = maybe "" formatDays (adm_days adm)
            mmod <- HM.lookup (adm_modifier adm) <$> getDynamicModifiers
            thescope <- getCurrentScope
            dynflag <- case thescope of
                Just HOI4Country -> eflag (Just HOI4Country) $ adm_scope adm
                Just HOI4ScopeState -> eGetState $ adm_scope adm
                Just HOI4From -> return $ Just "FROM"
                _ -> return $ Just "<!-- check script -->"
            let dynflagd = fromMaybe "<!-- check script -->" dynflag
            case mmod of
                Just mod -> withCurrentIndent $ \i -> do
                    effect <- fold <$> indentUp (traverse (modifierMSG False) (dmodEffects mod))
                    trigger <- indentUp $ ppMany (dmodEnable mod)
                    let name = dmodLocName mod
                        locName = maybe ("<tt>" <> adm_modifier adm <> "</tt>") (Doc.doc2text . iquotes) name
                    return $ ((i, MsgAddDynamicModifier locName dynflagd days) : effect) ++ (if null trigger then [] else (i+1, MsgLimit) : trigger)
                Nothing -> trace ("add_dynamic_modifier: Modifier " ++ T.unpack (adm_modifier adm) ++ " not found") $ preStatement stmt
addDynamicModifier stmt = trace ("Not handled in addDynamicModifier: " ++ show stmt) $ preStatement stmt

removeDynamicModifier :: (HOI4Info g, Monad m) => StatementHandler g m
removeDynamicModifier stmt@[pdx| %_ = $txt |] = withLocAtom MsgRemoveDynamicMod stmt
removeDynamicModifier stmt@[pdx| %_ = @dyn |] = do
    case dyn of
        [stmtd@[pdx| %_ = $txt |]] ->  withLocAtom MsgRemoveDynamicMod stmtd
        _-> preStatement stmt
removeDynamicModifier stmt = preStatement stmt

flagTextMaybe :: (HOI4Info g, Monad m) => Text -> PPT g m (Maybe Text)
flagTextMaybe txt = eflag (Just HOI4Country) (Left txt)

hasDynamicModifier :: (HOI4Info g, Monad m) => StatementHandler g m
hasDynamicModifier stmt@[pdx| %_ = @dyn |] = if length dyn == 2
    then textAtom "scope" "modifier" MsgHasDynamicModFlag flagTextMaybe stmt
    else case dyn of
        [stmtd@[pdx| %_ = $txt |]] ->  withLocAtom MsgHasDynamicMod stmtd
        _-> preStatement stmt
hasDynamicModifier stmt = preStatement stmt

----------------
-- characters --
----------------

addFieldMarshalRole :: (Monad m, HOI4Info g) => (Text -> ScriptMessage) -> StatementHandler g m
addFieldMarshalRole msg stmt@[pdx| %_ = @scr |] = do
        let (name, _) = extractStmt (matchLhsText "character") scr
        nameloc <- case name of
            Just [pdx| character = ?id |] -> getCharacterName id
            _ -> case extractStmt (matchLhsText "name") scr of
                (Just [pdx| name = ?id |],_) -> getCharacterName id
                _-> return ""
        msgToPP $ msg nameloc
addFieldMarshalRole _ stmt = preStatement stmt

setCharacterName :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
setCharacterName stmt@[pdx| %_ = ?txt |] = withLocAtom MsgSetCharacterName stmt
setCharacterName stmt@[pdx| %_ = @scr |] = case scr of
    [[pdx| $who = $name |]] -> do
        whochar <- getCharacterName who
        nameloc <- getGameL10n name
        msgToPP $ MsgSetCharacterNameType whochar nameloc
    _ -> preStatement stmt
setCharacterName stmt = preStatement stmt

removeAdvisorRole :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
removeAdvisorRole stmt@[pdx| %_ = @scr |] =
    if length scr == 2
    then textAtom "character" "slot" MsgRemoveAdvisorRole getGameL10nIfPresent stmt
    else do
        let (mslot,_) = extractStmt (matchLhsText "slot") scr
        slot <- case mslot of
            Just [pdx| %_ = $slottype |] -> getGameL10n slottype
            _-> return "<!-- Check Script -->"
        msgToPP $ MsgRemoveAdvisorRole "" "" slot
removeAdvisorRole stmt = preStatement stmt

withCharacter :: (HOI4Info g, Monad m) => (Text -> ScriptMessage) -> StatementHandler g m
withCharacter msg stmt@[pdx| %_ = ?txt |] = do
    chaname <- getCharacterName txt
    msgToPP $ msg chaname
withCharacter _ stmt = preStatement stmt

addAdvisorRole :: (Monad m, HOI4Info g) => StatementHandler g m
addAdvisorRole stmt@[pdx| %_ = @scr |] = do
        let (name, rest) = extractStmt (matchLhsText "character") scr
            (advisor, rest') = extractStmt (matchLhsText "advisor") rest
            (activate, _) = extractStmt (matchLhsText "activate") rest'
        activate <- maybe (return False) (\case
            [pdx| %_ = yes |] -> return True
            _-> return False) activate
        nameloc <- case name of
            Just [pdx| character = $id |] -> getCharacterName id
            _ -> return ""
        case advisor of
            Just advisorj -> do
                (slotloc, traitmsg) <- parseAdvisor advisorj
                basemsg <- msgToPP $ MsgAddAdvisorRole nameloc slotloc
                (if activate
                then do
                    hiremsg <- msgToPP MsgAndIsHired
                    return $ basemsg ++ traitmsg ++ hiremsg
                else return $ basemsg ++ traitmsg)
            _-> preStatement stmt
addAdvisorRole stmt = preStatement stmt

parseAdvisor :: (Monad m, HOI4Info g) =>
    GenericStatement -> PPT g m (Text, [IndentedMessage])
parseAdvisor stmt@[pdx| %_ = @scr |] = do
    let (slot, rest) = extractStmt (matchLhsText "slot") scr
        (traits, modrest) = extractStmt (matchLhsText "traits") rest
        (modifier, bonusrest) = extractStmt (matchLhsText "modifier") modrest
        (resbonus, _) = extractStmt (matchLhsText "research_bonus") bonusrest
    modmsg <- maybe (return []) (indentUp . handleModifier) modifier
    resmsg <- maybe (return []) (indentUp . handleResearchBonus) resbonus
    traitmsg <- case traits of
        Just [pdx| %_ = @arr |] -> do
            let traitbare = mapMaybe getbaretraits arr
            concatMapM getLeaderTraits traitbare
        _-> return []
    slotloc <- maybe (return "") (\case
        [pdx| %_ = $slottype|] -> getGameL10n slottype
        _->return "<!-- Check Script -->") slot

    return (slotloc, traitmsg ++ modmsg ++ resmsg)
parseAdvisor stmt = return ("<!-- Check Script -->", [])

addLeaderRole :: (Monad m, HOI4Info g) => StatementHandler g m
addLeaderRole stmt@[pdx| %_ = @scr |] = do
        let (name, rest) = extractStmt (matchLhsText "character") scr
            (leader, rest') = extractStmt (matchLhsText "country_leader") rest
            (promote, _) = extractStmt (matchLhsText "promote_leader") rest'
        promoted <- maybe (return False) (\case
            [pdx| %_ = yes |] -> return True
            _-> return False) promote
        nameloc <- case name of
            Just [pdx| character = $id |] -> getCharacterName id
            _ -> return ""
        case leader of
            Just leaderj -> do
                (ideoloc, traitmsg) <- parseLeader leaderj
                basemsg <- if promoted
                    then msgToPP $ MsgAddCountryLeaderRolePromoted nameloc ideoloc
                    else msgToPP $ MsgAddCountryLeaderRole nameloc ideoloc
                return $ basemsg ++ traitmsg
            _-> preStatement stmt
addLeaderRole stmt = preStatement stmt

parseLeader :: (Monad m, HOI4Info g) =>
    GenericStatement -> PPT g m (Text, [IndentedMessage])
parseLeader stmt@[pdx| %_ = @scr |] = do
    let (ideo, rest) = extractStmt (matchLhsText "ideology") scr
        (traits, _) = extractStmt (matchLhsText "traits") rest
    traitmsg <- case traits of
        Just [pdx| %_ = @arr |] -> do
            let traitbare = mapMaybe getbaretraits arr
            concatMapM ppHt traitbare
        _-> return []
    ideoloc <- maybe (return "") (\case
        [pdx| %_ = $ideotype|] -> do
            subideos <- getIdeology
            case HM.lookup ideotype subideos of
                Just ideo -> getGameL10n ideo
                _-> return "<!-- Check Script -->"
        _->return "<!-- Check Script -->") ideo
    return (ideoloc, traitmsg)
parseLeader stmt = return ("<!-- Check Script -->", [])


createLeader :: (Monad m, HOI4Info g) => StatementHandler g m
createLeader stmt@[pdx| %_ = @scr |] = do
        let (name, rest) = extractStmt (matchLhsText "name") scr
            (ideo, rest') = extractStmt (matchLhsText "ideology") rest
            (traits, _) = extractStmt (matchLhsText "traits") rest'
        nameloc <- case name of
            Just [pdx| %_ = ?id |] -> getCharacterName id
            _ -> return ""
        traitmsg <- case traits of
            Just [pdx| %_ = @arr |] -> do
                let traitbare = mapMaybe getbaretraits arr
                concatMapM ppHt traitbare
            _-> return []
        ideoloc <- maybe (return "") (\case
            [pdx| %_ = $ideotype|] -> do
                subideos <- getIdeology
                case HM.lookup ideotype subideos of
                    Just ideo -> getGameL10n ideo
                    _-> return "<!-- Check Script -->"
            _-> return "<!-- Check Script -->") ideo
        basemsg <- msgToPP $ MsgAddCountryLeaderRole nameloc ideoloc
        return $ basemsg ++ traitmsg
createLeader stmt = preStatement stmt

promoteCharacter :: (Monad m, HOI4Info g) => StatementHandler g m
promoteCharacter stmt@[pdx| %_ = @scr |] =
    ppPC (parseTA "character" "ideology" scr)
    where
        ppPC ta = case (ta_what ta, ta_atom ta) of
            (Just what, Just atom) -> promomessage what atom stmt
            (_, Just atom) -> promomessage "" atom stmt
            _ -> preStatement stmt
promoteCharacter stmt@[pdx| %_ = $txt |]
    | txt == "yes" = msgToPP $ MsgPromoteCharacter ""
    | otherwise = do
        chas <- getCharacters
        subideos <- getIdeology
        case HM.lookup txt subideos of
            Just ideo -> promomessage "" txt stmt
            _-> case HM.lookup txt chas of
                Just ccha -> promomessage txt "" stmt
                _-> preStatement stmt
promoteCharacter stmt = preStatement stmt

promomessage :: (Monad m, HOI4Info g) => Text
    -> Text-> StatementHandler g m
promomessage what atom stmt = do
    chas <- getCharacters
    subideos <- getIdeology
    ideoloc <- maybe (return "") getGameL10n (HM.lookup atom subideos)
    case HM.lookup what chas of
        Just ccha -> do
            let nameloc = chaName ccha
                ideolocd = if T.null ideoloc
                    then fromMaybe "" (cha_leader_ideology ccha)
                    else ideoloc
            traitmsg <- case chaLeaderTraits ccha of
                Just trts -> do
                    concatMapM ppHt trts
                _-> return []
            basemsg <- if not (T.null ideoloc)
                then msgToPP $ MsgAddCountryLeaderRolePromoted nameloc ideolocd
                else msgToPP $ MsgPromoteCharacter nameloc
            modmsg <- maybe (return []) (indentUp .handleModifier) (cha_adv_modifier ccha)
            resmsg <- maybe (return []) (indentUp .handleResearchBonus) (cha_adv_research_bonus ccha)
            return $ basemsg ++ traitmsg ++ modmsg ++ resmsg
        _-> if not (T.null what)
            then preStatement stmt
            else msgToPP $ MsgAddCountryLeaderRolePromoted "" ideoloc

ppHt :: (Monad m, HOI4Info g) => Text -> PPT g m IndentedMessages
ppHt trait = do
    traitloc <- getGameL10n trait
    namemsg <- indentUp $ plainMsg' ("'''" <> traitloc <> "'''")
    traitmsg' <- indentUp $ getLeaderTraits trait
    return $ namemsg : traitmsg'

getbaretraits :: GenericStatement -> Maybe Text
getbaretraits (StatementBare (GenericLhs trait [])) = Just trait
getbaretraits stmt = Nothing

getCharacterName :: (Monad m, HOI4Info g) =>
    Text -> PPT g m Text
getCharacterName idn = do
    characters <- getCharacters
    case HM.lookup idn characters of
        Just charid -> return $ chaName charid
        _ -> getGameL10n idn

-- operatives

data CreateOperative = CreateOperative
        {   co_bypass_recruitment :: Bool
        ,   co_name :: Text
        ,   co_traits :: Maybe [Text]
        ,   co_nationalities :: Maybe [Text]
        ,   co_available_to_spy_master :: Bool
        }

newCO :: CreateOperative
newCO = CreateOperative undefined "" Nothing Nothing False

createOperativeLeader :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
createOperativeLeader stmt@[pdx| %_ = @scr |]
    = ppCO (foldl' addLine newCO scr)
    where
        addLine :: CreateOperative -> GenericStatement -> CreateOperative
        addLine co [pdx| bypass_recruitment = %rhs |]
            | GenericRhs "yes" [] <- rhs = co { co_bypass_recruitment = True }
            | GenericRhs "no" [] <- rhs = co { co_bypass_recruitment = False }
        addLine co [pdx| name = ?txt |] = co {co_name = txt}
        addLine co [pdx| traits = @arr |] =
            let traits = mapMaybe getbaretraits arr
            in co {co_traits = Just traits}
        addLine co [pdx| nationalities = @arr |] =
            let nats = mapMaybe getbaretraits arr
            in co {co_nationalities = Just nats}
        addLine co [pdx| available_to_spy_master = %rhs |]
            | GenericRhs "yes" [] <- rhs = co { co_available_to_spy_master = True }
            | otherwise = co
        addLine co stmt = co

        ppCO co = do
            natmsg <- case co_nationalities co of
                    Just nats -> do
                        flagged <- mapM (flagText (Just HOI4Country)) nats
                        return $ T.intercalate ", " flagged
                    _ -> return ""
            basemsg <- msgToPP $ MsgCreateOperativeLeader (co_name co) natmsg (co_bypass_recruitment co) (co_available_to_spy_master co)
            traitsmsg <- case co_traits co of
                Just traits -> concatMapM (\t -> do
                    namemsg <- indentUp $ plainMsg' ("'''" <> t <> "'''")
                    traitmsg <- indentUp $ getUnitTraits t
                    return $ namemsg : traitmsg
                    ) traits
                _ -> return []
            return $ basemsg ++ traitsmsg
createOperativeLeader stmt = preStatement stmt

------------
-- traits --
------------
data HandleTrait = HandleTrait
    { ht_trait :: Text
    , ht_character :: Maybe Text
    , ht_ideology :: Maybe Text
    }

newHT :: HandleTrait
newHT = HandleTrait undefined Nothing Nothing

handleTrait :: forall g m. (HOI4Info g, Monad m) => Bool -> StatementHandler g m
handleTrait addremove stmt@[pdx| %_ = @scr |] =
    pp_ht addremove (foldl' addLine newHT scr)
    where
        addLine ht [pdx| trait = $txt |] = ht { ht_trait = txt }
        addLine ht [pdx| character = $txt |] = ht { ht_character = Just txt }
        addLine ht [pdx| ideology = $txt |] = ht { ht_ideology = Just txt }
        addLine ht [pdx| slot = %_ |] = ht
        addLine ht stmt = trace ("Unknown in handleTrait: " ++ show stmt) ht
        pp_ht addremove ht = do
            traitloc <- getGameL10n $ ht_trait ht
            namemsg <- indentUp $ plainMsg' ("'''" <> traitloc <> "'''")
            traitmsg' <- indentUp $ getLeaderTraits (ht_trait ht)
            let traitmsg = namemsg : traitmsg'
            case (ht_character ht, ht_ideology ht) of
                (Just char, Just ideo) -> do
                    charloc <- getCharacterName char
                    ideoloc <- getGameL10n ideo
                    baseMsg <- msgToPP $ MsgTraitCharIdeo charloc addremove ideoloc
                    return $ baseMsg ++ traitmsg
                (Just char, _) -> do
                    charloc <- getCharacterName char
                    baseMsg <- msgToPP $ MsgTraitChar charloc addremove
                    return $ baseMsg ++ traitmsg
                (_, Just ideo) -> do
                    ideoloc <- getGameL10n ideo
                    baseMsg <- msgToPP $ MsgTraitIdeo addremove ideoloc
                    return $ baseMsg ++ traitmsg
                _ -> do
                    baseMsg <- msgToPP $ MsgTrait addremove
                    return $ baseMsg ++ traitmsg
handleTrait _ stmt = preStatement stmt

addRemoveLeaderTrait :: (Monad m, HOI4Info g) => ScriptMessage -> StatementHandler g m
addRemoveLeaderTrait msg stmt@[pdx| %_ = $trait |] = do
    traitloc <- getGameL10n trait
    namemsg <- indentUp $ plainMsg' ("'''" <> traitloc <> "'''")
    traitmsg' <- indentUp $ getLeaderTraits trait
    let traitmsg = namemsg : traitmsg'
    baseMsg <- msgToPP msg
    return $ baseMsg ++ traitmsg
addRemoveLeaderTrait _ stmt = preStatement stmt

addRemoveUnitTrait :: (Monad m, HOI4Info g) => ScriptMessage -> StatementHandler g m
addRemoveUnitTrait msg stmt@[pdx| %_ = $trait |] = do
    traitloc <- getGameL10n trait
    namemsg <- indentUp $ plainMsg' ("'''" <> traitloc <> "'''")
    traitmsg' <- indentUp $ getUnitTraits trait
    let traitmsg = namemsg : traitmsg'
    baseMsg <- msgToPP msg
    return $ baseMsg ++ traitmsg
addRemoveUnitTrait _ stmt = preStatement stmt

data AddTimedTrait = AddTimedTrait
    { adt_trait :: Text
    , adt_days :: Maybe Double
    , adt_daysvar :: Maybe Text
    }

newADT :: AddTimedTrait
newADT = AddTimedTrait undefined Nothing Nothing
addTimedTrait ::  (Monad m, HOI4Info g) => GenericStatement -> PPT g m IndentedMessages
addTimedTrait stmt@[pdx| %_ = @scr |] =
    ppADT (foldl' addLine newADT scr)

    where
        addLine adt [pdx| trait = $txt |] = adt { adt_trait = txt }
        addLine adt [pdx| days = !num |] = adt { adt_days = Just num }
        addLine adt [pdx| days = $txt |] = adt { adt_daysvar = Just txt }
        addLine adt stmt = trace ("Unknown in addTimedTrait: " ++ show stmt) adt
        ppADT adt = do
            traitloc <- getGameL10n (adt_trait adt)
            traitmsg <- getUnitTraits (adt_trait adt)
            baseMsg <- case (adt_days adt, adt_daysvar adt) of
                (Just days,_)-> msgToPP $ MsgAddTimedUnitLeaderTrait traitloc days
                (_, Just daysvar)->msgToPP $ MsgAddTimedUnitLeaderTraitVar traitloc daysvar
                _-> msgToPP $ MsgAddTimedUnitLeaderTraitVar traitloc "<!-- Check Script -->"
            return $ baseMsg ++ traitmsg
addTimedTrait stmt = preStatement stmt


data SwapTrait = SwapTrait
    { st_add :: Text
    , st_remove :: Text
    }

newST :: SwapTrait
newST = SwapTrait undefined undefined
swapLeaderTrait ::  (Monad m, HOI4Info g) => GenericStatement -> PPT g m IndentedMessages
swapLeaderTrait stmt@[pdx| %_ = @scr |] =
    ppST (foldl' addLine newST scr)

    where
        addLine st [pdx| add = $txt |] = st { st_add = txt }
        addLine st [pdx| remove = $txt |] = st { st_remove = txt }
        addLine st stmt = trace ("Unknown in swapTrait: " ++ show stmt) st
        ppST st = do
            traitaddloc <- getGameL10n (st_add st)
            traitremoveloc <- getGameL10n (st_remove st)
            let same = traitaddloc == traitremoveloc
            namemsg <- indentUp $ plainMsg' ("'''" <> traitaddloc <> "'''")
            traitmsg' <- indentUp $ getLeaderTraits (st_add st)
            let traitmsg = namemsg : traitmsg'
            baseMsg <- if same
                then msgToPP MsgModifyCountryLeaderTrait
                else msgToPP $ MsgReplaceCountryLeaderTrait traitremoveloc
            return $ baseMsg ++ traitmsg
swapLeaderTrait stmt = preStatement stmt

getLeaderTraits :: (Monad m, HOI4Info g) => Text -> PPT g m IndentedMessages
getLeaderTraits trait = do
    traits <- getCountryLeaderTraits
    case HM.lookup trait traits of
        Just clt-> do
            mod <- maybe (return []) (\t -> fold <$> indentUp (traverse (modifierMSG False) t)) (clt_modifier clt)
            equipmod <- maybe (return []) (indentUp . handleEquipmentBonus) (clt_equipment_bonus clt)
            tarmod <- maybe (return []) (indentUp . fmap concat . mapM handleTargetedModifier) (clt_targeted_modifier clt)
            hidmod <- maybe (return []) (indentUp . handleModifier) (clt_hidden_modifier clt)
            return ( mod ++ tarmod ++ equipmod ++ hidmod)
        Nothing -> getUnitTraits trait

getUnitTraits :: (Monad m, HOI4Info g) => Text-> PPT g m IndentedMessages
getUnitTraits trait = do
    traits <- getUnitLeaderTraits
    case HM.lookup trait traits of
        Just ult-> do
            attack <- maybe (return []) (indentUp . msgToPP . MsgAddSkill "Attack") (ult_attack_skill ult)
            defense <- maybe (return []) (indentUp . msgToPP . MsgAddSkill "Defense") (ult_defense_skill ult)
            logistics <- maybe (return []) (indentUp . msgToPP . MsgAddSkill "Logistics") (ult_logistics_skill ult)
            planning <- maybe (return []) (indentUp . msgToPP . MsgAddSkill "Planning") (ult_planning_skill ult)
            maneuvering <- maybe (return []) (indentUp . msgToPP . MsgAddSkill "Maneuvering") (ult_maneuvering_skill ult)
            coordination <- maybe (return []) (indentUp . msgToPP . MsgAddSkill "Coordination") (ult_coordination_skill ult)
            let skillmsg = attack ++ defense ++ logistics ++ planning ++ maneuvering ++ coordination
            mod <- maybe (return []) (indentUp . handleModifier) (ult_modifier ult)
            nsmod <- maybe (return []) (indentUp . handleModifier) (ult_non_shared_modifier ult)
            ccmod <- maybe (return []) (indentUp . handleModifier) (ult_corps_commander_modifier ult)
            fmmod <- maybe (return []) (indentUp . handleModifier) (ult_field_marshal_modifier ult)
            sumod <- maybe (return []) (indentUp . handleEquipmentBonus) (ult_sub_unit_modifiers ult)
            return (skillmsg ++ mod ++ nsmod ++ ccmod ++ fmmod ++ sumod)
        Nothing -> return []
