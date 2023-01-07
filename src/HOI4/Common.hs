{-# LANGUAGE TupleSections #-}
{-|
Module      : HOI4.Common
Description : Message handler for Europa Hearts of Iron IV
-}
module HOI4.Common (
        ppScript
    ,   ppStatement
    ,   ppMtth
    ,   ppOne
    ,   ppMany
    ,   AIWillDo (..), AIModifier (..)
    ,   ppAiWillDo, ppAiMod
    ,   extractStmt, matchLhsText, matchExactText
    ,   module HOI4.Types
    ) where

import Debug.Trace (trace, traceM)
import Yaml (LocEntry (..))

import Control.Applicative (liftA2)
import Control.Arrow (first)
import Control.Monad (liftM, MonadPlus (..), forM, foldM, join {- temp -}, when)
import Control.Monad.Reader (MonadReader (..), asks)
import Control.Monad.State (MonadState (..), gets)

import Data.Char (isUpper, toUpper, toLower, isDigit)
import Data.List (foldl', intersperse)
import Data.Maybe (isJust, fromMaybe, listToMaybe, fromJust)
import Data.Monoid ((<>))
import Data.Foldable (fold)
import Data.Void (Void)

import Data.ByteString (ByteString)

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Encoding as TE

-- TODO: get rid of these, do icon key lookups from another module
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Trie (Trie)
import qualified Data.Trie as Tr

import qualified Data.Set as S

import Text.PrettyPrint.Leijen.Text (Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP

import Abstract -- everything
import qualified Doc
import HOI4.Messages -- everything
import MessageTools (plural)
import QQ (pdx)
import SettingsTypes -- everything
import HOI4.Handlers -- everything
import HOI4.SpecialHandlers -- everything
import HOI4.Types -- everything

-- no particular order from here... TODO: organize this!

-- | Format a script as wiki text.
ppScript :: (HOI4Info g, Monad m) =>
    GenericScript -> PPT g m Doc
ppScript [] = return "(Nothing)"
ppScript script = imsg2doc =<< ppMany script

-- | Format a single statement as wiki text.
ppStatement :: (HOI4Info g, Monad m) =>
    GenericStatement -> PPT g m Doc
ppStatement statement = imsg2doc =<< ppOne statement

flagTextMaybe :: (HOI4Info g, Monad m) => Text -> PPT g m (Text,Text)
flagTextMaybe = fmap (mempty,) . flagText (Just HOI4Country)

-- | Extract the appropriate message(s) from a script.
ppMany :: (HOI4Info g, Monad m) => GenericScript -> PPT g m IndentedMessages
ppMany scr = indentUp (concat <$> mapM ppOne scr)

-- | Table of handlers for statements. Dispatch on strings is /much/ quicker
-- using a lookup table than a huge @case@ expression, which uses @('==')@ on
-- each one in turn.
--
-- When adding a new statement handler, add it to one of the sections in
-- alphabetical order if possible, and use one of the generic functions for it
-- if applicable.
ppHandlers :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
ppHandlers = foldl' Tr.unionL Tr.empty
    [ handlersRhsIrrelevant
    , handlersNumeric
    , handlersNumericCompare
    , handlersNumericIcons
    , handlersModifiers
    , handlersCompound
    , handlersLocRhs
    , handlersState
    , handlersFlagOrstate
    , handlersNumericOrFlag
    , handlersAdvisorId
    , handlersTypewriter
    , handlersSimpleIcon
    , handlersSimpleFlag
    , handlersFlagOrYesNo
    , handlersIconFlagOrPronoun
    , handlersYesNo
    , handlersNumericOrTag
    , handlersNumStates
    , handlersTextValue
    , handlersTextAtom
    , handlersSpecialComplex
    , handlersIdeas
    , handlersMisc
    , handlersIgnored
    ]

-- | Handlers for statements where RHS is irrelevant (usually "yes")
handlersRhsIrrelevant :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersRhsIrrelevant = Tr.fromList
        [("dismantle_faction"       , rhsAlwaysYes MsgDismantleFaction)
        ,("drop_cosmetic_tag"       , rhsAlwaysYes MsgDropCosmeticTag)
        ,("kill_country_leader"     , rhsAlwaysYes MsgKillCountryLeader)
        ,("leave_faction"           , rhsAlwaysYes MsgLeaveFaction)
        ,("mark_focus_tree_layout_dirty" , rhsAlwaysYes MsgMarkFocusTreeLayoutDirty)
        ,("retire"                  , rhsAlwaysYes MsgRetire)
        ,("retire_country_leader"   , rhsAlwaysYes MsgRetireCountryLeader)
        ,("set_country_leader_description" , rhsIgnored MsgSetLeaderDescription)
        ,("set_portraits"            , rhsIgnored MsgSetPortraits)
        ]

-- | Handlers for numeric statements
handlersNumeric :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersNumeric = Tr.fromList
        [("add_compliance"                   , numeric MsgAddCompliance)
        ,("add_research_slot"                , numeric MsgAddResearchSlot)
        ,("add_resistance"                   , numeric MsgAddResistance)
        ,("add_threat"                       , numeric MsgAddThreat)
        ,("reset_province_name"              , numeric MsgResetProvinceName)
        ,("set_compliance"                   , numeric MsgSetCompliance)
        ,("set_political_power"              , numeric MsgSetPoliticalPower)
        ,("set_stability"                    , numeric MsgSetStability)
        ,("set_war_support"                  , numeric MsgSetWarSupport)
        ,("add_logistics"                    , numeric MsgAddLogistics)
        ,("add_planning"                     , numeric MsgAddPlanning)
        ,("add_defense"                      , numeric MsgAddDefense)
        ,("add_attack"                       , numeric MsgAddAttack)
        ,("add_coordination"                 , numeric MsgAddCoordination)
        ,("add_maneuver"                     , numeric MsgAddManeuver)
        ]

-- | Handlers for numeric statements that compare
handlersNumericCompare :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersNumericCompare = Tr.fromList
        [("air_base"                         , numericCompare "more than" "less than" MsgAirBase MsgAirBaseVar)
        ,("alliance_strength_ratio"          , numericCompare "more than" "less than" MsgAllianceStrengthRatio MsgAllianceStrengthRatioVar)
        ,("amount_research_slots"            , numericCompare "more than" "less than" MsgAmountResearchSlots MsgAmountResearchSlotsVar)
        ,("any_war_score"                    , numericCompare "over" "under" MsgAnyWarScore MsgAnyWarScoreVar)
        ,("arms_factory"                     , numericCompare "more than" "less than" MsgArmsFactory MsgArmsFactoryVar)
        ,("command_power"                    , numericCompare "more than" "less than" MsgCommandPower MsgCommandPowerVar)
        ,("compare_autonomy_progress_ratio"  , numericCompare "over" "under" MsgCompareAutonomyProgressRatio MsgCompareAutonomyProgressRatioVar)
        ,("dockyard"                         , numericCompare "more than" "less than" MsgDockyard MsgDockyardVar)
        ,("compliance"                       , numericCompare "more than" "less than" MsgCompliance MsgComplianceVar)
        ,("resistance"                       , numericCompare "more than" "less than" MsgResistance MsgResistanceVar)
        ,("enemies_strength_ratio"           , numericCompare "over" "under" MsgEnemiesStrengthRatio MsgEnemiesStrengthRatioVar)
        ,("has_added_tension_amount"         , numericCompare "more than" "less than" MsgHasAddedTensionAmount MsgHasAddedTensionAmountVar)
        ,("has_air_experience"               , numericCompare "more than" "less than" MsgHasAirExperience MsgHasAirExperienceVar)
        ,("has_army_experience"              , numericCompare "more than" "less than" MsgHasArmyExperience MsgHasArmyExperienceVar)
        ,("has_bombing_war_support"          , numericCompare "more than" "less than" MsgHasBombingWarSupport MsgHasBombingWarSupportVar)
        ,("has_casualties_war_support"       , numericCompare "more than" "less than" MsgHasCasualtiesWarSupport MsgHasCasualtiesWarSupportVar)
        ,("has_convoys_war_support"          , numericCompare "more than" "less than" MsgHasConvoysWarSupport MsgHasConvoysWarSupportVar)
        ,("has_equipment"                    , numericCompareCompoundLoc "More than" "Less than" MsgHasEquipment MsgHasEquipmentVar)
        ,("has_navy_experience"              , numericCompare "more than" "less than" MsgHasNavyExperience MsgHasNavyExperienceVar)
        ,("has_army_manpower"                , numericCompareCompound "more than" "less than" MsgHasArmyManpower MsgHasArmyManpowerVar)
        ,("has_legitimacy"                   , numericCompare "more than" "less than" MsgHasLegitimacy MsgHasLegitimacyVar)
        ,("has_manpower"                     , numericCompare "more than" "less than" MsgHasManpower MsgHasManpowerVar)
        ,("has_political_power"              , numericCompare "more than" "less than" MsgHasPoliticalPower MsgHasPoliticalPowerVar)
        ,("political_power_daily"            , numericCompare "more than" "less than" MsgPoliticalPowerDaily MsgPoliticalPowerDailyVar)
        ,("has_stability"                    , numericCompare "more than" "less than" MsgHasStability MsgHasStabilityVar)
        ,("has_war_support"                  , numericCompare "more than" "less than" MsgHasWarSupport MsgHasWarSupportVar)
        ,("industrial_complex"               , numericCompare "more than" "fewer than" MsgIndustrialComplex MsgIndustrialComplexVar)
        ,("infrastructure"                   , numericCompare "more than" "fewer than" MsgInfrastructure MsgInfrastructureVar)
        ,("nuclear_reactor"                  , numericCompare "more than" "less than" MsgNuclearReactor MsgNuclearReactorVar)
        ,("num_of_controlled_factories"      , numericCompare "more than" "fewer than" MsgNumOfControlledFactories MsgNumOfControlledFactoriesVar)
        ,("num_of_controlled_states"         , numericCompare "more than" "fewer than" MsgNumOfControlledStates MsgNumOfControlledStatesVar)
        ,("num_of_civilian_factories"        , numericCompare "more than" "fewer than" MsgNumOfCivilianFactories MsgNumOfCivilianFactoriesVar)
        ,("num_of_available_civilian_factories" , numericCompare "more than" "fewer than" MsgNumOfAvailableCivilianFactories MsgNumOfAvailableCivilianFactoriesVar)
        ,("num_of_civilian_factories_available_for_projects" , numericCompare "more than" "less than" MsgNumOfProjectFactories MsgNumOfProjectFactoriesVar)
        ,("num_of_factories"                 , numericCompare "more than" "fewer than" MsgNumOfFactories MsgNumOfFactoriesVar)
        ,("num_of_nukes"                     , numericCompare "more than" "fewer than" MsgNumOfNukes MsgNumOfNukesVar)
        ,("num_of_naval_factories"           , numericCompare "more than" "fewer than" MsgNumOfNavalFactories MsgNumOfNavalFactoriesVar)
        ,("num_of_operatives"                , numericCompare "more than" "fewer than" MsgNumOfOperatives MsgNumOfOperativesVar)
        ,("num_subjects"                     , numericCompare "more than" "fewer than" MsgNumSubjects MsgNumSubjectsVar)
        ,("original_research_slots"          , numericCompare "more than" "fewer than" MsgOriginalResearchSlots MsgOriginalResearchSlotsVar)
        ,("state_population"                 , numericCompare "more than" "less than" MsgStatePopulation MsgStatePopulationVar)
        ,("surrender_progress"               , numericCompare "more than" "less than" MsgSurrenderProgress MsgSurrenderProgressVar)
        ,("threat"                           , numericCompare "more than" "less than" MsgThreat MsgThreatVar)
        ,("fascism"                          , numericCompare "more than" "less than" MsgFascismCompare MsgFascismCompareVar)
        ,("democratic"                       , numericCompare "more than" "less than" MsgDemocraticCompare MsgDemocraticCompareVar)
        ,("communism"                        , numericCompare "more than" "less than" MsgCommunismCompare MsgCommunismCompareVar)
        ,("neutrality"                       , numericCompare "more than" "less than" MsgNeutralityCompare MsgNeutralityCompareVar)
        ]

-- | Handlers for numeric statements with icons
handlersNumericIcons :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersNumericIcons = Tr.fromList
        [("add_manpower"             , numericIconLoc "manpower" "MANPOWER" MsgGainLosePosIcon MsgGainLoseLocIconVar)
        ,("add_extra_state_shared_building_slots", numericIcon "building slot" MsgAddExtraStateSharedBuildingSlots MsgAddExtraStateSharedBuildingSlotsVar)
        ,("add_political_power"      , numericIconLoc "political power" "POLITICAL_POWER" MsgGainLosePosIcon MsgGainLoseLocIconVar)
        ,("add_command_power"        , numericIconLoc "command power" "COMMAND_POWER" MsgGainLosePosIcon MsgGainLoseLocIconVar)
        ,("add_stability"            , numericIconLoc "stability" "STABILITY" MsgGainLocPC MsgGainLoseLocIconVar)
        ,("add_war_support"          , numericIconLoc "war support" "WAR_SUPPORT" MsgGainLocPC MsgGainLoseLocIconVar)
        ,("air_experience"           , numericIconLoc "air exp" "AIR_EXPERIENCE" MsgGainLosePosIcon MsgGainLoseLocIconVar)
        ,("army_experience"          , numericIconLoc "army exp" "ARMY_EXPERIENCE" MsgGainLosePosIcon MsgGainLoseLocIconVar)
        ,("navy_experience"          , numericIconLoc "navy exp" "NAVY_EXPERIENCE" MsgGainLosePosIcon MsgGainLoseLocIconVar)
        ]

-- | Handlers for statements pertaining to modifiers
handlersModifiers :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersModifiers = Tr.fromList
        [("add_dynamic_modifier"        , addDynamicModifier)
        ,("remove_dynamic_modifier"     , removeDynamicModifier)
        ,("has_dynamic_modifier"        , hasDynamicModifier)
        ,("modifier"                    , handleModifier)
        ,("add_state_modifier"          , plainmodifiermsg MsgAddStateModifier)
        ,("add_power_balance_modifier"  , addPowerBalanceModifier)
        ,("remove_power_balance_modifier" , textAtomKey "id" "modifier" MsgRemovePowerBalanceModifier tryLoc)
        ,("has_power_balance_modifier"  , textAtomKey "id" "modifier" MsgHasPowerBalanceModifier tryLoc)
        ,("research_bonus"              , handleResearchBonus)
        ,("targeted_modifier"           , handleTargetedModifier)
        ,("equipment_bonus"             , handleEquipmentBonus)
        ]

-- | Handlers for simple compound statements
handlersCompound :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersCompound = Tr.fromList
        -- Note that "any" can mean "all" or "one or more" depending on context.
        [        -- There is a semantic distinction between "all" and "every",
        -- namely that the former means "this is true for all <type>" while
        -- the latter means "do this for every <type>."
        -- trigger scopes
         ("all_allied_country" {- sic -}, scope HOI4Country     . compoundMessage MsgAllAlliedCountry)
        ,("all_army_leader"             , scope HOI4UnitLeader  . compoundMessage MsgAllArmyLeader)
        ,("all_character"               , scope HOI4ScopeCharacter   . compoundMessage MsgAllCharacter)
        ,("all_controlled_state"        , scope HOI4ScopeState  . compoundMessage MsgAllControlledState)
        ,("all_core_state"              , scope HOI4ScopeState  . compoundMessage MsgAllCoreState)
        ,("all_country"                 , scope HOI4Country     . compoundMessage MsgAllCountry)
        ,("all_country_with_original_tag", scope HOI4Country    . compoundMessageExtractTag "original_tag_to_check" MsgAllCountryWithOriginalTag)
        ,("all_enemy_country"           , scope HOI4Country     . compoundMessage MsgAllEnemyCountry)
        ,("all_guaranteed_country"      , scope HOI4Country     . compoundMessage MsgAllGuaranteedCountry)
        ,("all_navy_leader"             , scope HOI4UnitLeader  . compoundMessage MsgAllNavyLeader)
        ,("all_neighbor_country"        , scope HOI4Country     . compoundMessage MsgAllNeighborCountry)
        ,("all_neighbor_state"          , scope HOI4ScopeState  . compoundMessage MsgAllNeighborState)
        ,("all_occupied_country"        , scope HOI4Country     . compoundMessage MsgAllOccupiedCountry)
        ,("all_operative_leader"        , scope HOI4Operative   . compoundMessage MsgAllOperativeLeader)
        ,("all_other_country"           , scope HOI4Country     . compoundMessage MsgAllOtherCountry)
        ,("all_owned_state"             , scope HOI4ScopeState  . compoundMessage MsgAllOwnedState)
        ,("all_state"                   , scope HOI4ScopeState  . compoundMessage MsgAllState)
        ,("all_subject_countries"{- sic -}, scope HOI4Country    . compoundMessage MsgAllSubjectCountries)
        ,("all_unit_leader"             , scope HOI4UnitLeader  . compoundMessage MsgAllUnitLeader)
        ,("any_allied_country"          , scope HOI4Country     . compoundMessage MsgAnyAlliedCountry)
        ,("any_army_leader"             , scope HOI4UnitLeader  . compoundMessage MsgAnyArmyLeader)
        ,("any_character"               , scope HOI4ScopeCharacter   . compoundMessage MsgAnyCharacter)
        ,("any_controlled_state"        , scope HOI4ScopeState  . compoundMessage MsgAnyControlledState)
        ,("any_core_state"              , scope HOI4ScopeState  . compoundMessage MsgAnyCoreState)
        ,("any_country"                 , scope HOI4Country     . compoundMessage MsgAnyCountry)
        ,("any_country_division"        , scope HOI4Division     . compoundMessage MsgAnyCountryDivision)
        ,("any_country_with_core"       , scope HOI4Country     . compoundMessage MsgAnyCountryWithCore)
        ,("any_country_with_original_tag", scope HOI4Country    . compoundMessageExtractTag "original_tag_to_check" MsgAnyCountryWithOriginalTag)
        ,("any_enemy_country"           , scope HOI4Country     . compoundMessage MsgAnyEnemyCountry)
        ,("any_guaranteed_country"      , scope HOI4Country     . compoundMessage MsgAnyGuaranteedCountry)
        ,("any_home_area_neighbor_country", scope HOI4Country    . compoundMessage MsgAnyHomeAreaNeighborCountry)
        ,("any_navy_leader"             , scope HOI4UnitLeader  . compoundMessage MsgAnyNavyLeader)
        ,("any_neighbor_country"        , scope HOI4Country     . compoundMessage MsgAnyNeighborCountry)
        ,("any_neighbor_state"          , scope HOI4ScopeState  . compoundMessage MsgAnyNeighborState)
        ,("any_occupied_country"        , scope HOI4Country     . compoundMessage MsgAnyOccupiedCountry)
        ,("any_operative_leader"        , scope HOI4Operative   . compoundMessage MsgAnyOperativeLeader)
        ,("any_other_country"           , scope HOI4Country     . compoundMessage MsgAnyOtherCountry)
        ,("any_owned_state"             , scope HOI4ScopeState  . compoundMessage MsgAnyOwnedState)
        ,("any_state"                   , scope HOI4ScopeState  . compoundMessage MsgAnyState)
        ,("any_state_division"          , scope HOI4Division    . compoundMessage MsgAnyStateDivision)
        ,("any_subject_country"         , scope HOI4Country     . compoundMessage MsgAnySubjectCountry)
        ,("any_unit_leader"             , scope HOI4UnitLeader  . compoundMessage MsgAnyUnitLeader)
        -- effect scopes
        ,("every_army_leader"           , scope HOI4UnitLeader  . compoundMessage MsgEveryArmyLeader)
        ,("every_character"             , scope HOI4ScopeCharacter   . compoundMessage MsgEveryCharacter)
        ,("every_controlled_state"      , scope HOI4ScopeState  . compoundMessage MsgEveryControlledState)
        ,("every_core_state"            , scope HOI4ScopeState  . compoundMessage MsgEveryCoreState)
        ,("every_country"               , scope HOI4Country     . compoundMessage MsgEveryCountry)
        ,("every_country_division"      , scope HOI4Division     . compoundMessage MsgEveryCountryDivision)
        ,("every_country_with_original_tag", scope HOI4Country  . compoundMessageExtractTag "original_tag_to_check" MsgEveryCountryWithOriginalTag)
        ,("every_enemy_country"         , scope HOI4Country     . compoundMessage MsgEveryEnemyCountry)
        ,("every_navy_leader"           , scope HOI4UnitLeader  . compoundMessage MsgEveryNavyLeader)
        ,("every_neighbor_country"      , scope HOI4Country     . compoundMessage MsgEveryNeighborCountry)
        ,("every_neighbor_state"        , scope HOI4ScopeState  . compoundMessage MsgEveryNeighborState)
        ,("every_occupied_country"      , scope HOI4Country     . compoundMessage MsgEveryOccupiedCountry)
        ,("every_operative"             , scope HOI4Operative   . compoundMessage MsgEveryOperative)
        ,("every_other_country"         , scope HOI4Country     . compoundMessage MsgEveryOtherCountry)
        ,("every_owned_state"           , scope HOI4ScopeState  . compoundMessage MsgEveryOwnedState)
        ,("every_possible_country"      , scope HOI4Country     . compoundMessage MsgEveryPossibleCountry)
        ,("every_state"                 , scope HOI4ScopeState  . compoundMessage MsgEveryState)
        ,("every_state_division"        , scope HOI4Division     . compoundMessage MsgEveryStateDivision)
        ,("every_subject_country"       , scope HOI4Country     . compoundMessage MsgEverySubjectCountry)
        ,("every_unit_leader"           , scope HOI4UnitLeader  . compoundMessage MsgEveryUnitLeader)
        ,("global_every_army_leader"    , scope HOI4UnitLeader  . compoundMessage MsgGlobalEveryArmyLeader)
        ,("random_army_leader"          , scope HOI4UnitLeader  . compoundMessage MsgRandomArmyLeader)
        ,("random_character"            , scope HOI4ScopeCharacter   . compoundMessage MsgRandomCharacter)
        ,("random_controlled_state"     , scope HOI4ScopeState  . compoundMessage MsgRandomControlledState)
        ,("random_core_state"           , scope HOI4ScopeState  . compoundMessage MsgRandomCoreState)
        ,("random_country"              , scope HOI4Country     . compoundMessage MsgRandomCountry)
        ,("random_country_division"     , scope HOI4Country     . compoundMessage MsgRandomCountryDivision)
        ,("random_country_with_original_tag", scope HOI4Country . compoundMessageExtractTag "original_tag_to_check" MsgRandomCountryWithOriginalTag)
        ,("random_enemy_country"        , scope HOI4Country     . compoundMessage MsgRandomEnemyCountry)
        ,("random_navy_leader"          , scope HOI4UnitLeader  . compoundMessage MsgRandomNavyLeader)
        ,("random_neighbor_country"     , scope HOI4Country     . compoundMessage MsgRandomNeighborCountry)
        ,("random_neighbor_state"       , scope HOI4ScopeState  . compoundMessage MsgRandomNeighborState)
        ,("random_occupied_country"     , scope HOI4Country     . compoundMessage MsgRandomOccupiedCountry)
        ,("random_operative"            , scope HOI4Operative   . compoundMessage MsgRandomOperative)
        ,("random_other_country"        , scope HOI4Country     . compoundMessage MsgRandomOtherCountry)
        ,("random_owned_controlled_state" , scope HOI4ScopeState . compoundMessage MsgRandomOwnedControlledState)
        ,("random_owned_state"          , scope HOI4ScopeState  . compoundMessage MsgRandomOwnedState)
        ,("random_state"                , scope HOI4ScopeState  . compoundMessage MsgRandomState)
        ,("random_state_division"       , scope HOI4Division    . compoundMessage MsgRandomStateDivision)
        ,("random_subject_country"      , scope HOI4Country     . compoundMessage MsgRandomSubjectCountry)
        ,("random_unit_leader"          , scope HOI4UnitLeader  . compoundMessage MsgRandomUnitLeader)
        -- dual scopes
        ,("root"                        , compoundMessagePronoun) --ROOT
        ,("prev"                        , compoundMessagePronoun) --PREV
        ,("prev.prev"                   , compoundMessagePronoun) -- need beter way
        ,("prev.prev.prev"              , compoundMessagePronoun) -- need beter way
        ,("from"                        , compoundMessagePronoun) --FROM
        ,("from.from"                   , compoundMessagePronoun) -- need beter way
        ,("from.from.from"              , compoundMessagePronoun) -- need beter way
        -- no THIS, not used on LHS
        ,("overlord"                    , scope HOI4Country   . compoundMessage MsgOverlordSCOPE)
        ,("faction_leader"              , scope HOI4Country   . compoundMessage MsgFactionLeaderSCOPE)
        ,("owner"                       , compoundMessagePronoun)
        ,("controller"                  , scope HOI4Country   . compoundMessage MsgControllerSCOPE)
        ,("capital_scope"               , scope HOI4ScopeState  . compoundMessage MsgCapitalSCOPE)
        ,("event_target"        , compoundMessageTagged MsgSCOPEEventTarget (Just HOI4Misc)) -- Tagged blocks
        ,("var"                 , compoundMessageTagged MsgSCOPEVariable (Just HOI4Misc)) -- Tagged blocks
        -- arrays
        ,("all_of_scopes"               , scope HOI4Misc . compoundMessageExtract "array" MsgAllOfScopes)
        ,("any_of_scopes"               , scope HOI4Misc . compoundMessageExtract "array" MsgAnyOfScopes)
        ,("for_each_scope_loop"         , scope HOI4Misc . compoundMessageExtract "array" MsgForEachScopeLoop)
        ,("random_scope_in_array"       , scope HOI4Misc . compoundMessageExtract "array" MsgRandomScopeInArray)
        -- flow control
        ,("and"                         , compoundMessage MsgAnd) --AND
        ,("not"                         , compoundMessage MsgNot) --NOT
        ,("or"                          , compoundMessage MsgOr) --OR
        ,("count_triggers"          ,   compoundMessageExtractNum "amount" MsgCountTriggers)
        ,("hidden_trigger"          ,                      compoundMessage MsgHiddenTriggers)
        ,("custom_trigger_tooltip"  ,                      compoundMessage MsgCustomTriggerTooltip)
        ,("hidden_effect"           ,                      compoundMessage MsgHiddenEffect)
        ,("else"                    ,                      compoundMessage MsgElse)
        ,("else_if"                 ,                      compoundMessage MsgElseIf)
        ,("if"                      ,                      compoundMessage MsgIf) -- always needs editing
        ,("limit"                   , setIsInEffect False . compoundMessage MsgLimit) -- always needs editing
        ,("prioritize"              ,                       prioritize) -- always needs editing
        ,("while_loop_effect"       ,                       compoundMessage MsgWhile) -- always needs editing
        ,("for_loop_effect"         ,                       compoundMessage MsgFor) -- always needs editing
        -- random and random_list are also part of flow control but are more complicated
        ]

withLocAtomName :: (HOI4Info g, Monad m) =>
    (Text -> ScriptMessage) -> StatementHandler g m
withLocAtomName msg = withLocAtom' msg (<> "_name")

-- | Handlers for simple statements where RHS is a localizable atom
handlersLocRhs :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersLocRhs = Tr.fromList
        [("create_faction"        , withLocAtom MsgCreateFaction)
        ,("set_state_name"        , withLocAtom MsgSetStateName)
        ,("set_state_category"    , withLocAtom MsgSetStateCategory)
        ,("custom_effect_tooltip" , withLocAtom MsgCustomEffectTooltip)
        ,("has_country_leader_with_trait" , withLocAtom MsgHasCountryLeaderWithTrait)
        ,("has_decision"          , withLocAtomKey MsgHasDecision)
        ,("has_opinion_modifier"  , withLocAtom MsgHasOpinionMod)
        ,("has_power_balance"     , withLocAtomCompound MsgHasPowerBalance)
        ,("has_tech"              , withLocAtom MsgHasTech)
        ,("has_template"          , withLocAtom MsgHasTemplate)
        ,("occupation_law"        , withLocAtom MsgOccupationLaw)
        ,("is_character"          , withLocAtom MsgIsCharacter)
        ,("is_on_continent"       , withLocAtom MsgIsOnContinent)
        ,("is_in_tech_sharing_group" , withLocAtomName MsgIsInTechSharingGroup)
        ,("add_to_tech_sharing_group" , withLocAtomName MsgAddToTechSharingGroup)
        ,("remove_power_balance"  , withLocAtomCompound MsgRemovePowerBalance)
        ,("tooltip"               , withLocAtom MsgTooltip)
        ]

-- | Handlers for statements whose RHS is a state ID
handlersState :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersState = Tr.fromList
        [("add_state_claim"     , withState MsgAddStateClaim)
        ,("add_state_core"      , withState MsgAddStateCore)
        ,("controls_state"      , withState MsgControlsState)
        ,("has_full_control_of_state" , withState MsgHasFullControlOfState)
        ,("owns_state"          , withState MsgOwnsState)
        ,("remove_state_claim"  , withState MsgRemoveStateClaim)
        ,("remove_state_core"   , withState MsgRemoveStateCore)
        ,("set_state_controller" , withState MsgSetStateController)
        ,("set_state_owner"     , withState MsgSetStateOwner)
        ,("state"               , withState MsgStateId)
        ,("transfer_state"      , withState MsgTransferState)
        ]

-- | Handlers for statements whose RHS is a flag OR a province ID
-- Also abusable for tag,scope purposes
handlersFlagOrstate :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersFlagOrstate = Tr.fromList
        [
        ]

-- | Handlers for statements whose RHS is a number OR a tag/pronoun, with icon
handlersNumericOrFlag :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersNumericOrFlag = Tr.fromList
        [
        ]

-- TODO: parse advisor files
-- | Handlers for statements whose RHS is an advisor ID
handlersAdvisorId :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersAdvisorId = Tr.fromList
        [
        ]

-- | Simple statements whose RHS should be presented as is, in typewriter face
handlersTypewriter :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersTypewriter = Tr.fromList
        [("clr_character_flag"  , withNonlocAtom2 MsgCharacterFlag MsgClearFlag)
        ,("clr_country_flag"    , withNonlocAtom2 MsgCountryFlag MsgClearFlag)
        ,("clr_global_flag"     , withNonlocAtom2 MsgGlobalFlag MsgClearFlag)
        ,("clr_state_flag"      , withNonlocAtom2 MsgStateFlag MsgClearFlag)
        ,("clr_unit_leader_flag" , withNonlocAtom2 MsgUnitLeaderFlag MsgClearFlag)
        ,("has_focus_tree"        , withNonlocAtom MsgHasFocusTree)
        ,("save_event_target_as", withNonlocAtom MsgSaveEventTargetAs)
        ,("save_global_event_target_as", withNonlocAtom MsgSaveGlobalEventTargetAs)
        ,("set_cosmetic_tag"    , withNonlocAtom MsgSetCosmeticTag)
        ,("has_cosmetic_tag"    , withNonlocAtom MsgHasCosmeticTag)

        ,("has_opinion_modifier"  , withNonlocAtom MsgHasOpinionMod)
        ]

-- | Handlers for simple statements with icon
handlersSimpleIcon :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersSimpleIcon = Tr.fromList
        [("has_autonomy_state"      , withLocAtomIcon MsgHasAutonomyState True)
        ,("has_government"          , withLocAtomIcon MsgHasGovernment False)
        ]

-- | Handlers for simple statements with a flag or pronoun
handlersSimpleFlag :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersSimpleFlag = Tr.fromList
        [("add_claim_by"            , withFlag MsgAddClaimBy)
        ,("add_core_of"             , withFlag MsgAddCoreOf)
        ,("add_nationality"         , withFlag MsgAddNationality)
        ,("add_to_faction"          , withFlag MsgAddToFaction)
        ,("change_tag_from"         , withFlag MsgChangeTagFrom)
        ,("country_exists"          , withFlag MsgCountryExists)
        ,("has_defensive_war_with"  , withFlag MsgHasDefensiveWarWith)
        ,("give_guarantee"          , withFlag MsgGiveGuarantee)
        ,("give_military_access"    , withFlag MsgGiveMilitaryAccess)
        ,("has_attache_from"        , withFlag MsgHasAttacheFrom)
        ,("has_border_war_with"     , withFlag MsgHasBorderWarWith)
        ,("has_guaranteed"          , withFlag MsgHasGuaranteed)
        ,("has_military_access_to" , withFlag MsgHasMilitaryAccessTo)
        ,("has_non_aggression_pact_with" , withFlag MsgHasNonAggressionPactWith)
        ,("has_offensive_war_with"  , withFlag MsgHasOffensiveWarWith)
        ,("has_subject"             , withFlag MsgHasSubject)
        ,("occupied_country_tag"    , withFlag MsgOccupiedCountryTag)
        ,("inherit_technology"      , withFlag MsgInheritTechnology)
        ,("is_ally_with"            , withFlag MsgIsAllyWith)
        ,("is_controlled_by"        , withFlag MsgIsControlledBy)
        ,("is_exiled_in"            , withFlag MsgIsExiledIn)
        ,("is_fully_controlled_by"  , withFlag MsgIsFullyControlledBy)
        ,("is_guaranteed_by"        , withFlag MsgIsGuaranteedBy)
        ,("is_hosting_exile"        , withFlag MsgIsHostingExile)
        ,("is_in_faction_with"      , withFlag MsgIsInFactionWith)
        ,("is_justifying_wargoal_against" , withFlag MsgIsJustifyingWargoalAgainst)
        ,("is_neighbor_of"          , withFlag MsgIsNeighborOf)
        ,("is_owned_and_controlled_by" , withFlag MsgIsOwnedAndControlledBy)
        ,("is_puppet_of"            , withFlag MsgIsPuppetOf)
        ,("is_claimed_by"           , withFlag MsgIsClaimedBy)
        ,("is_core_of"              , withFlag MsgIsStateCore)
        ,("is_subject_of"           , withFlag MsgIsSubjectOf)
        ,("is_owned_by"             , withFlag MsgIsOwnedBy)
        ,("puppet"                  , withFlag MsgPuppet)
        ,("recall_volunteers_from"  , withFlag MsgRecallVolunteersFrom)
        ,("release"                 , withFlag MsgRelease)
        ,("release_puppet"          , withFlag MsgReleasePuppet)
        ,("remove_claim_by"         , withFlag MsgRemoveClaimBy)
        ,("remove_core_of"          , withFlag MsgRemoveCoreOf)
        ,("remove_from_faction"     , withFlag MsgRemoveFromFaction)
        ,("set_state_controller_to" , withFlag MsgSetStateControllerTo)
        ,("tag"                     , withFlag MsgCountryIs)
        ,("transfer_state_to"       , withFlag MsgTransferStateTo)
        ,("has_war_with"            , withFlag MsgHasWarWith)
        ,("has_war_together_with"   , withFlag MsgHasWarTogetherWith)
        ,("original_tag"            , withFlagAndTag MsgOrignalTag)
        ,("white_peace"             , withFlag MsgMakeWhitePeace)
        ]

-- | Handlers for simple generic statements with a flag or "yes"/"no"
handlersFlagOrYesNo :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersFlagOrYesNo = Tr.fromList
        [("start_resistance"            , withFlagOrBool MsgStartResistance MsgCountryStartResistance)
        ]

-- | Handlers for statements whose RHS may be an icon, a flag, a province, or a
-- pronoun (such as ROOT).
handlersIconFlagOrPronoun :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersIconFlagOrPronoun = Tr.fromList
        [
        ]



-- | Handlers for yes/no statements
handlersYesNo :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersYesNo = Tr.fromList
        [("is_ai"                       , withBool MsgIsAIControlled)
        ,("always"                      , withBool MsgAlways)
        ,("country_lock_all_division_template" , withBool MsgLockDivision)
        ,("exists"                      , withBool MsgExists)
        ,("has_attache"                 , withBool MsgHasAttache)
        ,("has_border_war"              , withBool MsgHasBorderWar)
        ,("has_capitulated"             , withBool MsgHasCapitulated)
        ,("has_civil_war"               , withBool MsgHasCivilWar)
        ,("has_defensive_war"           , withBool MsgHasDefensiveWar)
        ,("has_intelligence_agency"     , withBool MsgHasIntelligenceAgency)
        ,("has_offensive_war"           , withBool MsgHasOffensiveWar)
        ,("has_war"                     , withBool MsgHasWar)
        ,("is_capital"                  , withBool MsgIsCapital)
        ,("is_coastal"                  , withBool MsgIsCoastal)
        ,("is_country_leader"           , withBool MsgIsCountryLeader)
        ,("is_demilitarized_zone"       , withBool MsgIsDemilitarizedZone)
        ,("is_faction_leader"           , withBool MsgIsFactionLeader)
        ,("is_female"                   , withBoolHOI4Scope MsgIsFemaleLeader MsgIsFemale)
        ,("is_government_in_exile"      , withBool MsgIsGovernmentInExile)
        ,("is_historical_focus_on"      , withBool MsgIsHistoricalFocusOn)
        ,("is_operative_captured"       , withBool MsgIsOperativeCaptured)
        ,("is_in_faction"               , withBool MsgIsInFaction)
        ,("is_in_home_area"             , withBool MsgIsInHomeArea)
        ,("is_island_state"             , withBool MsgIsIslandState)
        ,("is_major"                    , withBool MsgIsMajor)
        ,("is_puppet"                   , withBool MsgIsPuppet)
        ,("is_subject"                  , withBool MsgIsSubject)
        ,("is_unit_leader"              , withBool MsgIsUnitLeader)
        ,("set_demilitarized_zone"      , withBool MsgSetDemilitarizedZone)
        ]

-- | Handlers for statements that may be numeric or a tag
handlersNumericOrTag :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersNumericOrTag = Tr.fromList
        [
        ]

-- | Handlers querying the number of provinces of some kind, mostly religions
-- and trade goods
handlersNumStates :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersNumStates = Tr.fromList
        [
        ]

-- Helpers for text/value pairs
tryLocAndIconTitle :: (IsGameData (GameData g), Monad m) => Text -> PPT g m (Text, Text)
tryLocAndIconTitle t = tryLocAndIcon (t <> "_title")

-- | Handlers for text/value pairs.
--
-- $textvalue
handlersTextValue :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersTextValue = Tr.fromList
        [("add_offsite_building"        , textValue "type" "level" MsgAddOffsiteBuilding MsgAddOffsiteBuildingVar tryLocAndIcon)
        ,("add_popularity"              , textValue "ideology" "popularity" MsgAddPopularity MsgAddPopularityVar tryLocAndIcon)
        ,("add_power_balance_value"     , textValueKey "id" "value" MsgAddPowerBalanceValue MsgAddPowerBalanceValueVar)
        ,("core_compliance"             , textValueCompare "occupied_country_tag" "value" "more than" "less than" MsgCoreCompliance MsgCoreComplianceVar flagTextMaybe)
        ,("core_resistance"             , textValueCompare "occupied_country_tag" "value" "more than" "less than" MsgCoreResistance MsgCoreResistanceVar flagTextMaybe)
        ,("has_volunteers_amount_from"  , textValueCompare "tag" "count" "more than" "less than" MsgHasVolunteersAmountFrom MsgHasVolunteersAmountFromVar flagTextMaybe)
        ,("modify_tech_sharing_bonus"   , textValue "id" "bonus" MsgModifyTechSharingBonus MsgModifyTechSharingBonusVar tryLocMaybe) --icon ignored
        ,("power_balance_value"         , textValueCompare "id" "value" "more than" "less than" MsgPowerBalanceValue MsgPowerBalanceValueVar tryLocMaybe)
        ,("set_province_name"           , textValue "name" "id" MsgSetProvinceName MsgSetProvinceNameVar tryLocMaybe)
        ,("set_victory_points"          , valueValue "province" "value" MsgSetVictoryPoints MsgSetVictoryPointsVar)
        ,("add_victory_points"          , valueValue "province" "value" MsgAddVictoryPoints MsgAddVictoryPointsVar)
        ,("stockpile_ratio"             , textValueCompare "archetype" "ratio" "more than" "less than" MsgStockpileRatio MsgStockpileRatioVar tryLocMaybe)
        ,("strength_ratio"              , textValueCompare "tag" "ratio" "more than" "less than" MsgStrengthRatio MsgStrengthRatioVar flagTextMaybe)
        ,("remove_building"             , textValue "type" "level" MsgRemoveBuilding MsgRemoveBuildingVar tryLocAndIcon)
        ,("modify_character_flag"       , withNonlocTextValue "flag" "value" MsgCharacterFlag MsgModifyFlag MsgModifyFlagVar) -- Localization/icon ignored
        ,("modify_country_flag"         , withNonlocTextValue "flag" "value" MsgCountryFlag MsgModifyFlag MsgModifyFlagVar) -- Localization/icon ignored
        ,("modify_global_flag"          , withNonlocTextValue "flag" "value" MsgGlobalFlag MsgModifyFlag MsgModifyFlagVar) -- Localization/icon ignored
        ,("modify_state_flag"           , withNonlocTextValue "flag" "value" MsgStateFlag MsgModifyFlag MsgModifyFlagVar) -- Localization/icon ignored
        ,("modify_unit_leader_flag"     , withNonlocTextValue "flag" "value" MsgUnitLeaderFlag MsgModifyFlag MsgModifyFlagVar) -- Localization/icon ignored
        ]

flagMaybeText :: (HOI4Info g, Monad m) => Text -> PPT g m (Maybe Text)
flagMaybeText txt = eflag (Just HOI4Country) (Left txt)
-- | Handlers for text/atom pairs
handlersTextAtom :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersTextAtom = Tr.fromList
        [("has_game_rule"               , textAtom "rule" "option" MsgHasRule tryLoc)
        ,("has_core_occupation_modifier" , textAtom "occupied_country_tag" "modifier" MsgHasCoreOccupationModifier flagMaybeText)
        ]

-- | Handlers for special complex statements
handlersSpecialComplex :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersSpecialComplex = Tr.fromList
        [("add_building_construction"    , addBuildingConstruction)
        ,("add_doctrine_cost_reduction"  , addDoctrineCostReduction)
        ,("add_province_modifier"        , addProvinceModifier True)
        ,("remove_province_modifier"     , addProvinceModifier False)
        ,("add_equipment_to_stockpile"   , addEquipment)
        ,("add_named_threat"             , addNamedThreat)
        ,("add_opinion_modifier"         , opinion MsgAddOpinion MsgAddOpinionDur)
        ,("add_tech_bonus"               , addTechBonus)
        ,("add_to_war"                   , addToWar)
        ,("annex_country"                , annexCountry)
        ,("reverse_add_opinion_modifier" , opinion MsgReverseAddOpinion MsgReverseAddOpinionDur)
        ,("build_railway"                , buildRailway)
        ,("can_build_railway"            , canBuildRailway)
        ,("create_equipment_variant"     , createEquipmentVariant)
        ,("create_wargoal"               , createWargoal)
        ,("create_unit"                  , createUnit)
        ,("custom_trigger_tooltip"       , customTriggerTooltip)
        ,("country_event"                , triggerEvent MsgCountryEvent)
        ,("declare_war_on"               , declareWarOn)
        ,("free_building_slots"          , freeBuildingSlots)
        ,("has_completed_focus"          , handleFocus MsgHasCompletedFocus)
        ,("complete_national_focus"      , handleFocus MsgCompleteNationalFocus)
        ,("unlock_national_focus"        , handleFocus MsgUnlockNationalFocus)
        ,("focus"                        , handleFocus MsgFocus) -- used in pre-requisite for focuses
        ,("focus_progress"               , focusProgress MsgFocusProgress)
        ,("uncomplete_national_focus"    , focusUncomplete MsgUncompleteNationalFocus)
        ,("has_army_size"                , hasArmySize)
        ,("has_navy_size"                , hasNavySize)
        ,("has_opinion"                  , hasOpinion MsgHasOpinion)
        ,("has_country_leader"           , hasCountryLeader)
        ,("is_power_balance_in_range"    , powerBalanceRange)
        ,("add_opinion_modifier"         , opinion MsgAddOpinion (\modid what who _years -> MsgAddOpinion modid what who))
        ,("load_focus_tree"              , loadFocusTree)
        ,("modify_building_resources"    , modifyBuildingResources)
        ,("news_event"                   , triggerEvent MsgNewsEvent)
        ,("naval_strength_comparison"    , navalStrengthComparison)
        ,("release_autonomy"             , setAutonomy MsgReleaseAutonomy)
        ,("remove_opinion_modifier"      , opinion MsgRemoveOpinionMod (\modid what who _years -> MsgRemoveOpinionMod modid what who))
        ,("set_autonomy"                 , setAutonomy MsgSetAutonomy)
        ,("set_building_level"           , setBuildingLevel)
        ,("set_politics"                 , setPolitics)
        ,("set_party_name"               , setPartyName)
        ,("start_civil_war"              , startCivilWar)
        ,("start_border_war"             , startBorderWar)
        ,("state_event"                  , triggerEvent MsgStateEvent)
        ,("unit_leader_event"            , triggerEvent MsgUnitLeaderEvent)
        ,("operative_leader_event"       , triggerEvent MsgOperativeEvent)
        -- flags
        ,("set_character_flag"           , setFlag MsgCharacterFlag)
        ,("set_country_flag"             , setFlag MsgCountryFlag)
        ,("set_global_flag"              , setFlag MsgGlobalFlag)
        ,("set_state_flag"               , setFlag MsgStateFlag)
        ,("set_unit_leader_flag"         , setFlag MsgUnitLeaderFlag)
        ,("has_character_flag"           , hasFlag MsgCharacterFlag)
        ,("has_country_flag"             , hasFlag MsgCountryFlag)
        ,("has_global_flag"              , hasFlag MsgGlobalFlag)
        ,("has_state_flag"               , hasFlag MsgStateFlag)
        ,("has_unit_leader_flag"         , hasFlag MsgUnitLeaderFlag)

        ,("set_nationality"              , setNationality)

        -- Effects
        -- simpleEffectAtom and simpleEffectNum

        -- Variables
        ,("set_variable"                 , setVariable MsgSetVariable MsgSetVariableVal)
        ,("set_temp_variable"            , setVariable MsgSetTempVariable MsgSetTempVariableVal)
        ,("add_to_variable"              , setVariable MsgAddVariable MsgAddVariableVal)
        ,("add_to_temp_variable"         , setVariable MsgAddTempVariable MsgAddTempVariableVal)
        ,("subtract_from_variable"       , setVariable MsgSubVariable MsgSubVariableVal)
        ,("subtract_from_temp_variable"  , setVariable MsgSubTempVariable MsgSubTempVariableVal)
        ,("multiply_variable"            , setVariable MsgMulVariable MsgMulVariableVal)
        ,("multiply_temp_variable"       , setVariable MsgMulTempVariable MsgMulTempVariableVal)
        ,("divide_variable"              , setVariable MsgDivVariable MsgDivVariableVal)
        ,("divide_temp_variable"         , setVariable MsgDivTempVariable MsgDivTempVariableVal)
        ,("check_variable"               , checkVariable MsgCheckVariable MsgCheckVariableVal)
        ,("clamp_variable"               , clampVariable MsgClampVariableValVal MsgClampVariableValVar MsgClampVariableVarVal MsgClampVariableVarVar)
        ,("clamp_temp_variable"          , clampVariable MsgClampTempVariableValVal MsgClampTempVariableValVar MsgClampTempVariableVarVal MsgClampTempVariableVarVar)
        ,("is_variable_equal"            , setVariable MsgEquVariable MsgEquVariableVal)
        ,("export_to_variable"           , exportVariable)
        ,("round_variable"              , withNonlocAtom MsgRoundVariable)
        ,("round_temp_variable"         , withNonlocAtom MsgRoundTempVariable)
        ,("clear_variable"              , withNonlocAtom MsgClearVariable)
        ,("has_variable"                , withNonlocAtom MsgHasVariable)

        --decisions
        ,("activate_decision"            , locandid MsgActivateDecision)
        ,("remove_decision"              , locandid MsgRemoveDecision)
        ,("activate_mission"             , locandid MsgActivateMission)
        ,("remove_mission"               , locandid MsgRemoveMission)
        ,("has_active_mission"           , locandid MsgHasActiveMission)
        ,("activate_targeted_decision"   , textAtomKey "target" "decision" MsgActivateTargetedDecision flagMaybeText)
        ,("remove_targeted_decision"     , textAtomKey "target" "decision" MsgRemoveTargetedDecision flagMaybeText)
        ,("unlock_decision_category_tooltip" , withLocAtom MsgUnlockDecisionCategoryTooltip)
        ,("unlock_decision_tooltip"       , unlockDecisionTooltip)
        ,("activate_mission_tooltip"      , withLocAtom MsgActivateMissionTooltip)
        ,("add_days_remove"              , textValueKey "decision" "days" MsgAddDaysRemove MsgAddDaysRemoveVar)
        ,("add_days_mission_timeout"     , textValueKey "mission" "days" MsgAddDaysMissionTimeout MsgAddDaysMissionTimeoutVar)
        ]

-- | Handlers for idea groups
handlersIdeas :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersIdeas = Tr.fromList
        [("has_idea"                    , handleIdeas False MsgHasIdea)
        ,("add_ideas"                   , handleIdeas True MsgAddIdea)
        ,("remove_ideas"                , handleIdeas False MsgRemoveIdea)
        ,("add_timed_idea"              , handleTimedIdeas MsgAddTimedIdea)
        ,("modify_timed_idea"           , handleTimedIdeas MsgModifyTimedIdea)
        ,("swap_ideas"                  , handleSwapIdeas)
        ,("show_ideas_tooltip"          , showIdea)
        ]

-- | Handlers for miscellaneous statements
handlersMisc :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersMisc = Tr.fromList
        [("add_ace"                     , addAce)
        ,("add_ai_strategy"             , rhsIgnored MsgAddAiStrategy)
        ,("add_autonomy_ratio"          , addAutonomyRatio MsgAddAutonomyRatio MsgAddAutonomyRatioVar)
        ,("add_autonomy_score"          , addAutonomyRatio MsgAddAutonomyScore MsgAddAutonomyScoreVar)
        ,("add_field_marshal_role"      , addFieldMarshalRole MsgAddFieldMarshalRole)
        ,("create_field_marshal"        , addFieldMarshalRole MsgAddFieldMarshalRole) -- deprecated
        ,("add_corps_commander_role"    , addFieldMarshalRole MsgAddCorpsCommanderRole)
        ,("create_corps_commander"      , addFieldMarshalRole MsgAddCorpsCommanderRole) -- deprecated
        ,("add_naval_commander_role"    , addFieldMarshalRole MsgAddNavalCommanderRole)
        ,("create_navy_leader"          , addFieldMarshalRole MsgAddNavalCommanderRole) -- deprecated
        ,("add_advisor_role"            , addAdvisorRole)
        ,("remove_advisor_role"         , removeAdvisorRole)
        ,("add_country_leader_role"     , addLeaderRole)
        ,("create_country_leader"       , createLeader)
        ,("create_operative_leader"     , createOperativeLeader)
        ,("promote_character"           , promoteCharacter)
        ,("damage_building"             , damageBuilding)
        ,("delete_unit_template_and_units" , deleteUnits MsgDeleteUnitTemplateAndunits)
        ,("delete_units"                , deleteUnits MsgDeleteUnits)
        ,("division_template"           , divisionTemplate)
        ,("army_manpower_in_state"          , divisionsInState MsgArmyManpowerInState)
        ,("divisions_in_state"          , divisionsInState MsgDivisionsInState)
        ,("divisions_in_border_state"   , divisionsInState MsgDivisionsInBorderState)
        ,("add_country_leader_trait"    , addRemoveLeaderTrait MsgAddCountryLeaderTrait)
        ,("remove_country_leader_trait" , addRemoveLeaderTrait MsgRemoveCountryLeaderTrait)
        ,("add_unit_leader_trait"       , addRemoveUnitTrait MsgAddUnitLeaderTrait)
        ,("remove_unit_leader_trait"    , addRemoveUnitTrait MsgRemoveUnitLeaderTrait)
        ,("add_timed_unit_leader_trait" , addTimedTrait)
        ,("swap_ruler_traits"           , swapLeaderTrait)
        ,("swap_country_leader_traits"  , swapLeaderTrait)
        ,("has_trait"                   , withLocAtom MsgHasTrait)
        ,("add_resource"                , addResource)
        ,("date"                        , handleDate "After" "Before")
        ,("has_start_date"              , handleDate "Game initially started after" "Game initially started before")
        ,("random"                      , random)
        ,("random_list"                 , randomList)
        -- Special
        ,("add_trait"                   , handleTrait True)
        ,("remove_trait"                , handleTrait False)
        ,("diplomatic_relation" , diplomaticRelation)
        ,("give_resource_rights" , giveResourceRights)
        ,("has_character"       , withCharacter MsgHasCharacter)
        ,("retire_character"    , withCharacter MsgRetireCharacter)
        ,("has_dlc"             , hasDlc)
        ,("has_wargoal_against" , hasWarGoalAgainst)
        ,("region"              , withRegion)
        ,("send_equipment"      , sendEquipment)
        ,("set_capital"         , setCapital MsgSetCapital)
        ,("set_character_name"  , setCharacterName)
        ,("set_popularities"    , setPopularities)
        ,("set_rule"            , setRule MsgSetRule)
        ,("set_technology"      , setTechnology)
        ]

-- | Handlers for ignored statements
handlersIgnored :: (HOI4Info g, Monad m) => Trie (StatementHandler g m)
handlersIgnored = Tr.fromList
        [("custom_tooltip", return $ return [])
        ,("effect_tooltip", return $ return []) -- shows the effects but doesn't execute them, don't know if I want it to show up in the parser
        ,("goto"          , return $ return [])
        ,("log"           , return $ return [])
        ,("required_personality", return $ return[]) -- From the 1.30 patch notes: "The required_personality field will now be ignored"
        ,("highlight"     , return $ return [])
        ,("picture"       , return $ return []) -- Some modifiers have custom pictures
        ]

-- | Extract the appropriate message(s) from a single statement. Note that this
-- may produce many lines (via 'ppMany'), since some statements are compound.
ppOne :: (HOI4Info g, Monad m) => StatementHandler g m
ppOne stmt@[pdx| %lhs = %rhs |] = ppOne' stmt lhs rhs
ppOne stmt@[pdx| %lhs > %rhs |] = ppOne' stmt lhs rhs
ppOne stmt@[pdx| %lhs < %rhs |] = ppOne' stmt lhs rhs
ppOne stmt = preStatement stmt
ppOne' :: (HOI4Info g, Monad m) =>
    GenericStatement
    -> Lhs lhs
    -> Rhs Void Void
    -> PPT g m IndentedMessages
ppOne' stmt lhs rhs = case lhs of
    GenericLhs label _ -> case Tr.lookup (TE.encodeUtf8 (T.toLower label)) ppHandlers of
        Just handler -> handler stmt
        -- default
        Nothing -> if isTag label
             then case rhs of
                CompoundRhs scr ->
                    withCurrentIndent $ \_ -> do -- force indent level at least 1
                        lflag <- plainMsg' . (<> ":") =<< flagText (Just HOI4Country) label
                        scriptMsgs <- scope HOI4Country $ ppMany scr
                        return (lflag : scriptMsgs)
                _ -> preStatement stmt
             else case rhs of
                CompoundRhs scr -> do
                    characters <- getCharacters
                    case HM.lookup label characters of
                        Just charid -> withCurrentIndent $ \_ -> do  -- force indent level at least 1
                            lchar <- plainMsg' (chaName charid <> ":")
                            scriptMsgs <- scope HOI4ScopeCharacter $ ppMany scr
                            return (lchar : scriptMsgs)
                        _
                            | any (`T.isSuffixOf` label) [".owner",".OWNER",".Owner"] -> withCurrentIndent $ \_ -> do -- force indent level at least 1
                                    let labelstrip
                                            | ".owner" `T.isSuffixOf` label = fromMaybe "<!--CHECK SCRIPT-->" (T.stripSuffix ".owner" label)
                                            | ".Owner" `T.isSuffixOf` label = fromMaybe "<!--CHECK SCRIPT-->" (T.stripSuffix ".Owner" label)
                                            | ".OWNER" `T.isSuffixOf` label = fromMaybe "<!--CHECK SCRIPT-->" (T.stripSuffix ".OWNER" label)
                                            | otherwise = label
                                    stateloc <-
                                        if all isDigit $ T.unpack labelstrip
                                        then getStateLoc $ read (T.unpack labelstrip)
                                        else do
                                            mstate <- eGetState (Left labelstrip)
                                            return $ fromMaybe "<!--CHECK SCRIPT-->" mstate
                                    lowner <- msgToPP' $ MsgOwnerOfSCOPE stateloc
                                    scriptMsgs <- scope HOI4Country $ ppMany scr
                                    return (lowner : scriptMsgs)
                            | otherwise -> preStatement stmt
                GenericRhs t []
                    | T.toLower t == "no"|| T.toLower t == "yes" -> do
                        scripteffect <- getScriptedEffects
                        scripttrigger <- getScriptedTriggers
                        case HM.lookup label scripteffect of
                            Just effect -> plainStatement "Scripted Effect: " stmt
                            _ -> case HM.lookup label scripttrigger of
                                Just trigger -> plainStatement "Scripted Trigger: " stmt
                                _ -> preStatement stmt
                _ -> preStatement stmt
    AtLhs _ -> return [] -- don't know how to handle these
    IntLhs n -> do -- Treat as a province tag
        case rhs of
            CompoundRhs scr -> do
                        state_loc <- getStateLoc n
                        header <- msgToPP (MsgState state_loc)
                        scriptMsgs <- scope HOI4ScopeState $ ppMany scr
                        return (header ++ scriptMsgs)
            _ -> preStatement stmt
    CustomLhs _ -> preStatement stmt


-- | Try to extract one matching statement
extractStmt :: (a -> Bool) -> [a] -> (Maybe a, [a])
extractStmt p xs = extractStmt' p xs []
    where
        extractStmt' _ [] acc = (Nothing, acc)
        extractStmt' p (x:xs) acc =
            if p x then
                (Just x, acc++xs)
            else
                extractStmt' p xs (acc++[x])

-- | Predicate for matching text on the left hand side
matchLhsText :: Text -> GenericStatement -> Bool
matchLhsText t s@[pdx| $lhs = %_ |] | t == lhs = True
matchLhsText t s@[pdx| $lhs < %_ |] | t == lhs = True
matchLhsText t s@[pdx| $lhs > %_ |] | t == lhs = True
matchLhsText _ _ = False

-- | Predicate for matching text on boths sides
matchExactText :: Text -> Text -> GenericStatement -> Bool
matchExactText l r s@[pdx| $lhs = $rhs |] | l == lhs && r == T.toLower rhs = True
matchExactText _ _ _ = False
