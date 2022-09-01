{-|
Module      : EU4.Common
Description : Message handler for Europa Universalis IV
-}
module EU4.Common (
        ppScript
    ,   pp_mtth
    ,   ppOne
    ,   ppMany
    ,   iconKey, iconFile, iconFileB
    ,   AIWillDo (..), AIModifier (..)
    ,   ppAiWillDo, ppAiMod
    ,   extractStmt, matchLhsText, matchExactText
    ,   module EU4.Types
    ) where

import Debug.Trace (trace, traceM)
import Yaml (LocEntry (..))

import Control.Applicative (liftA2)
import Control.Arrow (first)
import Control.Monad (liftM, MonadPlus (..), forM, foldM, join {- temp -}, when)
import Control.Monad.Reader (MonadReader (..), asks)
import Control.Monad.State (MonadState (..), gets)

import Data.Char (isUpper, toUpper, toLower)
import Data.List (foldl', intersperse)
import Data.Maybe (isJust, fromMaybe, listToMaybe)
import Data.Monoid ((<>))
import Data.Foldable (fold)

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
import Messages -- everything
import MessageTools (plural, colourNumSign)
import QQ (pdx)
import SettingsTypes -- everything
import EU4.Handlers -- everything
import EU4.Types -- everything

-- no particular order from here... TODO: organize this!

-- | Format a script as wiki text.
ppScript :: (EU4Info g, Monad m) =>
    GenericScript -> PPT g m Doc
ppScript [] = return "(Nothing)"
ppScript script = imsg2doc =<< ppMany script

flagTextMaybe :: (EU4Info g, Monad m) => Text -> PPT g m (Text,Text)
flagTextMaybe = fmap (\t -> (mempty, t)) . flagText (Just EU4Country)

-- | Extract the appropriate message(s) from a script.
ppMany :: (EU4Info g, Monad m) => GenericScript -> PPT g m IndentedMessages
ppMany scr = indentUp (concat <$> mapM ppOne scr)

-- | Table of handlers for statements. Dispatch on strings is /much/ quicker
-- using a lookup table than a huge @case@ expression, which uses @('==')@ on
-- each one in turn.
--
-- When adding a new statement handler, add it to one of the sections in
-- alphabetical order if possible, and use one of the generic functions for it
-- if applicable.
ppHandlers :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
ppHandlers = foldl' Tr.unionL Tr.empty
    [ handlersRhsIrrelevant
    , handlersNumeric
    , handlersNumericIcons
    , handlersModifiers
    , handlersCompound
    , handlersLocRhs
    , handlersProvince
    , handlersFlagOrProvince
    , handlersNumericOrFlag
    , handlersAdvisorId
    , handlersTypewriter
    , handlersSimpleIcon
    , handlersSimpleFlag
    , handlersFlagOrYesNo
    , handlersIconFlagOrPronoun
    , handlersTagOrProvince -- merge?
    , handlersYesNo
    , handlersNumericOrTag
    , handlersSignedNumeric
    , handlersNumProvinces
    , handlersTextValue
    , handlersTextAtom
    , handlersSpecialComplex
    , handlersRebels
    , handlersIdeaGroups
    , handlersMisc
    , handlersIgnored
    ]

-- | Handlers for statements where RHS is irrelevant (usually "yes")
handlersRhsIrrelevant :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersRhsIrrelevant = Tr.fromList
        [("active_imperial_incident" , rhsAlways "any" MsgAnyActiveTradeNode)
        ,("add_cardinal"             , rhsAlwaysYes MsgAddCardinal)
        ,("add_estate_burghers_loyalty_effect", rhsAlwaysYes (MsgGenericTemplate "add_estate_burghers_loyalty_effect"))
        ,("add_estate_church_loyalty_effect", rhsAlwaysYes (MsgGenericTemplate "add_estate_church_loyalty_effect"))
        ,("add_estate_cossacks_loyalty_effect", rhsAlwaysYes (MsgGenericTemplate "add_estate_loyalty_effect|cossacks"))
        ,("add_estate_dhimmi_loyalty_effect", rhsAlwaysYes (MsgGenericTemplate "add_estate_dhimmi_loyalty_effect"))
        ,("add_estate_jains_loyalty_effect", rhsAlwaysYes (MsgGenericTemplate "add_estate_loyalty_effect|jains"))
        ,("add_estate_nobles_loyalty_effect", rhsAlwaysYes (MsgGenericTemplate "add_estate_nobles_loyalty_effect"))
        ,("add_estate_rajput_loyalty_effect", rhsAlwaysYes (MsgGenericTemplate "add_estate_loyalty_effect|rajputs"))
        ,("add_innovativeness_big_effect", rhsAlwaysYes MsgAddInnovativenessBigEffect)
        ,("add_innovativeness_small_effect", rhsAlwaysYes MsgAddInnovativenessSmallEffect)
        ,("add_loot_from_province_effect", rhsAlwaysYes MsgAddLootFromProvinceEffect)
        ,("add_mandate_effect"     , rhsAlwaysYes MsgAddMandateEffect)
        ,("add_mandate_large_effect", rhsAlwaysYes MsgAddMandateLargeEffect)
        ,("add_meritocracy_effect" , rhsAlwaysYes MsgAddMeritocracyEffect)
        ,("add_meritocracy_large_effect", rhsAlwaysYes MsgAddMeritocracyLargeEffect)
        ,("add_reform_progress_medium_effect", rhsAlwaysYes MsgAddReformProgressMediumEffect)
        ,("add_reform_progress_small_effect", rhsAlwaysYes MsgAddReformProgressSmallEffect)
        ,("add_stability_or_adm_power", rhsAlwaysYes MsgAddStabilityOrAdm)
        ,("boost_bureaucrats_effect", rhsAlwaysYes MsgBoostBureaucratsEffect)
        ,("boost_bureaucrats_large_effect", rhsAlwaysYes MsgBoostBureaucratsLargeEffect)
        ,("boost_eunuchs_effect", rhsAlwaysYes MsgBoostEunuchsEffect)
        ,("boost_eunuchs_large_effect", rhsAlwaysYes MsgBoostEunuchsLargeEffect)
        ,("boost_temples_effect", rhsAlwaysYes MsgBoostTemplesEffect)
        ,("boost_temples_large_effect", rhsAlwaysYes MsgBoostTemplesLargeEffect)
        ,("can_have_center_of_reformation_trigger" , const $ msgToPP MsgCanHaveCenterOfReformation)
        ,("cancel_construction"    , rhsAlwaysYes MsgCancelConstruction) -- Canals
        ,("cb_on_overseas"         , rhsAlwaysYes MsgGainOverseasCB) -- Full Expansion
        ,("cb_on_primitives"       , rhsAlwaysYes MsgGainPrimitivesCB) -- Full Exploration
        ,("cb_on_religious_enemies", rhsAlwaysYes MsgGainReligiousCB) -- Deus Vult
        ,("change_government_to_monarchy"  , rhsAlwaysYes $ MsgChangeGovernment "monarchy")
        ,("change_government_to_republic"  , rhsAlwaysYes $ MsgChangeGovernment "republic")
        ,("change_government_to_theocracy" , rhsAlwaysYes $ MsgChangeGovernment "theocracy")
        ,("check_if_non_state_advisor_effect", const $ msgToPP MsgCheckIfNonStateAdvisorEffect) -- Ignore actual percentages
        ,("clear_previous_primary_cults" , rhsAlwaysYes $ MsgClearPreviousPrimaryCults)
        ,("clear_rebels"           , rhsAlwaysYes MsgClearRebels)
        ,("divorce_consort_effect", rhsAlwaysYes MsgDivorceConsortEffect)
        ,("enable_hre_leagues"     , rhsAlwaysYes MsgEnableHRELeagues)
        ,("erase_advisor_flags_effect", rhsAlwaysYes MsgEnableHRELeagues)
        ,("grant_independence"      , rhsAlwaysYes MsgGrantIndependence)
        ,("has_holy_order_trigger"  , rhsAlwaysYes MsgHasAnyHolyOrder)
        ,("has_border_with_religious_enemy" , rhsAlwaysYes MsgHasBorderWithReligiousEnemy)
        ,("has_river_estuary_trigger", rhsAlwaysYes MsgHasRiverEstuary)
        ,("has_religious_scholars_trigger", rhsAlwaysYes MsgHasScholar)
        ,("has_shia_school_trigger", rhsAlwaysYes MsgHasShiaSchool)
        ,("has_sunni_school_trigger", rhsAlwaysYes MsgHasSunniSchool)
        ,("highest_supply_limit_in_area" , rhsAlwaysYes MsgHighestSupplyLimitInArea)
        ,("highest_value_trade_node", rhsAlwaysYes MsgHighestValueTradeNode)
        ,("increase_heir_adm_effect", rhsAlwaysYes MsgIncreaseHeirAdmEffect)
        ,("increase_heir_dip_effect", rhsAlwaysYes MsgIncreaseHeirDipEffect)
        ,("increase_heir_mil_effect", rhsAlwaysYes MsgIncreaseHeirMilEffect)
        ,("increase_legitimacy_huge_effect"  , rhsAlwaysYes MsgIncreaseLegitimacyHugeEffect)
        ,("increase_legitimacy_medium_effect", rhsAlwaysYes MsgIncreaseLegitimacyMediumEffect)
        ,("increase_legitimacy_small_effect" , rhsAlwaysYes MsgIncreaseLegitimacySmallEffect)
        ,("is_imperial_modifier"   , rhsAlwaysYes MsgIsImperialMod)
        ,("is_janissary_modifier"  , rhsAlwaysYes MsgIsJanissaryMod)
        ,("is_rajput_modifier"     , rhsAlwaysYes MsgIsRajputMod)
        ,("is_subject_other_than_tributary_trigger" , rhsAlwaysYes MsgIsSubjectOtherThanTributary)
        ,("kill_ruler"             , rhsAlwaysYes MsgRulerDies)
        ,("may_agitate_for_liberty", rhsAlwaysYes MsgMayAgitateForLiberty) -- Espionage: Destabilizing Efforts
        ,("may_explore"            , rhsAlwaysYes MsgMayExplore) -- Exploration: Quest for the New World
        ,("may_infiltrate_administration", rhsAlwaysYes MsgMayInfiltrateAdministration) -- Espionage: Espionage
        ,("may_sabotage_reputation", rhsAlwaysYes MsgMaySabotageReputation) -- Espionage: Rumormongering
        ,("may_sow_discontent"     , rhsAlwaysYes MsgMaySowDiscontent) -- Espionage: Destabilizing Efforts
        ,("may_study_technology"   , rhsAlwaysYes MsgMayStudyTech) -- Espionage: Shady Recruitment
        ,("move_capital_effect"    , rhsAlwaysYes MsgMoveCapitalEffect)
        ,("prev_move_capital_effect" , rhsAlwaysYes MsgPrevMoveCapitalEffect)
        ,("set_hre_religion_treaty", rhsAlwaysYes MsgSignWestphalia)
        ,("reduced_stab_impacts"   , rhsAlwaysYes MsgReducedStabImpacts) -- Full Diplomacy
        ,("reduce_estate_burghers_loyalty_effect", rhsAlwaysYes (MsgGenericTemplate "reduce_estate_burghers_loyalty_effect"))
        ,("reduce_estate_church_loyalty_effect", rhsAlwaysYes (MsgGenericTemplate "reduce_estate_church_loyalty_effect"))
        ,("reduce_estate_cossacks_loyalty_effect", rhsAlwaysYes (MsgGenericTemplate "add_estate_loyalty_effect|cossacks|lose"))
        ,("reduce_estate_dhimmi_loyalty_effect", rhsAlwaysYes (MsgGenericTemplate "reduce_estate_dhimmi_loyalty_effect"))
        ,("reduce_estate_jains_loyalty_effect", rhsAlwaysYes (MsgGenericTemplate "add_estate_loyalty_effect|jains|lose"))
        ,("reduce_estate_nobles_loyalty_effect", rhsAlwaysYes (MsgGenericTemplate "reduce_estate_nobles_loyalty_effect"))
        ,("reduce_bureaucrats_effect", rhsAlwaysYes MsgReduceBureaucratsEffect)
        ,("reduce_eunuchs_effect"  , rhsAlwaysYes MsgReduceEunuchsEffect)
        ,("reduce_innovativeness_small_effect", rhsAlwaysYes MsgAddInnovativenessSmallEffect)
        ,("reduce_temples_effect"  , rhsAlwaysYes MsgReduceTemplesEffect)
        ,("reduce_legitimacy_medium_effect", rhsAlwaysYes MsgReduceLegitimacyEffect)
        ,("reduce_legitimacy_small_effect", rhsAlwaysYes MsgReduceLegitimacySmallEffect)
        ,("reduce_mandate_effect", rhsAlwaysYes MsgReduceMandateEffect)
        ,("reduce_mandate_large_effect", rhsAlwaysYes MsgReduceMandateLargeEffect)
        ,("reduce_meritocracy_effect", rhsAlwaysYes MsgReduceMeritocracyEffect)
        ,("reduce_meritocracy_large_effect", rhsAlwaysYes MsgReduceMeritocracyLargeEffect)
        ,("reduce_reform_progress_small_effect", rhsAlwaysYes MsgReduceReformProgressSmallEffect)
        ,("reduce_reform_progress_medium_effect", rhsAlwaysYes MsgReduceReformProgressMediumEffect)
        ,("reduce_reform_progress_big_effect", rhsAlwaysYes MsgReduceReformProgressBigEffect)
        ,("remove_advisor_adm_effect", rhsAlwaysYes MsgRemoveAdvisorAdmEffect) -- "The currently employed administrative advisor leaves the country's court."
        ,("remove_cardinal"          , rhsAlwaysYes MsgLoseCardinal)
        ,("remove_consort"           , rhsAlwaysYes MsgRemoveConsort)
        ,("remove_heir"              , rhsAlwaysEmptyCompound MsgHeirRemoved)
        ,("remove_non_electors_emperors_from_empire_effect", rhsAlwaysYes MsgLeaveHRE)
        ,("same_govt_as_root_trigger" , rhsAlwaysYes MsgSameGovtAsRoot)
        ,("sea_repair"             , rhsAlwaysYes MsgGainSeaRepair) -- Full Maritime
        ,("set_estate_led_regency_privilege" , rhsAlways "random" MsgSetEstateLedRegencyPrivilegeRandom) -- Only random used in 1.31.3
        ,("swap_free_idea_group"     , rhsAlwaysYes MsgSwapFreeIdeaGroup)
        ,("swap_non_generic_missions" , rhsAlwaysYes MsgGainNewMissions)
        ,("auto_explore_adjacent_to_colony", rhsAlwaysYes MsgAutoExploreAdjacentToColony)
        ,("can_fabricate_for_vassals", rhsAlwaysYes MsgCanFabricateForVassals)
        ,("idea_claim_colonies"    , rhsAlwaysYes MsgIdeaClaimColonies)
        ,("may_establish_frontier" , rhsAlwaysYes MsgMayEstablishFrontier)
        ,("may_perform_slave_raid" , rhsAlwaysYes MsgMayPerformSlaveRaid)
        ,("may_perform_slave_raid_on_same_religion", rhsAlwaysYes MsgMayPerformSlaveRaidOnSameReligion)
        ,("may_recruit_female_generals", rhsAlwaysYes MsgMayRecruitFemaleGenerals)
        ,("no_religion_penalty"    , rhsAlwaysYes MsgNoReligionPenalty)
        ,("map_setup"              , rhsAlways "map_setup_random" MsgMapSetupRandom) -- In 1.30.6 all uses are "map_setup = map_setup_random"
        ,("was_never_german_regional_tag_trigger" , rhsAlwaysYes MsgWasNeverGermanReigionalTag)

        -- Various effects from from common/scripted_effects/01_scripted_effects_for_simple_bonuses_penalties.txt
        --
        -- Curia effects
        ,("add_curia_treasur_small_effect" {-sic-} , rhsAlwaysYes (MsgAddCuriaTreasury 25))
        ,("add_curia_treasury_medium_effect"       , rhsAlwaysYes (MsgAddCuriaTreasury 50))
        ,("add_curia_treasury_big_effect"          , rhsAlwaysYes (MsgAddCuriaTreasury 100))
        ,("add_curia_treasury_huge_effect"         , rhsAlwaysYes (MsgAddCuriaTreasury 1000))
        ,("reduce_curia_treasury_medium_effect"    , rhsAlwaysYes (MsgReduceCuriaTreasury (-50)))
        ,("reduce_curia_treasury_big_effect"       , rhsAlwaysYes (MsgReduceCuriaTreasury (-100)))
        ,("reduce_curia_treasury_huge_effect"      , rhsAlwaysYes (MsgReduceCuriaTreasury (-1000)))

        -- Religious currency
        ,("increase_religious_currency_effect"     , rhsAlwaysYes MsgIncreaseReligiousCurrencyEffect)
        ,("reduce_religious_currency_effect"       , rhsAlwaysYes MsgReduceReligiousCurrencyEffect)

        ,("province_is_or_accepts_culture"         , rhsAlwaysYes (MsgGenericText "Culture is accepted by its owner"))
        ,("province_is_buddhist_or_accepts_buddhism", genericTextLines [
                        "Either:"
                        ,"* Province has one of the following religions (which is either the state religion, the syncretic religion, or harmonized):"
                        ,"** {{icon|buddhism}} Theravada"
                        ,"** {{icon|vajrayana}} Vajrayana"
                        ,"** {{icon|mahayana}} Mahayana"
                        ,"* The province and state religion are {{icon|tengri}} Tengri with any Buddhist religion as the syncretic religion."
                        ,"* The province and state religion are {{icon|confucian}} Confucian with a harmonized Buddhist religion."
                        ,"* The province and state religion are one of the following:"
                        ,"** {{icon|hinduism}} Hindu with {{icon|buddha}} Buddha as personal deity"
                        ,"** {{icon|fetishism}} Fetishist with the {{icon|buddhadharma}} Buddhadharma cult"
                        ,"** {{icon|shinto}} Shinto"
                        ,"* The state religion is {{icon|confucian}} Confucian with a harmonized Buddhist religion and the province has another harmonized religion"
                ])
        ]

-- | Handlers for numeric statements
handlersNumeric :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersNumeric = Tr.fromList
        [("add_authority"                    , numeric MsgGainAuth) -- Inti
        ,("add_colonysize"                   , numeric MsgGainColonyPopulation)
        ,("add_construction_progress"        , numeric MsgGainConstructionProgress)
        ,("add_doom"                         , numeric MsgGainDoom)
        ,("add_harmonization_progress"       , numeric MsgGainHarmonizationProgress)
        ,("add_heir_claim"                   , numeric MsgHeirGainClaim)
        ,("add_heir_support"                 , numeric MsgGainHeirSupport) -- elective monarchy
        ,("add_isolationism"                 , numeric MsgAddIsolationism)
        ,("add_next_institution_embracement" , numeric MsgAddNextInstitutionEmbracement)
        ,("add_nationalism"                  , numeric MsgGainYearsOfSeparatism)
        ,("add_trade_node_income"            , numeric MsgAddTradeNodeIcome)
        ,("army_size_percentage"             , numeric MsgArmySizePc) -- Inti?
        ,("authority"                        , numeric MsgAuth) -- Inti?
        ,("change_government_reform_progress", numeric MsgChangeGovernmentReformProgress)
        ,("change_native_size"               , numeric MsgChangeNativeSize)
        ,("change_siege"                     , numeric MsgGainSiegeProgress)
        ,("colonysize"                       , numeric MsgColonySettlers)
        ,("consort_age"                      , numeric MsgConsortAge)
        ,("convert_heir_to_general"          , numeric (MsgConvertHeirGeneral False))
        ,("convert_female_heir_to_general"   , numeric (MsgConvertHeirGeneral True))
        ,("convert_female_ruler_to_general"  , numeric MsgConvertFemaleRulerGeneral)
        ,("crown_land_share"                 , numeric MsgCrownlandShare)
        ,("curia_treasury_income"            , numeric MsgCuriaTreasuryIncome)
        ,("curia_treasury_size"              , numeric MsgCuriaTreasurySize)
        ,("extend_regency"                   , numeric MsgExtendRegency)
        ,("estate_led_regency_influence"     , numeric MsgEstateLedRegencyInfluence)
        ,("estate_led_regency_loyalty"       , numeric MsgEstateLedRegencyLoyalty)
        ,("federation_size"                  , numeric MsgFederationSize)
        ,("had_recent_war"                   , numeric MsgWasAtWar)
        ,("hegemon_strength"                 , numeric MsgHegemonStrength)
        ,("heir_age"                         , numeric MsgHeirAge)
        ,("hre_size"                         , numeric (\s -> if s == 1 then MsgHREExists else MsgHRESize s))
        ,("is_year"                          , numeric MsgYearIs)
        ,("janissary_percentage"             , numeric MsgJanissaryPercentage)
        ,("legitimacy_equivalent"            , numeric MsgLegitimacyEquivalent)
        ,("monarch_lifespan"                 , numeric MsgMonarchLifespan)
        ,("months_since_defection"           , numeric MsgMonthsSinceDefection)
        ,("native_size"                      , numeric MsgNativeSize)
        ,("num_federation_advancements"      , numeric MsgNumFederationAdvancements)
        ,("num_free_building_slots"          , numeric MsgNumFreeBuildingSlots)
        ,("num_of_aspects"                   , numeric MsgNumAspects)
        ,("num_of_buildings_in_province"     , numeric MsgNumBuildings)
        ,("num_of_centers_of_trade"          , numeric MsgNumCentersOfTrade)
        ,("num_of_colonial_subjects"         , numeric MsgNumColonialSubjects)
        ,("num_of_colonies"                  , numeric MsgNumColonies)
        ,("num_of_diplomatic_relations"      , numeric MsgNumDiplomaticRelations)
        ,("num_of_electors"                  , numeric MsgNumElectors)
        ,("num_of_foreign_hre_provinces"     , numeric MsgNumOfForeignHREProvinces)
        ,("num_of_harmonized"                , numeric MsgNumHarmonized)
        ,("num_of_hired_mercenary_companies" , numeric MsgNumOfHiredMercCompanies)
        ,("num_of_janissaries"               , numeric MsgNumJanissaries)
        ,("num_of_loans"                     , numeric MsgNumLoans)
        ,("num_of_mercenaries"               , numeric MsgNumMercs)
        ,("num_of_non_tributary_subjects"    , numeric MsgNumNonTribSubjects)
        ,("num_of_owned_and_controlled_institutions" , numeric MsgNumOwnInstitutionProvinces)
        ,("num_of_ports"                     , numeric MsgNumPorts) -- same as num_of_total_ports?
        ,("num_of_rajput"                    , numeric MsgNumRajput)
        ,("num_of_rebel_armies"              , numeric MsgNumRebelArmies)
        ,("num_of_rebel_controlled_provinces", numeric MsgNumRebelControlledProvinces)
        ,("num_of_streltsy"                  , numeric MsgNumStreltsy)
        ,("num_of_subjects"                  , numeric MsgNumSubjects)
        ,("num_of_times_improved"            , numeric MsgNumTimesImproved)
        ,("num_of_times_improved_by_owner"   , numeric MsgNumTimesImprovedByOwner)
        ,("num_of_times_used_transfer_development" , numeric MsgNumTimesUsedTransferDevelopment)
        ,("num_of_total_ports"               , numeric MsgNumPorts) -- same as num_of_ports?
        ,("num_of_trade_embargos"            , numeric MsgNumEmbargoes)
        ,("num_of_trusted_allies"            , numeric MsgNumTrustedAllies)
        ,("num_of_unlocked_cults"            , numeric MsgNumUnlockedCults)
        ,("num_of_war_reparations"           , numeric MsgNumOfWarReparations)
        ,("percentage_backing_issue"         , numeric MsgPctBackingParliamentIssue)
        ,("reform_level"                     , numeric MsgReformLevel)
        ,("revolt_percentage"                , numeric MsgRevoltPercentage)
        ,("ruler_age"                        , numeric MsgRulerAge)
        ,("tech_difference"                  , numeric MsgTechDifference)
        ,("trade_company_size"               , numeric MsgTradeCompanySize)
        ,("trade_income_percentage"          , numeric MsgTradeIncomePercentage)
        ,("tributary_state"                  , numeric MsgNumTributaryStates)
        ,("units_in_province"                , numeric MsgUnitsInProvince)
        ,("vassal"                           , numeric MsgHasNumVassals)
        -- Special cases
        ,("legitimacy_or_horde_unity"        , numeric MsgLegitimacyOrHordeUnity)
        ]

-- | Handlers for numeric statements with icons
handlersNumericIcons :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersNumericIcons = Tr.fromList
        [("absolutism"               , numericIcon "absolutism" MsgAbsolutism)
        ,("add_absolutism"           , numericIcon "absolutism" MsgGainAbsolutism)
        ,("add_adm_power"            , numericIcon "adm" MsgGainADM)
        ,("add_army_professionalism" , numericIcon "army professionalism" MsgGainArmyProfessionalism)
        ,("add_army_tradition"       , numericIcon "army tradition" MsgGainAT)
        ,("add_base_manpower"        , numericIcon "manpower" MsgGainBM)
        ,("add_base_production"      , numericIcon "production" MsgGainBP)
        ,("add_base_tax"             , numericIcon "base tax" MsgGainBT)
        ,("add_center_of_trade_level", numericIcon "center of trade" MsgAddCOTLevel)
        ,("add_church_power"         , numericIcon "church power" MsgGainChurchPower)
        ,("add_corruption"           , numericIcon "corruption" MsgGainCorruption)
        ,("add_devastation"          , numericIcon "devastation" MsgGainDevastation)
        ,("add_devotion"             , numericIcon "devotion" MsgGainDevotion)
        ,("add_dip_power"            , numericIcon "dip" MsgGainDIP)
        ,("add_fervor"               , numericIcon "monthly fervor" MsgGainFervor)
        ,("add_harmony"              , numericIcon "yearly harmony" MsgGainHarmony)
        ,("add_horde_unity"          , numericIcon "horde unity" MsgGainHordeUnity)
        ,("add_imperial_influence"   , numericIcon "imperial authority" MsgGainImperialAuthority)
        ,("add_inflation"            , numericIcon "inflation" MsgGainInflation)
        ,("add_karma"                , numericIcon "high karma" MsgGainKarma)
        ,("add_legitimacy"           , numericIcon "legitimacy" MsgGainLegitimacy)
        ,("add_liberty_desire"       , numericIcon "liberty desire" MsgGainLibertyDesire)
        ,("add_local_autonomy"       , numericIcon "local autonomy" MsgGainLocalAutonomy)
        ,("add_mandate"              , numericIcon "mandate" MsgGainMandate)
        ,("add_mercantilism"         , numericIcon "mercantilism" MsgGainMercantilism)
        ,("add_meritocracy"          , numericIcon "meritocracy" MsgGainMeritocracy)
        ,("add_mil_power"            , numericIcon "mil" MsgGainMIL)
        ,("add_militarised_society"  , numericIcon "militarization of state" MsgGainMilitarization)
        ,("add_navy_tradition"       , numericIcon "navy tradition" MsgGainNavyTradition)
        ,("add_papal_influence"      , numericIcon "papal influence" MsgGainPapalInfluence)
        ,("add_patriarch_authority"  , numericIcon "patriarch authority" MsgGainPatAuth)
        ,("add_piety"                , numericIconChange "mysticism" "legalism" MsgGainMysticism MsgGainLegalism)
        ,("add_prestige"             , numericIcon "prestige" MsgGainPrestige)
        ,("add_prosperity"           , numericIcon "prosperity" MsgGainProsperity)
        ,("add_reform_desire"        , numericIcon "reform desire" MsgGainReformDesire)
        ,("add_republican_tradition" , numericIcon "republican tradition" MsgGainRepTrad)
        ,("add_revolutionary_zeal"   , numericIcon "revolutionary zeal" MsgGainRevolutionaryZeal)
        ,("add_scaled_imperial_influence" , numericIcon "imperial authority" MsgGainScaledImperialAuthority)
        ,("add_splendor"             , numericIcon "splendor" MsgGainSplendor)
        ,("add_stability"            , numericIcon "stability" MsgGainStability)
        ,("add_tariff_value"         , numericIcon "gloabl tariffs" MsgAddTariffValue)
        ,("add_treasury"             , numericIcon "ducats" MsgAddTreasury)
        ,("add_tribal_allegiance"    , numericIcon "tribal allegiance" MsgGainTribalAllegiance)
        ,("add_unrest"               , numericIcon "local unrest" MsgAddLocalUnrest)
        ,("add_war_exhaustion"       , numericIcon "war exhaustion" MsgGainWarExhaustion)
        ,("add_yearly_manpower"      , numericIcon "manpower" MsgGainYearlyManpower)
        ,("add_yearly_sailors"       , numericIcon "sailors" MsgGainYearlySailors)
        ,("add_years_of_income"      , numericIcon "ducats" MsgAddYearsOfIncome)
        ,("adm"                      , numericIcon "adm" MsgRulerADM)
        ,("adm_power"                , numericIcon "adm" MsgHasADM)
        ,("administrative_efficiency", numericIconBonus "administrative efficiency" MsgAdminEfficiency MsgAdminEfficiencyBonus)
        ,("army_organiser"           , numericIconLoc "army organizer" "army_organiser" MsgHasAdvisorLevel)
        ,("army_reformer"            , numericIconLoc "army reformer" "army_reformer" MsgHasAdvisorLevel)
        ,("army_tradition"           , numericIconBonusAllowTag "army tradition" MsgArmyTradition MsgArmyTraditionAs MsgYearlyArmyTradition)
        ,("artillery_fraction"       , numericIcon "artillery" MsgArtilleryFraction)
        ,("artist"                   , numericIconLoc "artist" "artist" MsgHasAdvisorLevel)
        ,("average_autonomy"         , numericIcon "autonomy" MsgAverageAutonomy)
        ,("average_unrest"           , numericIcon "unrest" MsgAverageUnrest)
        ,("base_manpower"            , numericIcon "manpower" MsgBaseManpower)
        ,("base_production"          , numericIcon "base production" MsgBaseProduction)
        ,("base_tax"                 , numericIcon "base tax" MsgBaseTax)
        ,("blockade"                 , numericIcon "blockade" MsgBlockade)
        ,("cavalry_fraction"         , numericIcon "cavalry" MsgCavalryFraction)
        ,("center_of_trade"          , numericIcon "cot" MsgCenterOfTrade)
        ,("change_adm"               , numericIcon "adm" MsgGainADMSkill)
        ,("change_dip"               , numericIcon "dip" MsgGainDIPSkill)
        ,("change_heir_adm"          , numericIcon "adm" MsgGainHeirADMSkill)
        ,("change_heir_dip"          , numericIcon "dip" MsgGainHeirDIPSkill)
        ,("change_heir_mil"          , numericIcon "mil" MsgGainHeirMILSkill)
        ,("change_innovativeness"    , numericIcon "innovativeness" MsgChangeInnovativeness)
        ,("change_mil"               , numericIcon "mil" MsgGainMILSkill)
        ,("change_native_ferocity"   , numericIcon "ferocity" MsgChangeNativeFerocity)
        ,("change_native_hostileness" , numericIcon "aggressiveness" MsgChangeNativeAggressiveness)
        ,("change_statists_vs_orangists", numericIconChange "republic" "monarchy" MsgStrengthenStatists MsgStrengthenOrangists)
        ,("church_power"             , numericIcon "church power" MsgChurchPower)
        ,("colonial_governor"        , numericIconLoc "colonial governor" "colonial_governor" MsgHasAdvisorLevel)
        ,("colonist_placement_chance", numericIcon "settler chance" MsgSettlerChance)
        ,("commandant"               , numericIconLoc "commandant" "commandant" MsgHasAdvisorLevel)
        ,("consort_adm"              , numericIcon "adm" MsgConsortADM)
        ,("consort_dip"              , numericIcon "dip" MsgConsortDIP)
        ,("consort_mil"              , numericIcon "mil" MsgConsortMIL)
        ,("corruption"               , numericIcon "corruption" MsgCorruption)
        ,("create_colony"            , numericIcon "global settler increase" MsgCreateColony)
        ,("devastation"              , numericIcon "devastation" MsgDevastation)
        ,("development_cost"         , numericIcon "development cost" MsgDevelCost)
        ,("dip"                      , numericIcon "dip" MsgRulerDIP)
        ,("dip_power"                , numericIcon "adm" MsgHasDIP)
        ,("dip_tech"                 , numericIcon "dip tech" MsgDIPTech)
        ,("diplomat"                 , numericIconLoc "diplomat" "diplomat" MsgHasAdvisorLevel)
        ,("embracement_cost"         , numericIcon "embracement cost" MsgEmbracementCost)
        ,("establish_order_cost"     , numericIcon "establish holy order cost" MsgEstablishOrderCost)
        ,("fervor"                   , numericIcon "fervor" MsgFervor)
        ,("fire_damage"              , numericIcon "land fire damage" MsgLandFireDamage)
        ,("fort_level"               , numericIcon "fort level" MsgFortLevel)
        ,("fortification_expert"     , numericIconLoc "military engineer" "fortification_expert" MsgHasAdvisorLevel)
        ,("global_foreign_trade_power", numericIcon "trade power abroad" MsgTradePowerAbroad)
        ,("global_institution_spread", numericIcon "institution spread" MsgInstitutionSpread)
        ,("global_own_trade_power"   , numericIcon "domestic trade power" MsgDomesticTradePower)
        ,("global_prov_trade_power_modifier", numericIcon "provincial trade power modifier" MsgProvTradePowerMod)
        ,("global_tax_income"        , numericIcon "tax income" MsgGlobalTaxIncome)
        ,("gold_income_percentage"   , numericIcon "gold" MsgGoldIncomePercentage)
        ,("government_reform_progress" , numericIcon "reform progress" MsgGovernmentReformProgress)
        ,("grand_captain"            , numericIconLoc "grand captain" "grand_captain" MsgHasAdvisorLevel)
        ,("grown_by_development"     , numericIcon "development" MsgGrownByDevelopment)
        ,("grown_by_states"          , numericIcon "states" MsgGrownByStates)
        ,("heavy_ship_cost"          , numericIcon "heavy ship cost" MsgHeavyShipCost)
        ,("heir_adm"                 , numericIcon "adm" MsgHeirADM)
        ,("heir_chance"              , numericIcon "chance of new heir" MsgHeirChance)
        ,("heir_dip"                 , numericIcon "dip" MsgHeirDIP)
        ,("heir_mil"                 , numericIcon "mil" MsgHeirMIL)
        ,("harmony"                  , numericIcon "harmony" MsgHarmony)
        ,("horde_unity"              , numericIconBonus "horde unity" MsgHordeUnity MsgYearlyHordeUnity)
        ,("imperial_influence"       , numericIcon "imperial authority" MsgImperialAuthority)
        ,("imperial_mandate"         , numericIconBonus "mandate growth modifier" MsgImperialMandate MsgImperialMandateGrowth)
        ,("innovativeness"           , numericIcon "innovativeness" MsgInnovativeness)
        ,("inquisitor"               , numericIconLoc "inquisitor" "inquisitor" MsgHasAdvisorLevel)
        ,("is_defender_of_faith_of_tier" , numericIcon "dotf" MsgIsDotfTier)
        ,("karma"                    , numericIcon "high karma" MsgKarma)
        ,("legitimacy"               , numericIconBonusAllowTag "legitimacy" MsgLegitimacy MsgLegitimacyAs MsgYearlyLegitimacy)
        ,("liberty_desire"           , numericIconBonus "liberty desire" MsgLibertyDesire MsgLibertyDesireModifier)
        ,("light_ship_fraction"      , numericIcon "light ship" MsgLightShipFraction)
        ,("local_autonomy"           , numericIconBonus "local autonomy" MsgLocalAutonomy MsgMonthlylAutonomyChange)
        ,("local_build_cost"         , numericIcon "local construction cost" MsgLocalConstructionCost)
        ,("local_colonial_growth"    , numericIcon "local settler increase" MsgLocalSettlerIncrease)
        ,("local_culture_conversion_cost", numericIcon "local culture conversion cost" MsgLocalCultureConversionCost)
        ,("local_defensiveness"      , numericIcon "local defensiveness" MsgLocalDefensiveness)
        ,("local_development_cost"   , numericIcon "local development cost" MsgLocalDevelopmentCost )
        ,("local_hostile_movement_speed", numericIcon "local hostile movement speed" MsgLocalHostileMovementSpeed)
        ,("local_institution_spread" , numericIcon "local institution spread" MsgLocalInstitutionSpread)
        ,("local_manpower_modifier"  , numericIcon "local manpower modifier" MsgLocalManpowerMod)
        ,("local_missionary_strength", numericIcon "local missionary strength" MsgLocalMissionaryStrength)
        ,("local_monthly_devastation", numericIcon "local devastation" MsgLocalMonthlyDevastation)
        ,("local_production_efficiency", numericIcon "local production efficiency" MsgLocalProdEff)
        ,("local_state_maintenance_modifier", numericIcon "local state maintenance modifier" MsgLocalStateMaintMod)
        ,("local_tax_modifier"       , numericIcon "local tax modifier" MsgLocalTaxMod)
        ,("local_unrest"             , numericIcon "local unrest" MsgLocalUnrest)
        ,("manpower"                 , numericIcon "manpower" MsgManpower)
        ,("manpower_percentage"      , numericIcon "manpower" MsgManpowerPercentage)
        ,("master_of_mint"           , numericIconLoc "master of mint" "master_of_mint" MsgHasAdvisorLevel)
        ,("max_absolutism"           , numericIcon "max absolutism" MsgMaxAbsolutism)
        ,("max_sailors"              , numericIcon "sailors" MsgMaxSailors)
        ,("mercantilism"             , numericIcon "mercantilism" MsgMercantilism)
        ,("mercenary_discipline"     , numericIcon "mercenary discipline" MsgMercenaryDiscipline)
        ,("meritocracy"              , numericIconBonus "meritocracy" MsgMeritocracy MsgYearlyMeritocracy)
        ,("mil"                      , numericIcon "mil" MsgRulerMIL)
        ,("mil_power"                , numericIcon "adm" MsgHasMIL)
        ,("mil_tech"                 , numericIcon "mil tech" MsgMILTech)
        ,("monthly_adm"              , numericIcon "monthly administrative power" MsgMonthlyADM)
        ,("monthly_dip"              , numericIcon "monthly diplomatic power" MsgMonthlyDIP)
        ,("monthly_mil"              , numericIcon "monthly military power" MsgMonthlyMIL)
        ,("mr_aristocrats_influence" , numericIcon "aristocrats influence" MsgAristocratsInfluence)
        ,("nationalism"              , numericIcon "years of separatism" MsgSeparatism)
        ,("native_ferocity"          , numericIcon "ferocity" MsgNativeFerocity)
        ,("native_hostileness"       , numericIcon "aggressiveness" MsgNativeAggressiveness)
        ,("natural_scientist"        , numericIconLoc "natural scientist" "natural_scientist" MsgHasAdvisorLevel)
        ,("naval_forcelimit"         , numericIcon "naval force limit" MsgNavalForcelimit)
        ,("naval_reformer"           , numericIconLoc "naval reformer" "naval_reformer" MsgHasAdvisorLevel)
        ,("navigator"                , numericIconLoc "navigator" "navigator" MsgHasAdvisorLevel)
        ,("navy_reformer"            , numericIconLoc "naval reformer"  "naval_reformer"MsgHasAdvisorLevel) -- both are used
        ,("navy_size_percentage"     , numericIcon "naval force limit" MsgNavyPercentage)
        ,("navy_tradition"           , numericIconBonus "navy tradition" MsgNavyTradition MsgYearlyNavyTradition)
        ,("num_accepted_cultures"    , numericIcon "max promoted cultures" MsgMaxPromotedCultures)
        ,("num_of_admirals"          , numericIcon "admiral" MsgNumAdmirals)
        ,("num_of_allies"            , numericIcon "alliance" MsgNumAllies)
        ,("num_of_banners"           , numericIcon "banners" MsgNumOfBanners)
        ,("num_of_cardinals"         , numericIcon "cardinal" MsgNumCardinals)
        ,("num_of_colonists"         , numericIcon "colonists" MsgNumColonists)
        ,("num_of_conquistadors"     , numericIcon "conquistador" MsgNumOfConquistadors)
        ,("num_of_explorers"         , numericIcon "explorer" MsgNumOfExplorers)
        ,("num_of_generals"          , numericIcon "general" MsgNumGenerals)
        ,("num_of_generals_with_traits" , numericIcon "general" MsgNumGeneralsWithTrait)
        ,("num_of_merchants"         , numericIcon "merchant" MsgNumMerchants)
        ,("num_of_missionaries"      , numericIcon "missionary" MsgNumMissionaries)
        ,("num_of_royal_marriages"   , numericIcon "royal marriage" MsgNumRoyalMarriages)
        ,("num_of_states"            , numericIcon "states" MsgNumOfStates)
        ,("num_of_unions"            , numericIcon "personal union" MsgNumUnions)
        ,("num_of_vassals"           , numericIcon "vassal" MsgNumVassals) -- includes other subjects?
        ,("overextension_percentage" , numericIcon "overextension" MsgOverextension)
        ,("philosopher"              , numericIconLoc "philosopher" "philosopher" MsgHasAdvisorLevel)
        ,("power_projection"         , numericIcon "power projection" MsgPowerProjection)
        ,("province_trade_power"     , numericIcon "trade power" MsgProvinceTradePower)
        ,("province_trade_power_modifier", numericIcon "local trade power modifier" MsgLocalTradePowerMod)
        ,("province_trade_power_value", numericIcon "local trade power" MsgLocalTradePower)
        ,("quartermaster"            , numericIconLoc "quartermaster" "quartermaster" MsgHasAdvisorLevel)
        ,("raze_power_gain"          , numericIcon "razing power gain" MsgRazingPowerGain)
        ,("recover_navy_morale_speed", numericIcon "recover navy morale speed" MsgRecoverNavyMoraleSpeed)
        ,("recruitmaster"            , numericIconLoc "master recruiter" "recruitmaster" MsgHasAdvisorLevel)
        ,("revolutionary_zeal"       , numericIcon "revolutionary zeal" MsgRevolutionaryZeal)
        ,("share_of_starting_income" , numericIcon "income" MsgShareOfStartingIncome)
        ,("spymaster"                , numericIconLoc "spymaster" "spymaster" MsgHasAdvisorLevel)
        ,("total_base_tax"           , numericIcon "base tax" MsgTotalBaseTax)
        ,("treasurer"                , numericIconLoc "treasurer" "treasurer" MsgHasAdvisorLevel)
        ,("yearly_corruption_increase" , numericIcon "yearly corruption" MsgYearlyCorruptionIncrease)
        -- the number for the following is negated compared to the displayed figure
        ,("reduced_liberty_desire"   , numericIcon "liberty desire in subjects" MsgSubjectLibertyDesire)
        ,("reform_desire"            , numericIcon "reform desire" MsgReformDesire)
        ,("regiment_recruit_speed"   , numericIcon "recruitment time" MsgRecruitmentTime)
        ,("religious_unity"          , numericIconBonus "religious unity" MsgReligiousUnity MsgReligiousUnityBonus)
        ,("republican_tradition"     , numericIconBonus "republican tradition" MsgRepTrad MsgYearlyRepTrad)
        ,("sailors_percentage"       , numericIcon "sailors" MsgSailorsPercentage)
        ,("ship_recruit_speed"       , numericIcon "shipbuilding time" MsgShipbuildingTime)
        ,("shock_damage"             , numericIcon "shock damage" MsgShockDamage)
        ,("stability"                , numericIcon "stability" MsgStability)
        ,("statesman"                , numericIconLoc "statesman" "statesman" MsgHasAdvisorLevel)
        ,("state_maintenance_modifier", numericIcon "state maintenance" MsgStateMaintMod)
        ,("tax_income"               , numericIcon "tax income" MsgTaxIncome)
        ,("theologian"               , numericIconLoc "theologian" "theologian" MsgHasAdvisorLevel)
        ,("total_number_of_cardinals", numericIcon "cardinal" MsgTotalCardinals) -- in the world
        ,("trade_efficiency"         , numericIconBonus "trade efficiency" MsgTradeEfficiency MsgTradeEfficiencyBonus)
        ,("trade_goods_size"         , numericIcon "local goods produced" MsgLocalGoodsProduced)
        ,("trade_goods_size_modifier", numericIcon "local goods produced modifier" MsgLocalGoodsProducedMod)
        ,("trade_value_modifier"     , numericIcon "trade value modifier" MsgTradeValueMod)
        ,("trader"                   , numericIconLoc "trader" "trader" MsgHasAdvisorLevel)
        ,("treasury"                 , numericIcon "ducats" MsgHasDucats)
        ,("tribal_allegiance"        , numericIconBonus "tribal allegiance" MsgTribalAllegiance MsgTribalAllegianceBonus)
        ,("unrest"                   , numericIcon "unrest" MsgUnrest)
        ,("war_exhaustion"           , numericIconBonus "war exhaustion" MsgWarExhaustion MsgMonthlyWarExhaustion)
        ,("war_score"                , numericIcon "war score" MsgWarScore)
        ,("yearly_absolutism"        , numericIcon "absolutism" MsgYearlyAbsolutism)
        ,("yearly_army_professionalism", numericIcon "yearly army professionalism" MsgYearlyArmyProfessionalism)
        ,("yearly_corruption"        , numericIcon "yearly corruption" MsgYearlyCorruption)
        ,("yearly_tribal_allegiance" , numericIcon "tribal allegiance" MsgTribalAllegianceBonus)
        ,("years_of_income"          , numericIcon "ducats" MsgYearsOfIncome)
        -- Used in ideas and other bonuses, omit "gain/lose" in l10n
        ,("accepted_culture_threshold"        , numericIcon "accepted culture threshold" MsgAccCultureThreshold)
        ,("adm_tech_cost_modifier"            , numericIcon "adm tech cost" MsgADMTechCost)
        ,("advisor_cost"                      , numericIcon "advisor cost" MsgAdvisorCost)
        ,("advisor_pool"                      , numericIcon "advisor pool" MsgPossibleAdvisors)
        ,("ae_impact"                         , numericIcon "ae impact" MsgAEImpact)
        ,("army_tradition_decay"              , numericIcon "army tradition decay" MsgArmyTraditionDecay)
        ,("artillery_cost"                    , numericIcon "artillery cost" MsgArtilleryCost)
        ,("artillery_power"                   , numericIcon "artillery power" MsgArtilleryCombatAbility)
        ,("blockade_efficiency"               , numericIcon "blockade efficiency" MsgBlockadeEfficiency)
        ,("build_cost"                        , numericIcon "construction cost" MsgBuildCost)
        ,("caravan_power"                     , numericIcon "caravan power" MsgCaravanPower)
        ,("cavalry_cost"                      , numericIcon "cavalry cost" MsgCavalryCost)
        ,("cavalry_power"                     , numericIcon "cavalry power" MsgCavalryCombatAbility)
        ,("church_power_modifier"             , numericIcon "church power" MsgChurchPowerModifier)
        ,("colonists"                         , numericIcon "colonists" MsgColonists)
        ,("core_creation"                     , numericIcon "core creation cost" MsgCoreCreationCost)
        ,("culture_conversion_cost"           , numericIcon "culture conversion cost" MsgCultureConvCost)
        ,("defensiveness"                     , numericIcon "defensiveness" MsgFortDefense)
        ,("devotion"                          , numericIcon "devotion" MsgYearlyDevotion)
        ,("diplomatic_annexation_cost"        , numericIcon "diplomatic annexation cost" MsgDiploAnnexCost)
        ,("diplomatic_reputation"             , numericIcon "diplomatic reputation" MsgDiploRep)
        ,("diplomatic_upkeep"                 , numericIcon "diplomatic upkeep" MsgDiploRelations)
        ,("diplomats"                         , numericIcon "diplomats" MsgDiplomats)
        ,("dip_tech_cost_modifier"            , numericIcon "dip tech cost" MsgDIPTechCost)
        ,("discipline"                        , numericIcon "discipline" MsgDiscipline)
        ,("discovered_relations_impact"       , numericIcon "discovered relations impact" MsgCovertActionRelationImpact)
        ,("embargo_efficiency"                , numericIcon "embargo efficiency" MsgEmbargoEff)
        ,("enemy_core_creation"               , numericIcon "enemy core creation" MsgHostileCoreCreation)
        ,("envoy_travel_time"                 , numericIcon "envoy travel time" MsgEnvoyTravelTime)
        ,("fabricate_claims_cost"             , numericIcon "cost to fabricate claims" MsgCostToFabricateClaims)
        ,("fabricate_claims_time"             , numericIcon "time to fabricate claims" MsgTimeToFabricateClaims)
        ,("fort_maintenance_modifier"         , numericIcon "fort maintenance" MsgFortMaintenance)
        ,("free_leader_pool"                  , numericIcon "free leader pool" MsgLeadersWithoutUpkeep)
        ,("galley_power"                      , numericIcon "galley power" MsgGalleyCombatAbility)
        ,("garrison_size"                     , numericIcon "garrison size" MsgGarrisonSize)
        ,("global_autonomy"                   , numericIcon "global autonomy" MsgGlobalAutonomy)
        ,("global_colonial_growth"            , numericIcon "global settler increase" MsgGlobalSettlers)
        ,("global_heretic_missionary_strength", numericIcon "global heretic missionary strength" MsgMissionaryStrengthVsHeretics)
        ,("global_manpower_modifier"          , numericIcon "national manpower modifier" MsgNationalManpowerMod)
        ,("global_missionary_strength"        , numericIcon "missionary strength" MsgMissionaryStrength)
        ,("global_regiment_cost"              , numericIcon "regiment cost" MsgRegimentCost)
        ,("global_regiment_recruit_speed" {-sic-}, numericIcon "global regiment recruit speed" MsgRecruitmentTime)
        ,("global_ship_cost"                  , numericIcon "ship cost" MsgGlobalShipCost)
        ,("global_ship_recruit_speed" {- sic -}, numericIcon "shipbuilding time" MsgShipbuildingTime)
        ,("global_ship_repair"                , numericIcon "global ship repair" MsgGlobalShipRepair)
        ,("global_spy_defence"                , numericIcon "global spy defence" MsgGlobalSpyDefence)
        ,("global_tariffs"                    , numericIcon "global tariffs" MsgGlobalTariffs)
        ,("global_tax_modifier"               , numericIcon "global tax modifier" MsgGlobalTaxModifier)
        ,("global_trade_goods_size_modifier"  , numericIcon "goods produced modifier" MsgGoodsProducedMod)
        ,("global_trade_power"                , numericIcon "global trade power" MsgGlobalTradePower)
        ,("global_unrest"                     , numericIcon "national unrest" MsgNationalUnrest)
        ,("heavy_ship_power"                  , numericIcon "heavy ship power" MsgHeavyShipCombatAbility)
        ,("hostile_attrition"                 , numericIcon "attrition for enemies" MsgAttritionForEnemies)
        ,("idea_cost"                         , numericIcon "idea cost" MsgIdeaCost)
        ,("improve_relation_modifier"         , numericIcon "improve relations" MsgImproveRelations)
        ,("infantry_cost"                     , numericIcon "infantry cost" MsgInfantryCost)
        ,("infantry_power"                    , numericIcon "infantry power" MsgInfantryCombatAbility)
        ,("inflation_action_cost"             , numericIcon "reduce inflation cost" MsgReduceInflationCost)
        ,("inflation_reduction"               , numericIcon "inflation reduction" MsgYearlyInflationReduction)
        ,("interest"                          , numericIcon "interest" MsgInterestPerAnnum)
        ,("land_maintenance_modifier"         , numericIcon "land maintenance" MsgLandMaintenanceMod)
        ,("land_attrition"                    , numericIcon "land attrition" MsgLandAttrition)
        ,("land_forcelimit_modifier"          , numericIcon "land forcelimit modifier" MsgLandForcelimitMod)
        ,("leader_land_fire"                  , numericIcon "land leader fire" MsgGainLandLeaderFire)
        ,("leader_land_shock"                 , numericIcon "land leader shock" MsgGainLandLeaderShock)
        ,("leader_land_manuever" {- sic -}    , numericIcon "land leader maneuver" MsgGainLandLeaderManeuver)
        ,("leader_land_siege"                 , numericIcon "leader siege" MsgGainLandLeaderSiege)
        ,("leader_naval_fire"                 , numericIcon "naval leader fire" MsgGainNavalLeaderFire)
        ,("leader_naval_manuever" {- sic -}   , numericIcon "naval leader maneuver" MsgGainNavalLeaderManeuver)
        ,("leader_naval_shock"                , numericIcon "naval leader shock" MsgGainNavalLeaderShock)
        ,("light_ship_power"                  , numericIcon "light ship power" MsgLightShipCombatAbility)
        ,("manpower_recovery_speed"           , numericIcon "manpower recovery speed" MsgManpowerRecoverySpeed)
        ,("mercenary_cost"                    , numericIcon "mercenary cost" MsgMercCost)
        ,("merc_maintenance_modifier"         , numericIcon "merc maintenance modifier" MsgMercMaintenance)
        ,("merchants"                         , numericIcon "merchants" MsgMerchants)
        ,("mil_tech_cost_modifier"            , numericIcon "mil tech cost" MsgMILTechCost)
        ,("missionaries"                      , numericIcon "missionaries" MsgMissionaries)
        ,("missionary_maintenance_cost"       , numericIcon "missionary maintenance cost" MsgMissionaryMaintenanceCost)
        ,("monthly_fervor_increase"           , numericIcon "monthly fervor" MsgMonthlyFervor)
        ,("movement_speed"                    , numericIcon "movement speed" MsgMovementSpeed)
        ,("naval_attrition"                   , numericIcon "naval attrition" MsgNavalAttrition)
        ,("naval_forcelimit_modifier"         , numericIcon "naval forcelimit" MsgNavalForcelimitMod)
        ,("naval_maintenance_modifier"        , numericIcon "naval maintenance" MsgNavalMaintenanceMod)
        ,("naval_morale"                      , numericIcon "morale of navies" MsgMoraleOfNavies)
        ,("navy_tradition"                    , numericIcon "navy tradition" MsgYearlyNavyTradition)
        ,("navy_tradition_decay"              , numericIcon "navy tradition decay" MsgNavyTraditionDecay)
        ,("papal_influence"                   , numericIconBonus "papal influence" MsgPapalInfluence MsgYearlyPapalInfluence)
        ,("possible_mercenaries"              , numericIcon "available mercenaries" MsgAvailableMercs)
        ,("prestige"                          , numericIconBonusAllowTag "prestige" MsgPrestige MsgPrestigeAs MsgYearlyPrestige)
        ,("prestige_decay"                    , numericIcon "prestige decay" MsgPrestigeDecay)
        ,("prestige_from_land"                , numericIcon "prestige from land" MsgPrestigeFromLand)
        ,("prestige_from_naval"               , numericIcon "prestige from naval" MsgPrestigeFromNaval)
        ,("privateer_efficiency"              , numericIcon "privateer efficiency" MsgPrivateerEff)
        ,("production_efficiency"             , numericIconBonusAllowTag "production efficiency" MsgProdEff MsgProdEffAs MsgProdEffBonus)
        ,("prosperity"                        , numericIcon "prosperity" MsgProsperity)
        ,("province_warscore_cost"            , numericIcon "province warscore cost" MsgProvinceWarscoreCost)
        ,("rebel_support_efficiency"          , numericIcon "reform desire" MsgRebelSupportEff)
        ,("recover_army_morale_speed"         , numericIcon "recover army morale speed" MsgRecoverArmyMoraleSpeed)
        ,("reinforce_speed"                   , numericIcon "reinforce speed" MsgReinforceSpeed)
        ,("relations_decay_of_me"             , numericIcon "better relations over time" MsgBetterRelationsOverTime)
        ,("ship_durability"                   , numericIcon "ship durability" MsgShipDurability)
        ,("siege_ability"                     , numericIcon "siege ability" MsgSiegeAbility)
        ,("spy_offence"                       , numericIcon "spy offense" MsgSpyOffense) -- US spelling in game
        ,("stability_cost_modifier"           , numericIcon "stability cost" MsgStabilityCost)
        ,("technology_cost"                   , numericIcon "technology cost" MsgTechCost)
        ,("tolerance_heathen"                 , numericIcon "tolerance heathen" MsgToleranceHeathen)
        ,("tolerance_heretic"                 , numericIcon "tolerance heretic" MsgToleranceHeretic)
        ,("tolerance_own"                     , numericIcon "tolerance own" MsgToleranceTrue)
        ,("trade_range_modifier"              , numericIcon "trade range" MsgTradeRange)
        ,("trade_steering"                    , numericIcon "trade steering" MsgTradeSteering)
        ,("unjustified_demands"               , numericIcon "unjustified demands" MsgUnjustifiedDemands)
        ,("vassal_forcelimit_bonus"           , numericIcon "vassal forcelimit bonus" MsgVassalForcelimitContribution)
        ,("vassal_income"                     , numericIcon "income from vassals" MsgIncomeFromVassals)
        ,("war_exhaustion_cost"               , numericIcon "war exhaustion cost" MsgWarExhaustionCost)
        ,("years_of_nationalism"              , numericIcon "years of separatism" MsgYearsOfSeparatism)
        ,("admiral_cost"                      , numericIcon "admiral cost" MsgAdmiralCost)
        ,("allowed_marine_fraction"           , numericIcon "marines force limit" MsgAllowedMarineFraction)
        ,("allowed_num_of_buildings"          , numericIcon "possible number of buildings" MsgAllowedNumOfBuildings)
        ,("amount_of_banners"                 , numericIcon "possible manchu banners" MsgAmountOfBanners)
        ,("appoint_cardinal_cost"             , numericIcon "appoint cardinal cost" MsgAppointCardinalCost)
        ,("army_tradition_from_battle"        , numericIcon "army tradition from battles" MsgArmyTraditionFromBattle)
        ,("artillery_fire"                    , numericIcon "artillery fire" MsgArtilleryFire)
        ,("autonomy_change_time"              , numericIcon "autonomy change cooldown" MsgAutonomyChangeTime)
        ,("backrow_artillery_damage"          , numericIcon "artillery damage from back row" MsgBackrowArtilleryDamage)
        ,("brahmins_hindu_loyalty_modifier"   , numericIcon "brahmins loyalty" MsgBrahminsHinduLoyaltyModifier)
        ,("brahmins_muslim_loyalty_modifier"  , numericIcon "brahmins loyalty" MsgBrahminsMuslimLoyaltyModifier)
        ,("build_time"                        , numericIcon "construction time" MsgBuildTime)
        ,("burghers_influence_modifier"       , numericIcon "burghers influence" MsgBurghersInfluenceModifier)
        ,("burghers_loyalty_modifier"         , numericIcon "burghers loyalty" MsgBurghersLoyaltyModifier)
        ,("capture_ship_chance"               , numericIcon "chance to capture enemy ships" MsgCaptureShipChance)
        ,("cav_to_inf_ratio"                  , numericIcon "cavalry to infantry ratio" MsgCavToInfRatio)
        ,("cavalry_flanking"                  , numericIcon "cavalry flanking ability" MsgCavalryFlanking)
        ,("center_of_trade_upgrade_cost"      , numericIcon "center of trade upgrade cost" MsgCenterOfTradeUpgradeCost)
        ,("church_loyalty_modifier"           , numericIcon "clergy loyalty" MsgChurchLoyaltyModifier)
        ,("curia_treasury_contribution"       , numericIcon "curia treasury contribution" MsgCuriaTreasuryContribution)
        ,("dhimmi_loyalty_modifier"           , numericIcon "dhimmi loyalty" MsgDhimmiLoyaltyModifier)
        ,("disengagement_chance"              , numericIcon "ship disengagement chance" MsgDisengagementChance)
        ,("drill_decay_modifier"              , numericIcon "regiment drill loss" MsgDrillDecayModifier)
        ,("drill_gain_modifier"               , numericIcon "army drill gain modifier" MsgDrillGainMod)
        ,("enforce_religion_cost"             , numericIcon "cost of enforcing religion through war" MsgEnforceReligionCost)
        ,("expel_minorities_cost"             , numericIcon "expel minorities cost" MsgExpelMinoritiesCost)
        ,("female_advisor_chance"             , numericIcon "female advisor chance" MsgFemaleAdvisorChance)
        ,("fire_damage_received"              , numericIcon "fire damage received" MsgFireDamageReceived)
        ,("flagship_cost"                     , numericIcon "flagship cost" MsgFlagshipCost)
        ,("free_adm_policy"                   , numericIcon "administrative free policies" MsgFreeAdmPolicy)
        ,("free_dip_policy"                   , numericIcon "diplomatic free policies" MsgFreeDipPolicy)
        ,("free_mil_policy"                   , numericIcon "military free policies" MsgFreeMilPolicy)
        ,("galley_cost"                       , numericIcon "galley cost" MsgGalleyCost)
        ,("general_cost"                      , numericIcon "general cost" MsgGeneralCost)
        ,("global_garrison_growth"            , numericIcon "national garrison growth" MsgGlobalGarrisonGrowth)
        ,("global_naval_engagement_modifier"  , numericIcon "global naval engagement" MsgGlobalNavalEngagementModifier)
        ,("global_religious_conversion_resistance", numericIcon "resistance to reformation" MsgGlobalReligiousConversionResistance)
        ,("global_sailors_modifier"           , numericIcon "national sailors modifier" MsgGlobalSailorsModifier)
        ,("global_ship_trade_power"           , numericIcon "ship trade power" MsgGlobalShipTradePower)
        ,("global_supply_limit_modifier"      , numericIcon "supply limit modifier" MsgGlobalSupplyLimitModifier)
        ,("governing_capacity_modifier"       , numericIcon "governing capacity modifier" MsgGoverningCapacityModifier)
        ,("harsh_treatment_cost"              , numericIcon "harsh treatment cost" MsgHarshTreatmentCost)
        ,("imperial_authority"                , numericIcon "imperial authority growth modifier" MsgImperialAuthorityGrowthModifier)
        ,("imperial_authority_value"          , numericIcon "imperial authority modifier" MsgImperialAuthorityValue)
        ,("innovativeness_gain"               , numericIcon "innovativeness gain" MsgInnovativenessGain)
        ,("justify_trade_conflict_cost"       , numericIcon "cost to justify trade conflict" MsgJustifyTradeConflictCost)
        ,("leader_siege"                      , numericIcon "leader siege" MsgLeaderSiege)
        ,("legitimate_subject_elector"        , numericIcon "legitimate subject elector" MsgLegitimateSubjectElector)
        ,("liberty_desire_from_subject_development", numericIcon "liberty desire from subjects development" MsgLibertyDesireFromSubjectDevelopment)
        ,("light_ship_cost"                   , numericIcon "light ship cost" MsgLightShipCost)
        ,("local_friendly_movement_speed"     , numericIcon "friendly movement speed" MsgLocalFriendlyMovementSpeed)
        ,("local_missionary_maintenance_cost" , numericIcon "local missionary maintenance" MsgLocalMissionaryMaintenanceCost)
        ,("local_regiment_cost"               , numericIcon "local regiment cost" MsgLocalRegimentCost)
        ,("local_religious_conversion_resistance", numericIcon "resistance to reformation" MsgLocalReligiousConversionResistance)
        ,("local_sailors_modifier"            , numericIcon "local sailors modifier" MsgLocalSailorsModifier)
        ,("local_ship_cost"                   , numericIcon "local ship cost" MsgLocalShipCost)
        ,("local_ship_repair"                 , numericIcon "local ship repair" MsgLocalShipRepair)
        ,("loot_amount"                       , numericIcon "looting speed" MsgLootAmount)
        ,("max_revolutionary_zeal"            , numericIcon "maximum revolutionary zeal" MsgMaxRevolutionaryZeal)
        ,("mercenary_manpower"                , numericIcon "mercenary manpower" MsgMercenaryManpower)
        ,("migration_cooldown"                , numericIcon "migration cooldown" MsgMigrationCooldown)
        ,("min_autonomy_in_territories"       , numericIcon "minimum autonomy in territories" MsgMinAutonomyInTerritories)
        ,("monarch_diplomatic_power"          , numericIcon "monarch diplomatic skill" MsgMonarchDiplomaticPower)
        ,("monarch_military_power"            , numericIcon "monarch military skill" MsgMonarchMilitaryPower)
        ,("monthly_piety"                     , numericIcon "monthly piety" MsgMonthlyPiety)
        ,("mr_guilds_influence"               , numericIcon "guilds influence" MsgMrGuildsInfluence)
        ,("mr_traders_influence"              , numericIcon "traders influence" MsgMrTradersInfluence)
        ,("native_assimilation"               , numericIcon "native assimilation" MsgNativeAssimilation)
        ,("native_uprising_chance"            , numericIcon "native uprising chance" MsgNativeUprisingChance)
        ,("naval_tradition_from_battle"       , numericIcon "naval tradition from battles" MsgNavalTraditionFromBattle)
        ,("naval_tradition_from_trade"        , numericIcon "naval tradition from protecting trade" MsgNavalTraditionFromTrade)
        ,("nobles_influence_modifier"         , numericIcon "nobility influence" MsgNoblesInfluenceModifier)
        ,("nobles_loyalty_modifier"           , numericIcon "nobility loyalty" MsgNoblesLoyaltyModifier)
        ,("own_coast_naval_combat_bonus"      , numericIcon "naval combat bonus off owned coast" MsgOwnCoastNavalCombatBonus)
        ,("placed_merchant_power"             , numericIcon "merchant trade power" MsgPlacedMerchantPower)
        ,("possible_adm_policy"               , numericIcon "administrative possible policies" MsgPossibleAdmPolicy)
        ,("possible_dip_policy"               , numericIcon "diplomatic possible policies" MsgPossibleDipPolicy)
        ,("possible_mil_policy"               , numericIcon "military possible policies" MsgPossibleMilPolicy)
        ,("possible_policy"                   , numericIcon "possible policies" MsgPossiblePolicy)
        ,("power_projection_from_insults"     , numericIcon "power projection from insults" MsgPowerProjectionFromInsults)
        ,("pr_captains_influence"             , numericIcon "captains influence" MsgPrCaptainsInfluence)
        ,("province_has_center_of_trade_of_level" , numericIcon "center of trade" MsgProviceHasCenterOfTrade)
        ,("reelection_cost"                   , numericIcon "reelection cost" MsgReelectionCost)
        ,("reform_progress_growth"            , numericIcon "reform progress growth" MsgReformProgressGrowth)
        ,("reinforce_cost_modifier"           , numericIcon "reinforce cost" MsgReinforceCostModifier)
        ,("rival_border_fort_maintenance"     , numericIcon "fort maintenance on border with rival" MsgRivalBorderFortMaintenance)
        ,("sailor_maintenance_modifer"        , numericIcon "sailor maintenance" MsgSailorMaintenanceModifer)
        ,("sailors_recovery_speed"            , numericIcon "sailor recovery speed" MsgSailorsRecoverySpeed)
        ,("same_culture_advisor_cost"         , numericIcon "cost of advisors with ruler's culture" MsgSameCultureAdvisorCost)
        ,("shock_damage_received"             , numericIcon "shock damage received" MsgShockDamageReceived)
        ,("siege_blockade_progress"           , numericIcon "blockade impact on siege" MsgSiegeBlockadeProgress)
        ,("special_unit_forcelimit"           , numericIcon "special unit force limit" MsgSpecialUnitForcelimit)
        ,("sunk_ship_morale_hit_recieved"     , numericIcon "morale hit when losing a ship" MsgSunkShipMoraleHitRecieved)
        ,("trade_company_investment_cost"     , numericIcon "trade company investment cost" MsgTradeCompanyInvestmentCost)
        ,("transport_cost"                    , numericIcon "transport cost" MsgTransportCost)
        ,("treasure_fleet_income"             , numericIcon "treasure fleet income" MsgTreasureFleetIncome)
        ,("vaisyas_loyalty_modifier"          , numericIcon "vaishyas loyalty" MsgVaisyasLoyaltyModifier)
        ,("warscore_cost_vs_other_religion"   , numericIcon "war score cost vs other religions" MsgWarscoreCostVsOtherReligion)
        ,("yearly_harmony"                    , numericIcon "yearly harmony increase" MsgYearlyHarmony)
        ,("yearly_revolutionary_zeal"         , numericIcon "revolutionary zeal" MsgYearlyRevolutionaryZeal)
        ,("accept_vassalization_reasons"      , numericIcon "vassalizatation acceptance" MsgAcceptVassalizationReasons)
        ,("adm_advisor_cost"                  , numericIcon "administrative advisor cost" MsgAdmAdvisorCost)
        ,("all_power_cost"                    , numericIcon "all power costs" MsgAllPowerCost)
        ,("available_province_loot"           , numericIcon "available loot" MsgAvailableProvinceLoot)
        ,("cavalry_fire"                      , numericIcon "cavalry fire" MsgCavalryFire)
        ,("church_influence_modifier"         , numericIcon "clergy influence" MsgChurchInfluenceModifier)
        ,("country_admin_power"               , numericIcon "monthly administrative power" MsgCountryAdminPower)
        ,("curia_powers_cost"                 , numericIcon "curia powers cost" MsgCuriaPowersCost)
        ,("dip_advisor_cost"                  , numericIcon "diplomatic advisor cost" MsgDipAdvisorCost)
        ,("expand_administration_cost"        , numericIcon "expand administration cost" MsgExpandAdministrationCost)
        ,("garrison_growth"                   , numericIcon "garrison growth" MsgGarrisonGrowth)
        ,("governing_capacity"                , numericIcon "governing capacity" MsgGoverningCapacity)
        ,("great_project_upgrade_cost"        , numericIcon "great project upgrade cost" MsgGreatProjectUpgradeCost)
        ,("harmonization_speed"               , numericIcon "religious harmonization speed" MsgHarmonizationSpeed)
        ,("infantry_shock"                    , numericIcon "infantry shock" MsgInfantryShock)
        ,("institution_spread_from_true_faith", numericIcon "institution spread in true faith provinces" MsgInstitutionSpreadFromTrueFaith)
        ,("jains_loyalty_modifier"            , numericIcon "jains loyalty" MsgJainsLoyaltyModifier)
        ,("land_forcelimit"                   , numericIconBonus "land force limit" MsgLandForcelimit MsgLandForcelimitIncrease)
        ,("leader_cost"                       , numericIcon "leader cost" MsgLeaderCost)
        ,("local_build_time"                  , numericIcon "local construction time" MsgLocalBuildTime)
        ,("local_core_creation"               , numericIcon "local core-creation cost" MsgLocalCoreCreation)
        ,("local_sailors"                     , numericIcon "sailor increase" MsgLocalSailors)
        ,("mercantilism_cost"                 , numericIcon "cost to promote mercantilism" MsgMercantilismCost)
        ,("migration_cost"                    , numericIcon "migration cost" MsgMigrationCost)
        ,("monarch_admin_power"               , numericIcon "monarch administrative skill" MsgMonarchAdminPower)
        ,("monthly_federation_favor_growth"   , numericIcon "monthly federation favor growth" MsgMonthlyFederationFavorGrowth)
        ,("monthly_karma"                     , numericIcon "monthly karma" MsgMonthlyKarma)
        ,("monthly_militarized_society"       , numericIcon "militarization of state" MsgMonthlyMilitarizedSociety)
        ,("monthly_reform_progress_modifier"  , numericIcon "monthly reform progress modifier" MsgMonthlyReformProgressModifier)
        ,("monthly_splendor"                  , numericIcon "monthly splendor" MsgMonthlySplendor)
        ,("patriarch_authority"               , numericIcon "patriarch authority" MsgPatriarchAuthority)
        ,("promote_culture_cost"              , numericIcon "promote culture cost" MsgPromoteCultureCost)
        ,("reduced_liberty_desire_on_same_continent", numericIcon "liberty desire in same continent subjects" MsgReducedLibertyDesireOnSameContinent)
        ,("rival_change_cost"                 , numericIcon "change rival cost" MsgRivalChangeCost)
        ,("ship_power_propagation"            , numericIcon "ship tradepower propagation" MsgShipPowerPropagation)
        ,("stability_cost_to_declare_war"     , numericIcon "stability hit to declare war" MsgStabilityCostToDeclareWar)
        ,("supply_limit_modifier"             , numericIcon "supply limit modifier" MsgSupplyLimitModifier)
        ,("trade_value"                       , numericIcon "trade value" MsgTradeValue)
        ,("tribal_development_growth"         , numericIcon "tribal development growth" MsgTribalDevelopmentGrowth)
        ,("war_taxes_cost_modifier"           , numericIcon "war taxes cost" MsgWarTaxesCostModifier)
        ,("yearly_patriarch_authority"        , numericIcon "yearly patriarch authority" MsgYearlyPatriarchAuthority)
        ,("yearly_karma_decay"                , numericIcon "yearly karma decay" MsgYearlyKarmaDecay)
        ,("heir_claim"                        , numericIcon "legitimacy" MsgHeirClaim)
        ,("global_heathen_missionary_strength", numericIcon "missionary strength vs heathens" MsgGlobalHeathenMissionaryStrength)
        ,("manpower_in_true_faith_provinces"  , numericIcon "manpower in true faith provinces" MsgManpowerInTrueFaithProvinces)
        ,("blockade_force_required"           , numericIcon "blockade force required" MsgBlockadeForceRequired)
        ,("free_city_imperial_authority"      , numericIcon "imperial authority from free cities" MsgFreeCityImperialAuthority)
        ,("hostile_disembark_speed"           , numericIcon "hostile disembark time" MsgHostileDisembarkSpeed)
        ,("local_religious_unity_contribution", numericIcon "local religious unity contribution" MsgLocalReligiousUnityContribution)
        ,("all_estate_loyalty_equilibrium"    , numericIcon "all estates loyalty equilibrium" MsgAllEstateLoyaltyEquilibrium)
        ,("global_manpower"                   , numericIcon "manpower" MsgGlobalManpower)
        ,("global_prosperity_growth"          , numericIcon "global prosperity growth" MsgGlobalProsperityGrowth)
        ,("hostile_fleet_attrition"           , numericIcon "hostile fleet attrition" MsgHostileFleetAttrition)
        ,("local_gold_depletion_chance_modifier", numericIcon "local gold depletion chance modifier" MsgLocalGoldDepletionChanceModifier)
        ,("local_great_project_upgrade_cost"  , numericIcon "great project upgrade cost" MsgLocalGreatProjectUpgradeCost)
        ,("local_hostile_attrition"           , numericIcon "attrition for enemies" MsgLocalHostileAttrition)
        ,("local_manpower"                    , numericIcon "local manpower" MsgLocalManpower)
        ,("local_prosperity_growth"           , numericIcon "local prosperity growth" MsgLocalProsperityGrowth)
        ,("local_years_of_nationalism"        , numericIcon "years of separatism" MsgLocalYearsOfNationalism)
        ,("min_local_autonomy"                , numericIcon "minimum local autonomy" MsgMinLocalAutonomy)
        ,("monthly_gold_inflation_modifier"   , numericIcon "monthly gold inflation modifier" MsgMonthlyGoldInflationModifier)
        ,("monthly_heir_claim_increase"       , numericIcon "monthly heir claim increase" MsgMonthlyHeirClaimIncrease)
        ,("move_capital_cost_modifier"        , numericIcon "move capital cost modifier" MsgMoveCapitalCostModifier)
        ,("prestige_per_development_from_conversion", numericIcon "prestige per development from missionary" MsgPrestigePerDevelopmentFromConversion)
        ,("state_governing_cost"              , numericIcon "state governing cost" MsgStateGoverningCost)
        ,("tolerance_of_heathens_capacity"    , handleModifier "MODIFIER_TOLERANCE_OF_HEATHENS_CAPACITY" (colourNumSign True))
        ,("tolerance_of_heretics_capacity"    , handleModifier "MODIFIER_TOLERANCE_OF_HERETICS_CAPACITY" (colourNumSign True))
        ,("yearly_doom_reduction"             , handleModifier "MODIFIER_YEARLY_DOOM_REDUCTION" (colourNumSign True))
        ,("yearly_authority"                  , numericIcon "yearly authority" MsgYearlyAuthority)
        ,("monthly_piety_accelerator"         , numericIcon "monthly piety accelerator" MsgMonthlyPietyAccelerator)
        ,("movement_speed_in_fleet_modifier"  , numericIcon "fleet movement speed" MsgMovementSpeedInFleetModifier)
        ]

-- | Handlers for statements pertaining to modifiers
handlersModifiers :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersModifiers = Tr.fromList
        [("add_country_modifier"           , addModifier MsgCountryMod)
        ,("add_disaster_modifier"          , addModifier MsgDisasterMod)
        ,("add_permanent_province_modifier", addModifier MsgPermanentProvMod)
        ,("add_province_modifier"          , addModifier MsgProvMod)
        ,("add_ruler_modifier"             , addModifier MsgRulerMod)
        ,("add_trade_modifier"             , addModifier MsgTradeMod)
        ,("add_province_triggered_modifier", addProvinceTriggeredModifier)
        ,("has_country_modifier"           , withLocAtom2 MsgCountryMod MsgHasModifier)
        ,("has_province_modifier"          , withLocAtom2 MsgProvMod MsgHasModifier)
        ,("has_ruler_modifier"             , withLocAtom2 MsgRulerMod MsgHasModifier)
        ,("has_trade_modifier"             , tradeMod)
        ,("remove_country_modifier"        , withLocAtom2 MsgCountryMod MsgRemoveModifier)
        ,("remove_province_modifier"       , withLocAtom2 MsgProvMod MsgRemoveModifier)
        ]

-- | Handlers for simple compound statements
handlersCompound :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersCompound = Tr.fromList
        -- Note that "any" can mean "all" or "one or more" depending on context.
        [("and" , compoundMessage MsgAllOf)
        ,("root", compoundMessagePronoun)
        ,("from", compoundMessagePronoun)
        ,("prev", compoundMessagePronoun)
        -- no THIS, not used on LHS
        ,("not" , compoundMessage MsgNoneOf)
        ,("or"  , compoundMessage MsgAtLeastOneOf)
        -- Tagged blocks
        ,("event_target", compoundMessageTagged MsgEventTarget (Just EU4From))
        -- There is a semantic distinction between "all" and "every",
        -- namely that the former means "this is true for all <type>" while
        -- the latter means "do this for every <type>."
        ,("all_ally"                , scope EU4Country   . compoundMessage MsgAllAllies)
        ,("all_core_province"       , scope EU4Province  . compoundMessage MsgAllCoreProvince)
        ,("all_country" {- sic -}   , scope EU4Country   . compoundMessage MsgAllCountries)
        ,("all_elector"             , scope EU4Country   . compoundMessage MsgAllElectors)
        ,("all_federation_members"  , scope EU4Country   . compoundMessage MsgAllFederationMembers)
        ,("all_known_country"       , scope EU4Country   . compoundMessage MsgAllKnownCountries)
        ,("all_neighbor_country"    , scope EU4Country   . compoundMessage MsgAllNeighborCountries)
        ,("all_owned_province"      , scope EU4Province  . compoundMessage MsgEveryOwnedProvince)
        ,("all_province"            , scope EU4Province  . compoundMessage MsgAllProvince)
        ,("all_rival_country"       , scope EU4Country   . compoundMessage MsgAllRivalCountries)
        ,("all_subject_country"     , scope EU4Country   . compoundMessage MsgAllSubjectCountries)
        ,("all_trade_node"          , scope EU4TradeNode . compoundMessage MsgAllTradeNodes)
        ,("all_trade_node_member_province" , scope EU4Province . compoundMessage MsgAllTradeNodeProvince)
        ,("any_active_trade_node"   , scope EU4TradeNode . compoundMessage MsgAnyActiveTradeNode)
        ,("any_ally"                , scope EU4Country   . compoundMessage MsgAnyAlly)
        ,("any_army"                ,                      compoundMessage MsgAnyArmy)
        ,("any_core_country"        , scope EU4Country   . compoundMessage MsgAnyCoreCountry) -- used in province scope
        ,("any_core_province"       , scope EU4Province  . compoundMessage MsgAnyCoreProvince)
        ,("any_country"             , scope EU4Country   . compoundMessage MsgAnyCountry)
        ,("any_country_active_in_node" , scope EU4Country . compoundMessage MsgAnyCountryActiveInNode)
        ,("any_empty_neighbor_province", scope EU4Province  . compoundMessage MsgAnyEmptyNeighborProvince)
        ,("any_enemy_country"       , scope EU4Country   . compoundMessage MsgAnyEnemyCountry)
        ,("any_heretic_province"    , scope EU4Province  . compoundMessage MsgAnyHereticProvince)
        ,("any_hired_mercenary_company" ,                  compoundMessage MsgAnyHiredMercenaryCompany) -- TOOD: Need unit scope?
        ,("any_known_country"       , scope EU4Country   . compoundMessage MsgAnyKnownCountry)
        ,("any_neighbor_country"    , scope EU4Country   . compoundMessage MsgAnyNeighborCountry)
        ,("any_neighbor_province"   , scope EU4Province  . compoundMessage MsgAnyNeighborProvince)
        ,("any_owned_province"      , scope EU4Province  . compoundMessage MsgAnyOwnedProvince)
        ,("any_privateering_country", scope EU4TradeNode . compoundMessage MsgAnyPrivateeringCountry)
        ,("any_province"            , scope EU4Province  . compoundMessage MsgAnyProvince)
        ,("any_province_in_state"   , scope EU4Province  . compoundMessage MsgAnyProvinceInState)
        ,("any_rival_country"       , scope EU4Country   . compoundMessage MsgAnyRival)
        ,("any_subject_country"     , scope EU4Country   . compoundMessage MsgAnySubject)
        ,("any_trade_node"          , scope EU4TradeNode . compoundMessage MsgAnyTradeNode)
        ,("any_trade_node_member_country" , scope EU4Country . compoundMessage MsgAnyTradeNodeCountry)
        ,("any_trade_node_member_province" , scope EU4Province . compoundMessage MsgAnyTradeNodeProvince)
        ,("area_for_scope_province" , scope EU4Province  . scopeProvince MsgAreaOfProvince MsgAreaOfProvinceAll)
        ,("capital_scope"           , scope EU4Province  . compoundMessage MsgCapital)
        ,("colonial_parent"         , scope EU4Country   . compoundMessage MsgColonialParent)
        ,("controller"              , scope EU4Country   . compoundMessage MsgController)
        ,("else"                    ,                      compoundMessage MsgElse)
        ,("else_if"                 ,                      compoundMessage MsgElseIf)
        ,("emperor"                 , scope EU4Country   . compoundMessage MsgEmperor)
        ,("every_active_trade_node" , scope EU4TradeNode . compoundMessage MsgEveryActiveTradeNode)
        ,("every_ally"              , scope EU4TradeNode . compoundMessage MsgEveryAlly)
        ,("every_core_country"      , scope EU4Country   . compoundMessage MsgEveryCoreCountry) -- used in province scope
        ,("every_core_province"     , scope EU4Province  . compoundMessage MsgEveryCoreProvince)
        ,("every_country"           , scope EU4Country   . compoundMessage MsgEveryCountry)
        ,("every_enemy_country"     , scope EU4Country   . compoundMessage MsgEveryEnemyCountry)
        ,("every_federation_member" , scope EU4Country   . compoundMessage MsgEveryFederationMember)
        ,("every_heretic_province"  , scope EU4Province  . compoundMessage MsgEveryHereticProvince)
        ,("every_known_country"     , scope EU4Country   . compoundMessage MsgEveryKnownCountry)
        ,("every_neighbor_country"  , scope EU4Country   . compoundMessage MsgEveryNeighborCountry)
        ,("every_neighbor_province" , scope EU4Province  . compoundMessage MsgEveryNeighborProvince)
        ,("every_owned_province"    , scope EU4Province  . compoundMessage MsgEveryOwnedProvince)
        ,("every_province"          , scope EU4Province  . compoundMessage MsgEveryProvince)
        ,("every_rival_country"     , scope EU4Country   . compoundMessage MsgEveryRival)
        ,("every_subject_country"   , scope EU4Country   . compoundMessage MsgEverySubject)
        ,("every_trade_node_member_country" , scope EU4Country . compoundMessage MsgEveryTradeNodeMemberCountry)
        ,("home_province"           ,                      compoundMessage MsgHomeProvince) -- For mercs
        ,("home_trade_node"         , scope EU4TradeNode . compoundMessage MsgHomeTradeNode)
        ,("home_trade_node_effect_scope" , scope EU4TradeNode . compoundMessage MsgHomeTradeNodeEffectScope)
        ,("hidden_effect"           ,                      compoundMessage MsgHiddenEffect)
        ,("hidden_trigger"          ,                      compoundMessage MsgHiddenTrigger)
        ,("if"                      ,                      compoundMessage MsgIf) -- always needs editing
        ,("limit"                   , setIsInEffect False . compoundMessage MsgLimit) -- always needs editing
        ,("location"                , scope EU4Province  . compoundMessage MsgLocation) -- For mercs
        ,("most_province_trade_power", scope EU4Country  . compoundMessage MsgMostProvinceTradePower)
        ,("overlord"                , scope EU4Country   . compoundMessage MsgOverlord)
        ,("owner"                   , scope EU4Country   . compoundMessage MsgOwner)
        ,("random_active_trade_node", scope EU4TradeNode . compoundMessage MsgRandomActiveTradeNode)
        ,("random_ally"             , scope EU4Country   . compoundMessage MsgRandomAlly)
        ,("random_core_country"     , scope EU4Country   . compoundMessage MsgRandomCoreCountry)
        ,("random_core_province"    , scope EU4Country   . compoundMessage MsgRandomCoreProvince)
        ,("random_country"          , scope EU4Country   . compoundMessage MsgRandomCountry)
        ,("random_elector"          , scope EU4Country   . compoundMessage MsgRandomElector)
        ,("random_enemy_country"    , scope EU4Country   . compoundMessage MsgRandomEnemyCountry)
        ,("random_empty_neighbor_province", scope EU4Province . compoundMessage MsgRandomEmptyNeighborProvince)
        ,("random_heretic_province"    , scope EU4Province  . compoundMessage MsgRandomHereticProvince)
        ,("random_hired_mercenary_company" ,                compoundMessage MsgRandomHiredMercenaryCompany) -- TODO: Need unit scope?
        ,("random_known_country"    , scope EU4Country   . compoundMessage MsgRandomKnownCountry)
        ,("random_neighbor_country" , scope EU4Country   . compoundMessage MsgRandomNeighborCountry)
        ,("random_neighbor_province", scope EU4Province  . compoundMessage MsgRandomNeighborProvince)
        ,("random_owned_area"       , scope EU4Province  . compoundMessage MsgRandomOwnedArea)
        ,("random_owned_province"   , scope EU4Province  . compoundMessage MsgRandomOwnedProvince)
        ,("random_privateering_country", scope EU4TradeNode . compoundMessage MsgRandomPrivateeringCountry)
        ,("random_province"         , scope EU4Province  . compoundMessage MsgRandomProvince)
        ,("random_rival_country"    , scope EU4Country   . compoundMessage MsgRandomRival)
        ,("random_subject_country"  , scope EU4Country   . compoundMessage MsgRandomSubjectCountry)
        ,("random_trade_node"       , scope EU4TradeNode . compoundMessage MsgRandomTradeNode)
        ,("random_trade_node_member_province" , scope EU4Province . compoundMessage MsgRandomTradeNodeMemberProvince)
        ,("region_for_scope_province" , scope EU4Province . scopeProvince MsgRegionProvinceScope MsgRegionProvinceScopeAll)
        ,("strongest_trade_power"   , scope EU4Country   . compoundMessage MsgStrongestTradePower) -- always needs editing
        ,("variable_arithmetic_trigger" ,                  compoundMessage MsgVariableArithmeticTrigger)
        ,("while"                   , scope EU4Country   . compoundMessage MsgWhile) -- always needs editing
        ]

withLocAtomTitle msg = withLocAtom' msg (\t -> t <> "_title")

-- | Handlers for simple statements where RHS is a localizable atom
handlersLocRhs :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersLocRhs = Tr.fromList
        [("add_great_project"     , withLocAtom MsgStartConstructingGreatProject)
        ,("add_government_reform" , withLocAtom MsgAddGovernmentReform)
        ,("can_be_overlord"       , withLocAtom MsgCanBeOverlord)
        ,("change_government"     , withLocAtom MsgChangeGovernment)
        ,("change_province_name"  , withLocAtom MsgChangeProvinceName) -- will usually fail localization
        ,("colonial_region"       , withLocAtom MsgColonialRegion)
        ,("complete_mission"      , withLocAtomTitle MsgCompleteMission)
        ,("council_position"      , withLocAtom MsgCouncilPosition)
        ,("current_debate"        , withLocAtom MsgCurrentDebate)
        ,("end_disaster"          , withLocAtom MsgDisasterEnds)
        ,("end_incident"          , withLocAtomTitle MsgEndIncident)
        ,("government"            , withLocAtom MsgGovernmentIs)
        ,("has_advisor"           , withLocAtom MsgHasAdvisor)
        ,("has_active_policy"     , withLocAtom MsgHasActivePolicy)
        ,("has_construction"      , withLocAtom MsgConstructing)
        ,("has_church_aspect"     , withLocAtom MsgHasChurchAspect)
        ,("has_disaster"          , withLocAtom MsgDisasterOngoing)
        ,("has_estate_privilege"  , withLocAtom MsgHasEstatePrivilege)
        ,("has_faction"           , withLocAtom MsgHasFaction)
        ,("has_idea"              , withLocAtom MsgHasIdea)
        ,("has_leader"            , withLocAtom MsgHasLeader) -- will usually fail localization
        ,("has_mission"           , withLocAtomTitle MsgHasMission)
        ,("has_reform"            , withLocAtom MsgHasReform)
        ,("has_terrain"           , withLocAtom MsgHasTerrain)
        ,("has_winter"            , withLocAtom MsgHasWinter)
        ,("hre_reform_passed"     , withLocAtomTitle MsgHREPassedReform)
        ,("in_league"             , withLocAtom MsgInLeague)
        ,("is_incident_active"    , withLocAtomTitle MsgIsIncidentActive)
        ,("is_incident_happened"  , withLocAtomTitle MsgHasIncidentHappened)
        ,("is_incident_possible"  , withLocAtomTitle MsgIsIncidentPossible)
        ,("is_subject_of_type"    , withLocAtomTitle MsgIsSubjectOfType)
        ,("kill_advisor"          , withLocAtom MsgAdvisorDies)
        ,("mission_completed"     , withLocAtomTitle MsgMissionCompleted)
        ,("native_policy"         , withLocAtom MsgNativePolicy)
        ,("override_country_name" , withLocAtom MsgOverrideCountryName)
        ,("remove_advisor"        , withLocAtom MsgLoseAdvisor)
        ,("remove_advisor_by_category" , withLocAtom MsgRemoveAdvisor)
        ,("remove_government_reform" , withLocAtom MsgRemoveGovernmentReform)
        ,("remove_estate_privilege" , withLocAtom MsgRemoveEstatePrivilege)
        ,("rename_capital"        , withLocAtom MsgRenameCapital) -- will usually fail localization
        ,("set_estate_privilege"  , withLocAtom MsgGrantEstatePrivilege)
        ,("set_imperial_incident" , withLocAtom MsgStartHREIncident)
        ,("superregion"           , withLocAtom MsgSuperRegionIs)
        ,("trade_company_region"  , withLocAtom MsgTradeCompanyRegion)
        ]

-- | Handlers for statements whose RHS is a province ID
handlersProvince :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersProvince = Tr.fromList
        [("capital"           , withProvince MsgCapitalIs)
        ,("controls"          , withProvince MsgControls)
        ,("discover_province" , withProvince MsgDiscoverProvince)
        ,("higher_development_than" , withProvince MsgHigherDevelopmentThan)
        ,("owns"              , withProvince MsgOwns)
        ,("owns_core_province", withProvince MsgOwnsCore)
        ,("owns_or_non_sovereign_subject_of" , withProvince MsgOwnsOrNonTribSubject)
        ,("owns_or_vassal_of" , withProvince MsgOwnsOrVassal)
        ,("province_id"       , withProvince MsgProvinceIs)
        ,("set_capital"       , withProvince MsgSetCapital)
        ]

-- | Handlers for statements whose RHS is a flag OR a province ID
-- Also abusable for tag,scope purposes
handlersFlagOrProvince :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersFlagOrProvince = Tr.fromList
        [("add_claim"          , withFlagOrProvince MsgAddClaimFor MsgAddClaimOn)
        ,("add_core"           , withFlagOrProvince MsgGainCore MsgGainCoreProvince)
        ,("add_permanent_claim", withFlagOrProvince MsgGainPermanentClaimCountry MsgGainPermanentClaimProvince)
        ,("cavalry"            , withFlagOrProvince MsgCavalrySpawnsCountry MsgCavalrySpawnsProvince)
        ,("infantry"           , withFlagOrProvince MsgInfantrySpawnsCountry MsgInfantrySpawnsProvince)
        ,("remove_core"        , withFlagOrProvince MsgLoseCoreCountry MsgLoseCoreProvince)
        ,("is_colonial_nation_of" , withFlagOrProvince MsgIsColonialNationOf MsgIsColonialNationOf)
        -- RHS is a flag or province id, but the statement's meaning depends on the scope
        ,("has_discovered"     , withFlagOrProvinceEU4Scope MsgHasDiscovered MsgHasDiscovered MsgDiscoveredBy MsgDiscoveredBy) -- scope sensitive
        ,("same_continent"     , withFlagOrProvinceEU4Scope (MsgSameContinent True True) (MsgSameContinent True False) (MsgSameContinent False True) (MsgSameContinent False False)) -- scope sensitive
        ]

-- | Handlers for statements whose RHS is a number OR a tag/pronoun, with icon
handlersNumericOrFlag :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersNumericOrFlag = Tr.fromList
        [("adm_tech"             , withTagOrNumber "adm tech" MsgADMTech MsgADMTechAs)
        ,("army_size"            , withTagOrNumber "" MsgArmySize MsgArmySizeMatches) -- FIXME: Don't really need icon
        ,("development"          , withTagOrNumber "development" MsgDevelopment MsgDevelopmentAs) -- Can't really be a tag, but it can be "CAPITAL"
        ,("land_morale"          , withTagOrNumber "morale of armies" MsgMoraleOfArmies MsgMoraleOfArmiesAs)
        ,("monthly_income"       , withTagOrNumber "ducats" MsgMonthlyIncome MsgMonthlyIncomeAs)
        ,("navy_size"            , withTagOrNumber "" MsgNavySize MsgNavySizeMatches) -- FIXME: Don't really need icon
        ,("num_of_light_ship"    , withTagOrNumber "light ship" MsgNumLightShips MsgNumLightShipsMatches)
        ,("num_of_heavy_ship"    , withTagOrNumber "heavy ship" MsgNumHeavyShips MsgNumHeavyShipsMatches)
        ,("num_of_galley"        , withTagOrNumber "galley" MsgNumGalleyShips MsgNumGalleyShipsMatches)
        ,("num_of_transport"     , withTagOrNumber "transport" MsgNumTransportShips MsgNumTransportShipsMatches)
        ]

-- TODO: parse advisor files
-- | Handlers for statements whose RHS is an advisor ID
handlersAdvisorId :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersAdvisorId = Tr.fromList
        [("advisor_exists"     , numeric MsgAdvisorExists)
        ,("is_advisor_employed", numeric MsgAdvisorIsEmployed)
        ]

-- | Simple statements whose RHS should be presented as is, in typewriter face
handlersTypewriter :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersTypewriter = Tr.fromList
        [("clr_consort_flag" , withNonlocAtom2 MsgConsortFlag MsgClearFlag)
        ,("clr_country_flag" , withNonlocAtom2 MsgCountryFlag MsgClearFlag)
        ,("clr_global_flag"  , withNonlocAtom2 MsgGlobalFlag MsgClearFlag)
        ,("clr_heir_flag"    , withNonlocAtom2 MsgHeirFlag MsgClearFlag)
        ,("clr_province_flag", withNonlocAtom2 MsgProvinceFlag MsgClearFlag)
        ,("clr_ruler_flag"   , withNonlocAtom2 MsgRulerFlag MsgClearFlag)
        ,("clear_exiled_ruler" , withNonlocAtom MsgClearExiledRuler)
        ,("clear_saved_name" , withNonlocAtom MsgClearSavedName)
        ,("exile_heir_as"    , withNonlocAtom MsgExileHeir)
        ,("exile_ruler_as"   , withNonlocAtom MsgExileRuler)
        ,("exiled_same_dynasty_as_current" , withNonlocAtom MsgExiledRulerSameDynastyAsCurrent)
        ,("has_consort_flag" , withNonlocAtom2 MsgConsortFlag MsgHasFlag)
        ,("has_country_flag" , withNonlocAtom2 MsgCountryFlag MsgHasFlag)
        ,("has_global_flag"  , withNonlocAtom2 MsgGlobalFlag MsgHasFlag)
        ,("has_heir_flag"    , withNonlocAtom2 MsgHeirFlag MsgHasFlag)
        ,("has_province_flag", withNonlocAtom2 MsgProvinceFlag MsgHasFlag)
        ,("has_ruler"        , withNonlocAtom MsgHasRuler)
        ,("has_ruler_flag"   , withNonlocAtom2 MsgRulerFlag MsgHasFlag)
        ,("has_saved_event_target", withNonlocAtom MsgHasSavedEventTarget)
        ,("save_event_target_as", withNonlocAtom MsgSaveEventTargetAs)
        ,("save_global_event_target_as", withNonlocAtom MsgSaveGlobalEventTargetAs)
        ,("set_consort_flag" , withNonlocAtom2 MsgConsortFlag MsgSetFlag)
        ,("set_country_flag" , withNonlocAtom2 MsgCountryFlag MsgSetFlag)
        ,("set_global_flag"  , withNonlocAtom2 MsgGlobalFlag MsgSetFlag)
        ,("set_province_flag", withNonlocAtom2 MsgProvinceFlag MsgSetFlag)
        ,("set_heir"         , withNonlocAtom MsgSetHeir)
        ,("set_heir_flag"    , withNonlocAtom2 MsgHeirFlag MsgSetFlag)
        ,("set_ruler"        , withNonlocAtom MsgSetRuler)
        ,("set_ruler_flag"   , withNonlocAtom2 MsgRulerFlag MsgSetFlag)
        ]

-- | Handlers for simple statements with icon
handlersSimpleIcon :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersSimpleIcon = Tr.fromList
        [("accepted_culture"        , withLocAtomAndIcon "max promoted cultures" MsgAcceptedCulture)
        ,("add_accepted_culture"    , withLocAtomAndIcon "max promoted cultures" MsgAddAcceptedCulture)
        ,("add_building"            , withLocAtomIconBuilding MsgAddBuilding)
        ,("add_harmonized_religion" , withLocAtomIcon MsgAddHarmonizedReligion)
        ,("add_heir_personality"    , withLocAtomIcon (MsgAddHeirPersonality False))
        ,("add_queen_personality"   , withLocAtomIcon (MsgAddConsortPersonality False))
        ,("add_reform_center"       , withLocAtomIcon MsgAddCenterOfReformation)
        ,("add_ruler_personality"   , withLocAtomIcon (MsgAddRulerPersonality False))
        ,("advisor"                 , withLocAtomIcon MsgHasAdvisorType)
        ,("can_build"               , withLocAtomIconBuilding MsgCanBuild)
        ,("change_cult"             , withLocAtomIcon MsgChangeCult)
        ,("change_personal_deity"   , withLocAtomIcon MsgSetPersonalDiety)
        ,("change_technology_group" , withLocAtomIcon MsgChangeTechGroup)
        ,("change_trade_goods"      , withLocAtomIcon MsgChangeGoods)
        ,("change_unit_type"        , withLocAtomIcon MsgChangeUnitType)
        ,("consort_has_personality" , withLocAtomIcon (MsgConsortHasPersonality False))
        ,("create_advisor"          , withLocAtomIcon MsgCreateAdvisor)
        ,("current_age"             , withLocAtomIcon MsgCurrentAge)
        ,("current_icon"            , withLocAtomIcon MsgCurrentIcon)
        ,("enable_religion"         , withLocAtomIcon MsgEnableReligion)
        ,("full_idea_group"         , withLocAtomIcon MsgFullIdeaGroup)
        ,("has_adopted_cult"        , withLocAtomIcon MsgHasAdoptedCult)
        ,("has_building"            , withLocAtomIconBuilding MsgHasBuilding)
        ,("has_climate"             , withLocAtomIcon MsgHasClimate)
        ,("has_estate"              , withLocAtomIconEU4Scope MsgEstateExists MsgHasEstate)
        ,("has_harmonized_with"     , withLocAtomIcon MsgHasHarmonizedWith)
        ,("has_institution"         , withLocAtomIcon MsgHasInstitution)
        ,("has_personal_deity"      , withLocAtomIcon MsgHasPersonalDiety)
        ,("has_unlocked_cult"       , withLocAtomIcon MsgHasUnlockedCult)
        ,("heir_has_personality"    , withLocAtomIcon (MsgHeirHasPersonality False))
        ,("holy_order"              , withLocAtomIcon MsgHasHolyOrder)
        ,("hre_religion"            , withLocAtomIcon MsgHREReligion)
        ,("is_institution_enabled"  , withLocAtomIcon MsgInstitutionEnabled)
        ,("is_monarch_leader"       , withLocAtomAndIcon "ruler general" MsgRulerIsGeneral)
        ,("is_religion_enabled"     , withLocAtomIcon MsgReligionEnabled)
        ,("remove_building"         , withLocAtomIconBuilding MsgRemoveBuilding)
        ,("remove_estate"           , withLocAtomIcon MsgRemoveFromEstate )
        ,("remove_ruler_personality"  , withLocAtomIcon (MsgRemoveRulerPersonality False))
        ,("ruler_has_personality"   , withLocAtomIcon (MsgRulerHasPersonality False))
        ,("secondary_religion"      , withLocAtomIcon MsgSecondaryReligion)
        ,("set_estate"              , withLocAtomIcon MsgAssignToEstate)
        ,("set_hre_heretic_religion", withLocAtomIcon MsgSetHREHereticReligion)
        ,("set_hre_religion"        , withLocAtomIcon MsgSetHREReligion)
        ,("start_estate_agenda"     , withLocAtomIcon MsgStartEstateAgenda)
        ,("technology_group"        , withLocAtomIcon MsgTechGroup)
        ,("unlock_cult"             , withLocAtomIcon MsgUnlockCult)
        ]

-- | Handlers for simple statements with a flag
handlersSimpleFlag :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersSimpleFlag = Tr.fromList
        [("add_claim"               , withFlag MsgGainClaim)
        ,("add_historical_friend"   , withFlag MsgAddHistoricalFriend)
        ,("add_historical_rival"    , withFlag MsgAddHistoricalRival)
        ,("add_truce_with"          , withFlag MsgAddTruceWith)
        ,("adopt_reform_progress"   , withFlag MsgAdoptReformProgress)
        ,("alliance_with"           , withFlag MsgAlliedWith)
        ,("break_union"             , withFlag MsgBreakUnion)
        ,("cede_province"           , withFlag MsgCedeProvinceTo)
        ,("change_controller"       , withFlag MsgChangeController)
        ,("change_tag"              , withFlag MsgChangeTag)
        ,("clear_estate_agenda_cache" , withFlag MsgClearEstateAgendaCache)
        ,("controlled_by"           , withFlag MsgControlledBy)
        ,("country_or_non_sovereign_subject_holds" , withFlag MsgCountryOrNonSovereignSubjectHolds)
        ,("country_or_subject_holds" , withFlag MsgCountryOrSubjectHolds)
        ,("country_or_vassal_holds" , withFlag MsgCountryOrSubjectHolds) -- Legacy version of country_or_subject_holds
        ,("create_alliance"         , withFlag MsgCreateAlliance)
        ,("create_guarantee"        , withFlag MsgCreateGuarantee)
        ,("create_march"            , withFlag MsgCreateMarch)
        ,("create_marriage"         , withFlag MsgCreateMarriage)
        ,("create_union"            , withFlag MsgCreateUnion)
        ,("create_vassal"           , withFlag MsgCreateVassal)
        ,("defensive_war_with"      , withFlag MsgDefensiveWarAgainst)
        ,("discover_country"        , withFlag MsgDiscoverCountry)
        ,("excommunicate"           , withFlag MsgExcommunicate)
        ,("form_coalition_against"  , withFlag MsgFormCoalitionAgainst)
        ,("free_vassal"             , withFlag MsgFreeVassal)
        ,("galley"                  , withFlag MsgGalley)
        ,("guaranteed_by"           , withFlag MsgGuaranteedBy)
        ,("has_guaranteed"          , withFlag MsgHasGuaranteed)
        ,("has_merchant"            , withFlag MsgHasMerchant)
        ,("has_most_province_trade_power" , withFlag MsgHasMostProvinceTradePower)
        ,("has_religious_school_of" , withFlag MsgHasReligiousSchoolOf)
        ,("has_trader"              , withFlag MsgHasTrader)
        ,("heavy_ship"              , withFlag MsgHeavyShip)
        ,("historical_friend_with"  , withFlag MsgHistoricalFriendWith)
        ,("historical_rival_with"   , withFlag MsgHistoricalRivalWith)
        ,("inherit"                 , withFlag MsgInherit)
        ,("has_pillaged_capital_against" , withFlag MsgHasPillagedCapitalAgainst)
        ,("humiliated_by"           , withFlag MsgHumiliatedBy)
        ,("is_capital_of"           , withFlag MsgIsCapitalOf)
        ,("is_enemy"                , scope EU4Country . withFlag MsgIsEnemy)
        ,("is_in_trade_league_with" , withFlag MsgIsInTradeLeagueWith)
        ,("is_league_enemy"         , withFlag MsgIsLeagueEnemy)
        ,("is_league_friend"        , withFlag MsgIsLeagueFriend)
        ,("is_neighbor_of"          , withFlag MsgNeighbors)
        ,("is_origin_of_consort"    , withFlag MsgIsOriginOfConsort)
        ,("is_rival"                , withFlag MsgIsRival)
        ,("is_supporting_independence_of" , withFlag MsgIsSupportingIndependenceOf)
        ,("is_state_core"           , withFlag MsgIsStateCore)
        ,("is_strongest_trade_power", withFlag MsgIsStrongestTradePower)
        ,("is_subject_of"           , withFlag MsgIsSubjectOf)
        ,("is_threat"               , withFlag MsgIsThreat)
        ,("junior_union_with"       , withFlag MsgJuniorUnionWith)
        ,("knows_country"           , withFlag MsgKnowsCountry)
        ,("light_ship"              , withFlag MsgLightShip)
        ,("marriage_with"           , withFlag MsgRoyalMarriageWith)
        ,("offensive_war_with"      , withFlag MsgOffensiveWarAgainst)
        ,("overlord_of"             , withFlag MsgOverlordOf)
        ,("owned_by"                , withFlag MsgOwnedBy)
        ,("preferred_emperor"       , withFlag MsgPreferredEmperor)
        ,("provinces_on_capital_continent_of" , withFlag MsgProvincesOnCapitalContinentOf)
        ,("release"                 , withFlag MsgReleaseVassal)
        ,("remove_claim"            , withFlag MsgRemoveClaim)
        ,("remove_historical_friend" , withFlag MsgRemoveHistoricalFriend)
        ,("remove_historical_rival" , withFlag MsgRemoveHistoricalRival)
        ,("senior_union_with"       , withFlag MsgSeniorUnionWith)
        ,("sieged_by"               , withFlag MsgUnderSiegeBy)
        ,("succession_claim"        , withFlag MsgSuccessionClaim)
        ,("support_independence_of" , withFlag MsgSupportIndependenceOf)
        ,("switch_tag"              , withFlag MsgSwitchTag)
        ,("tag"                     , withFlag MsgCountryIs)
        ,("trade_embargoing"        , withFlag MsgTradeEmbargoing)
        ,("trade_embargo_by"        , withFlag MsgEmbargoedBy)
        ,("truce_with"              , withFlag MsgTruceWith)
        ,("vassal_of"               , withFlag MsgVassalOf)
        ,("vassalize"               , withFlag MsgVassalize)
        ,("war_with"                , withFlag MsgAtWarWith)
        ,("was_tag"                 , withFlag MsgWasTag)
        ,("white_peace"             , withFlag MsgMakeWhitePeace)
        ]

-- | Handlers for simple generic statements with a flag or "yes"/"no"
handlersFlagOrYesNo :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersFlagOrYesNo = Tr.fromList
        [("exists", withFlagOrBool MsgExists MsgCountryExists)
        ]

-- | Handlers for statements whose RHS may be an icon, a flag, a province, or a
-- pronoun (such as ROOT).
handlersIconFlagOrPronoun :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersIconFlagOrPronoun = Tr.fromList
        [("change_culture"   , locAtomTagOrProvince (const MsgChangeCulture) MsgChangeSameCulture)
        -- above is province, below is country - use same messages for both
        ,("change_primary_culture", locAtomTagOrProvince (const MsgChangeCulture) MsgChangeSameCulture)
        ,("change_culture"   , locAtomTagOrProvince (const MsgChangeCulture) MsgChangeSameCulture)
        ,("change_religion"  , iconOrFlag MsgChangeReligion MsgChangeSameReligion Nothing)
        ,("consort_culture"  , locAtomTagOrProvince (const MsgConsortCultureIs) MsgConsortCultureIsSame)
        ,("continent"        , locAtomTagOrProvince (const MsgContinentIs) MsgContinentIsAs)
        ,("culture"          , locAtomTagOrProvince (const MsgCultureIs) MsgCultureIsAs)
        ,("culture_group"    , locAtomTagOrProvince (const MsgCultureIsGroup) MsgCultureGroupAs)
        ,("dominant_culture" , locAtomTagOrProvince (const MsgDominantCultureIs) MsgDominantCultureIsAs)
        ,("dominant_religion", locAtomTagOrProvince MsgDominantReligion MsgDominantReligionAs)
        ,("heir_culture"     , locAtomTagOrProvince (const MsgHeirCultureIs) MsgHeirCultureIsSame)
        ,("heir_nationality" , locAtomTagOrProvince (const MsgHeirNationality) MsgHeirNationalityAs)
        ,("heir_religion"    , locAtomTagOrProvince MsgHeirReligion MsgHeirReligionAs)
        ,("is_core"          , tagOrProvince MsgIsCoreOf MsgHasCoreOn (Just EU4Country))
        ,("is_claim"         , tagOrProvince MsgHasClaim MsgHasClaimOn (Just EU4Country))
        ,("is_harmonizing_with" , locAtomTagOrProvince MsgIsHarmonizingWith MsgIsHarmonizingWithProvince)
        ,("is_permanent_claim" , tagOrProvince MsgIsPermanentClaim MsgHasPermanentClaim (Just EU4Country))
        ,("primary_culture"  , locAtomTagOrProvince (const MsgPrimaryCultureIs) MsgPrimaryCultureIsAs)
        ,("province_religion" , locAtomTagOrProvince MsgProvinceReligion MsgProvinceSameReligion)
        ,("religion"         , locAtomTagOrProvince MsgReligion MsgSameReligion)
        ,("religion_group"   , locAtomTagOrProvince MsgReligionGroup MsgSameReligionGroup)
        ,("ruler_culture"    , iconOrFlag MsgRulerCultureIs MsgRulerCultureIsSame Nothing)
        ,("ruler_religion"   , iconOrFlag MsgRulerReligionIs MsgRulerReligionIsSame Nothing)
        ,("set_consort_culture" , locAtomTagOrProvince (const MsgChangeConsortCulture) MsgChangeConsortSameCulture)
        ,("set_heir_culture" , locAtomTagOrProvince (const MsgChangeHeirCulture) MsgChangeHeirSameCulture)
        ,("set_heir_religion", locAtomTagOrProvince MsgSetHeirReligion MsgSetHeirReligionAs)
        ,("set_ruler_culture" , locAtomTagOrProvince (const MsgChangeRulerCulture) MsgChangeRulerSameCulture)
        ,("set_ruler_religion" , iconOrFlag MsgChangeRulerReligion MsgChangeRulerSameReligion Nothing)
        ,("trade_goods"      , locAtomTagOrProvince MsgProducesGoods MsgProducesSameGoods)
        ]

-- | Handlers for statements whose RHS may be either a tag or a province
handlersTagOrProvince :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersTagOrProvince = Tr.fromList
        [ -- obsolete
        ]

-- | Handlers for yes/no statements
handlersYesNo :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersYesNo = Tr.fromList
        [("ai"                          , withBool MsgIsAIControlled)
        ,("allows_female_emperor"       , withBool MsgFemaleEmperorAllowed)
        ,("always"                      , withBool MsgAlways)
        ,("at_war_with_religious_enemy" , withBool MsgAtWarWithReligiousEnemy)
        ,("back_current_issue"          , withBool MsgBackCurrentIssue)
        ,("can_establish_order"         , withBool MsgCanEstablishHolyOrder)
        ,("elector"                     , withBool MsgElector)
        ,("expelling_minorities"        , withBool MsgExpellingMinorities)
        ,("has_active_debate"           , withBool MsgHasActiveDebate)
        ,("has_any_active_estate_agenda", withBool MsgHasAnyActiveEstateAgenda)
        ,("has_any_disaster"            , withBool MsgHasAnyDisaster)
        ,("has_any_estates"             , withBool MsgHasAnyEstates)
        ,("has_active_fervor"           , withBool MsgHasActiveFervor)
        ,("has_cardinal"                , withBool MsgHasCardinal)
        ,("has_completed_all_reforms_trigger" , withBool MsgHasCompletedAllReforms)
        ,("has_final_tier_reforms_trigger" , withBool MsgHasFinalTierReform)
        ,("has_consort"                 , withBool MsgHasConsort)
        ,("has_consort_regency"         , withBool MsgHasConsortRegency)
        ,("has_custom_ideas"            , withBool MsgHasCustomIdeas)
        ,("has_divert_trade"            , withBool MsgHasDivertTrade)
        ,("has_embargo_rivals"          , withBool MsgHasEmbargoRivals)
        ,("has_empty_adjacent_province" , withBool MsgHasEmptyAdjProvince)
        ,("has_factions"                , withBool MsgHasFactions)
        ,("has_female_consort"          , withBool MsgHasFemaleConsort)
        ,("has_female_heir"             , withBool MsgHasFemaleHeir)
        ,("has_flagship"                , withBool MsgHasFlagship)
        ,("has_foreign_consort"         , withBool MsgHasForeignConsort)
        ,("has_foreign_heir"            , withBool MsgHasForeignHeir)
        ,("has_had_golden_age"          , withBool MsgHasHadGoldenAge)
        ,("has_influencing_fort"        , withBool MsgHasInfluencingFort)
        ,("has_manufactory_trigger"     , withBool MsgHasAnyManufactory)
        ,("has_missionary"              , withBool MsgHasMissionary)
        ,("has_new_dynasty"             , withBool MsgHasNewDynasty)
        ,("has_or_building_flagship"    , withBool MsgHasOrBuildingFlagship)
        ,("has_owner_accepted_culture"  , withBool MsgHasOwnerAcceptedCulture)
        ,("has_owner_culture"           , withBool MsgHasOwnerCulture)
        ,("has_owner_religion"          , withBool MsgHasOwnerReligion)
        ,("has_parliament"              , withBool MsgHasParliament)
        ,("has_port"                    , withBool MsgHasPort)
        ,("has_privateers"              , withBool MsgHasPrivateers)
        ,("has_regency"                 , withBool MsgIsInRegency)
        ,("has_religious_school"        , withBool MsgHasReligiousSchool)
        ,("has_revolution_in_province"  , withBool MsgHasRevolutionInProvince)
        ,("has_scutage"                 , withBool MsgHasScutage)
        ,("has_seat_in_parliament"      , withBool MsgHasSeatInParliament)
        ,("has_secondary_religion"      , withBool MsgHasSecondaryReligion)
        ,("has_send_officers"           , withBool MsgHasSendOfficers)
        ,("has_siege"                   , withBool MsgUnderSiege)
        ,("has_state_patriach"          , withBool MsgHasStatePatriach)
        ,("has_states_general_mechanic" , withBool MsgHasStatesGeneralMechanic)
        ,("has_subsidize_armies"        , withBool MsgHasSubsidizeArmies)
        ,("has_support_loyalists"       , withBool MsgHasSupportLoyalists)
        ,("has_truce"                   , withBool MsgHasTruce)
        ,("has_wartaxes"                , withBool MsgHasWarTaxes)
        ,("hre_leagues_enabled"         , withBool MsgHRELeaguesEnabled)
        ,("hre_religion_locked"         , withBool MsgHREReligionLocked)
        ,("hre_religion_treaty"         , withBool MsgHREWestphalia)
        ,("in_golden_age"               , withBool MsgInGoldenAge)
        ,("is_all_concessions_in_council_taken" , withBool MsgAllConcesssionsTaken)
        ,("is_at_war"                   , withBool MsgAtWar)
        ,("is_backing_current_issue"    , withBool MsgIsBackingCurrentIssue)
        ,("is_bankrupt"                 , withBool MsgIsBankrupt)
        ,("is_blockaded"                , withBool MsgIsBlockaded)
        ,("is_capital"                  , withBool MsgIsCapital)
        ,("is_center_of_revolution"     , withBool MsgIsCenterOfRevolution)
        ,("is_city"                     , withBool MsgIsCity)
        ,("is_colonial_nation"          , withBool MsgIsColonialNation)
        ,("is_colony"                   , withBool MsgIsColony)
        ,("is_council_enabled"          , withBool MsgIsCouncilEnabled)
        ,("is_defender_of_faith"        , withBool MsgIsDefenderOfFaith)
        ,("is_elector"                  , withBool MsgIsElector)
        ,("is_emperor"                  , withBool MsgIsEmperor)
        ,("is_emperor_of_china"         , withBool MsgIsEmperorOfChina)
        ,("is_empty"                    , withBool MsgIsProvinceEmpty)
        ,("is_excommunicated"           , withBool MsgIsExcommunicated)
        ,("is_federation_leader"        , withBool MsgIsFederationLeader)
        ,("is_federation_nation"        , withBool MsgIsFederationNation)
        ,("is_female"                   , withBool MsgIsFemale)
        ,("is_foreign_company"          , withBool MsgIsForeignCompany)
        ,("is_force_converted"          , withBool MsgWasForceConverted)
        ,("is_former_colonial_nation"   , withBool MsgIsFormerColonialNation)
        ,("is_free_or_tributary_trigger", withBool MsgIsFreeOrTributaryTrigger)
        ,("is_great_power"              , withBool MsgIsGreatPower)
        ,("is_heir_leader"              , withBool MsgIsHeirLeader)
        ,("is_in_capital_area"          , withBool MsgIsInCapitalArea)
        ,("is_in_coalition"             , withBool MsgIsInCoalition)
        ,("is_in_deficit"               , withBool MsgIsInDeficit)
        ,("is_in_extended_regency"      , withBool MsgIsInExtendedRegency)
        ,("is_in_league_war"            , withBool MsgIsInLeagueWar)
        ,("is_iroquois"                 , withBool MsgIsIroquois)
        ,("is_island"                   , withBool MsgIsIsland)
        ,("is_league_leader"            , withBool MsgIsLeagueLeader)
        ,("is_lesser_in_union"          , withBool MsgIsLesserInUnion)
        ,("is_looted"                   , withBool MsgIsLooted)
        ,("is_march"                    , withBool MsgIsMarch)
        ,("is_node_in_trade_company_region" , withBool MsgTradeNodeIsInTCRegion)
        ,("is_nomad"                    , withBool MsgIsNomad)
        ,("is_orangists_in_power"       , withBool MsgIsOrangistsInPower)
        ,("is_overseas"                 , withBool MsgIsOverseas)
        ,("is_owned_by_trade_company"   , withBool MsgIsOwnedByTradeCompany)
        ,("is_papal_controller"         , withBool MsgIsPapalController)
        ,("is_part_of_hre"              , withBool MsgIsPartOfHRE)
        ,("is_playing_custom_nation"    , withBool MsgIsCustomNation)
        ,("is_prosperous"               , withBool MsgIsProsperous)
        ,("is_random_new_world"         , withBool MsgRandomNewWorld)
        ,("is_reformation_center"       , withBool MsgIsCenterOfReformation)
        ,("is_religion_reformed"        , withBool MsgReligionReformed)
        ,("is_religious_center_province" , withBool MsgIsReligiousCenterProvince)
        ,("is_revolution_target"        , withBool MsgIsRevolutionTarget)
        ,("is_revolutionary"            , withBool MsgIsRevolutionary)
        ,("is_revolutionary_republic_trigger" , withBool MsgIsRevolutionaryRepublic)
        ,("is_sea"                      , withBool MsgIsSea) -- province or trade node
        ,("is_state"                    , withBool MsgIsState)
        ,("is_statists_in_power"        , withBool MsgIsStatistsInPower)
        ,("is_subject"                  , withBool MsgIsSubject)
        ,("is_territory"                , withBool MsgIsTerritory)
        ,("is_trade_league_leader"      , withBool MsgIsTradeLeagueLeader)
        ,("is_tribal"                   , withBool MsgIsTribal)
        ,("is_tutorial_active"          , withBool MsgIsInTutorial)
        ,("is_vassal"                   , withBool MsgIsVassal)
        ,("is_wasteland"                , withBool MsgIsWasteland)
        ,("luck"                        , withBool MsgLucky)
        ,("normal_or_historical_nations", withBool MsgNormalOrHistoricalNations)
        ,("papacy_active"               , withBool MsgPapacyIsActive)
        ,("primitives"                  , withBool MsgPrimitives)
        ,("province_has_current_tech_fort_trigger" , withBool MsgProvinceHasCurrentTechFort)
        ,("revolution_target_exists"    , withBool MsgRevolutionTargetExists)
        ,("recent_treasure_ship_passage", withBool MsgRecentTreasureShipPassage)
        ,("ruler_is_foreigner"          , withBool MsgRulerIsForeigner)
        ,("set_hre_religion_locked"     , withBool MsgSetHREReligionLocked)
        ,("set_in_empire"               , withBool MsgSetInEmpire)
        ,("set_seat_in_parliament"      , withBool MsgSetSeatInParliament)
        ,("set_revolution_in_province"  , withBool MsgSetRevolutionProvince)
        ,("uses_religious_icons"        , withBool MsgUsesIcons)
        ,("unit_in_siege"               , withBool MsgUnderSiege) -- duplicate?
        ,("uses_devotion"               , withBool MsgUsesDevotion)
        ,("uses_doom"                   , withBool MsgUsesDoom)
        ,("uses_piety"                  , withBool MsgUsesPiety)
        ,("valid_for_personal_unions_trigger" , withBool MsgValidForPU)
        ,("was_player"                  , withBool MsgHasBeenPlayer)
        ,("was_never_end_game_tag_trigger" , withBool MsgWasNeverEndGameTag)

        -- Scripted triggers for advisors
        ,("has_adm_advisor"             , boolIconLoc "adm" "ADM" MsgHasAdvisorCategory)
        ,("has_dip_advisor"             , boolIconLoc "dip" "DIP" MsgHasAdvisorCategory)
        ,("has_mil_advisor"             , boolIconLoc "mil" "MIL" MsgHasAdvisorCategory)
        ,("has_adm_advisor_2"           , boolIconLoc "adm" "ADM" (MsgHasAdvisorCategoryLevel 2))
        ,("has_dip_advisor_2"           , boolIconLoc "dip" "DIP" (MsgHasAdvisorCategoryLevel 2))
        ,("has_mil_advisor_2"           , boolIconLoc "mil" "MIL" (MsgHasAdvisorCategoryLevel 2))
        ,("has_adm_advisor_3"           , boolIconLoc "adm" "ADM" (MsgHasAdvisorCategoryLevel 3))
        ,("has_dip_advisor_3"           , boolIconLoc "dip" "DIP" (MsgHasAdvisorCategoryLevel 3))
        ,("has_mil_advisor_3"           , boolIconLoc "mil" "MIL" (MsgHasAdvisorCategoryLevel 3))

        -- From common/scripted_effects/01_scripted_triggers_muslim_schools.txt
        -- A bit lazy, but they're not commonly used
        --
        ,("has_sufi_sheikh_ul_islam_trigger"       , withBool (MsgRulerHasIslamModifier "Sufi"))
        ,("has_pious_sheikh_ul_islam_trigger"      , withBool (MsgRulerHasIslamModifier "Righteous"))
        ,("has_loyal_sheikh_ul_islam_trigger"      , withBool (MsgRulerHasIslamModifier "Loyal"))
        ]

-- | Handlers for statements that may be numeric or a tag
handlersNumericOrTag :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersNumericOrTag = Tr.fromList
        [("num_of_cities"       , numericOrTag MsgNumCities MsgNumCitiesThan)
        ,("army_professionalism", numericOrTagIcon "army professionalism" MsgArmyProfessionalism MsgArmyProfessionalismAs)
        ,("inflation"           , numericOrTagIcon "inflation" MsgInflation MsgInflationAs)
        ,("total_development"   , numericOrTagIcon "development" MsgTotalDevelopment MsgTotalDevelopmentAs)
        ,("total_own_and_non_tributary_subject_development" , numericOrTagIcon "development" MsgOwnOrNonTribSubjectDevelopment MsgOwnOrNonTribSubjectDevelopmentAs)
        ,("num_of_artillery"    , numericOrTag MsgNumArtillery MsgNumArtilleryThan)
        ,("num_of_cavalry"      , numericOrTag MsgNumCavalry MsgNumCavalryThan)
        ]

-- | Handlers for signed numeric statements
handlersSignedNumeric :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersSignedNumeric = Tr.fromList
        [("tolerance_to_this", numeric MsgToleranceToThis)
        ]

-- | Handlers querying the number of provinces of some kind, mostly religions
-- and trade goods
handlersNumProvinces :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersNumProvinces = Tr.fromList
        [
        -- Religions
         ("animism"       , numProvinces "animism" MsgReligionProvinces)
        ,("catholic"      , numProvinces "catholic" MsgReligionProvinces)
        ,("confucianism"  , numProvinces "confucianism" MsgReligionProvinces)
        ,("coptic"        , numProvinces "coptic" MsgReligionProvinces)
        ,("hinduism"      , numProvinces "hinduism" MsgReligionProvinces)
        ,("ibadi"         , numProvinces "ibadi" MsgReligionProvinces)
        ,("mahayana"      , numProvinces "mahayana" MsgReligionProvinces)
        ,("orthodox"      , numProvinces "orthodox" MsgReligionProvinces)
        ,("protestant"    , numProvinces "protestant" MsgReligionProvinces)
        ,("reformed"      , numProvinces "reformed" MsgReligionProvinces)
        ,("shamanism"     , numProvinces "fetishism" MsgReligionProvinces) -- Old name for fetishism
        ,("shiite"        , numProvinces "shiite" MsgReligionProvinces)
        ,("shinto"        , numProvinces "shinto" MsgReligionProvinces)
        ,("sikhism"       , numProvinces "sikhism" MsgReligionProvinces)
        ,("sunni"         , numProvinces "sunni" MsgReligionProvinces)
        ,("totemism"      , numProvinces "totemism" MsgReligionProvinces)

        -- Trade goods
        ,("coal"          , numProvinces "coal" MsgGoodsProvinces)
        ,("chinaware"     , numProvinces "chinaware" MsgGoodsProvinces)
        ,("cloth"         , numProvinces "cloth" MsgGoodsProvinces)
        ,("cocoa"         , numProvinces "cocoa" MsgGoodsProvinces)
        ,("coffee"        , numProvinces "coffee" MsgGoodsProvinces)
        ,("copper"        , numProvinces "copper" MsgGoodsProvinces)
        ,("cotton"        , numProvinces "cotton" MsgGoodsProvinces)
        ,("fish"          , numProvinces "fish" MsgGoodsProvinces)
        ,("fur"           , numProvinces "fur" MsgGoodsProvinces)
        ,("glass"         , numProvinces "glass" MsgGoodsProvinces)
        ,("gold"          , numProvinces "gold" MsgGoodsProvinces)
        ,("grain"         , numProvinces "grain" MsgGoodsProvinces)
        ,("iron"          , numProvinces "iron" MsgGoodsProvinces)
        ,("ivory"         , numProvinces "ivory" MsgGoodsProvinces)
        ,("livestock"     , numProvinces "livestock" MsgGoodsProvinces)
        ,("naval_supplies", numProvinces "naval supplies" MsgGoodsProvinces)
        ,("salt"          , numProvinces "salt" MsgGoodsProvinces)
        ,("silk"          , numProvinces "silk" MsgGoodsProvinces)
        ,("slaves"        , numProvinces "slaves" MsgGoodsProvinces)
        ,("spices"        , numProvinces "spices" MsgGoodsProvinces)
        ,("sugar"         , numProvinces "sugar" MsgGoodsProvinces)
        ,("tea"           , numProvinces "tea" MsgGoodsProvinces)
        ,("tobacco"       , numProvinces "tobacco" MsgGoodsProvinces)
        ,("wine"          , numProvinces "wine" MsgGoodsProvinces)
        ,("wool"          , numProvinces "wool" MsgGoodsProvinces)
        ]

-- Helpers for text/value pairs
tryLocAndIconTitle t = tryLocAndIcon (t <> "_title")

-- | Handlers for text/value pairs.
--
-- $textvalue
handlersTextValue :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersTextValue = Tr.fromList
        [("add_great_project_tier"      , textValue "type" "tier" MsgAddGreatProjectTier MsgAddGreatProjectTier tryLocAndIcon)
        ,("add_incident_variable_value" , textValue "incident" "value" MsgAddIncidentVariableValue MsgAddIncidentVariableValue tryLocAndIconTitle)
        ,("add_institution_embracement" , textValue "which" "value" MsgAddInstitutionEmbracement MsgAddInstitutionEmbracement tryLocAndIcon)
        ,("add_disaster_progress"       , textValue "disaster" "value" MsgAddDisasterProgress MsgAddDisasterProgress tryLocAndIcon)
        ,("add_estate_loyalty"          , textValue "estate" "loyalty" MsgAddEstateLoyalty MsgAddEstateLoyalty tryLocAndIcon)
        ,("add_named_unrest"            , textValue "name" "value" MsgAddNamedUnrest MsgAddNamedUnrest tryLocAndIcon)
        ,("add_power_projection"        , textValue "type" "amount" MsgAddPowerProjection MsgAddPowerProjection tryLocAndIcon)
        ,("add_spy_network_from"        , textValue "who" "value" MsgAddSpyNetworkFrom MsgAddSpyNetworkFrom flagTextMaybe)
        ,("add_spy_network_in"          , textValue "who" "value" MsgAddSpyNetworkIn MsgAddSpyNetworkIn flagTextMaybe)
        ,("army_strength"               , textValue "who" "value" MsgArmyStrength MsgArmyStrength flagTextMaybe)
        ,("border_distance"             , textValue "who" "distance" MsgBorderDistance MsgBorderDistance flagTextMaybe)
        ,("estate_influence"            , textValue "estate" "influence" MsgEstateInfluence MsgEstateInfluence tryLocAndIcon)
        ,("estate_loyalty"              , textValue "estate" "loyalty" MsgEstateLoyalty MsgEstateLoyalty tryLocAndIcon)
        ,("estate_territory"            , textValue "estate" "territory" MsgEstateTerritory MsgEstateTerritory tryLocAndIcon)
        ,("had_country_flag"            , textValue "flag" "days" MsgHadCountryFlag MsgHadCountryFlag tryLocAndIcon)
        ,("had_global_flag"             , textValue "flag" "days" MsgHadGlobalFlag MsgHadGlobalFlag tryLocAndIcon)
        ,("had_heir_flag"               , textValue "flag" "days" MsgHadHeirFlag MsgHadHeirFlag tryLocAndIcon)
        ,("had_province_flag"           , textValue "flag" "days" MsgHadProvinceFlag MsgHadProvinceFlag tryLocAndIcon)
        ,("had_ruler_flag"              , textValue "flag" "days" MsgHadRulerFlag MsgHadRulerFlag tryLocAndIcon)
        ,("has_global_modifier_value"   , textValue "which" "value" MsgHasGlobalModifierValue MsgHasGlobalModifierValue tryLocAndLocMod)
        ,("has_spy_network_from"        , textValue "who" "value" MsgHasSpyNetworkFrom MsgHasSpyNetworkFrom flagTextMaybe)
        ,("has_spy_network_in"          , textValue "who" "value" MsgHasSpyNetworkIn MsgHasSpyNetworkIn flagTextMaybe)
        ,("has_won_war_against"         , textValue "who" "max_years_since" MsgHasWonWarAgainst MsgHasWonWarAgainst flagTextMaybe)
        ,("incident_variable_value"     , textValue "incident" "value" MsgIncidentVariableValue MsgIncidentVariableValue tryLocAndIconTitle)
        ,("institution_difference"      , textValue "who" "value" MsgInstitutionDifference MsgInstitutionDifference flagTextMaybe)
        ,("military_strength"           , textValue "who" "value" MsgMilitaryStrength MsgMilitaryStrength flagTextMaybe)
        ,("num_of_estate_privileges"    , textValue "estate" "value" MsgNumEstatePrivileges MsgNumEstatePrivileges tryLocAndIcon)
        ,("num_of_units_in_province"    , textValue "who" "amount" MsgNumUnitsInProvince MsgNumUnitsInProvince flagTextMaybe) -- TODO: Support type
        ,("num_investments_in_trade_company_region" , textValue "investment" "value" MsgNumInvestmentsInTradeCompanyReigion MsgNumInvestmentsInTradeCompanyReigion tryLocAndIcon)
        ,("naval_strength"              , textValue "who" "value" MsgNavalStrength MsgNavalStrength flagTextMaybe)
        ,("province_distance"           , textValue "who" "distance" MsgProvinceDistance MsgProvinceDistance flagTextMaybe)
        ,("school_opinion"              , textValue "who" "opinion" MsgSchoolOpinion MsgSchoolOpinion flagTextMaybe)
        ,("set_school_opinion"          , textValue "who" "opinion" MsgSetSchoolOpinion MsgSetSchoolOpinion flagTextMaybe)
        ,("remove_loot"                 , textValue "who" "amount" MsgRemoveLoot MsgRemoveLoot flagTextMaybe)
        ,("trade_goods_produced_amount" , textValue "trade_goods" "amount" MsgTradeGoodsProduced MsgTradeGoodsProduced tryLocAndIcon)
        ,("trading_part"                , textValue "trade_goods" "value" MsgTradingPart MsgTradingPart tryLocAndIcon)
        ,("trade_share"                 , textValue "country" "share" MsgTradeShare MsgTradeShare flagTextMaybe)
        ,("trust"                       , textValue "who" "value" MsgTrust MsgTrust flagTextMaybe)
        ,("war_score_against"           , textValue "who" "value" MsgWarscoreAgainst MsgWarscoreAgainst flagTextMaybe)
        ,("years_in_union_under"        , textValue "who" "years" MsgYearsInUnionUnder MsgYearsInUnionUnder flagTextMaybe)
        ]

-- | Handlers for text/atom pairs
handlersTextAtom :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersTextAtom = Tr.fromList
        [("create_flagship"      , taDescAtomIcon "name" "type" MsgCreateFlagShip)
        ,("create_named_ship"    , taDescAtomIcon "name" "type" MsgCreateNamedShip)
        ,("pick_random_estate_if_present" , textAtom "flag" "estate_action" MsgPickRandomEstateIfPresent tryLoc) -- Localization/icon ignored
        ,("religious_school"     , textAtom "school" "group" MsgReligiousSchool tryLoc)
        ,("set_religious_school" , textAtom "school" "group" MsgSetReligiousSchool tryLoc)
        ]

-- | Handlers for special complex statements
handlersSpecialComplex :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersSpecialComplex = Tr.fromList
        [("add_building_construction"    , addBuildingConstruction)
        ,("add_casus_belli"              , addCB True)
        ,("add_faction_influence"        , factionInfluence MsgFactionGainInfluence)
        ,("add_government_power"         , governmentPower)
        ,("add_estate_influence_modifier", estateInfluenceModifier MsgEstateInfluenceModifier)
        ,("add_mutual_opinion_modifier_effect", opinion MsgMutualOpinion MsgMutualOpinionDur)
        ,("add_opinion"                  , opinion MsgAddOpinion MsgAddOpinionDur)
        ,("add_unit_construction"        , addUnitConstruction)
        ,("add_trust"                    , trust)
        ,("ai_attitude"                  , aiAttitude MsgAiAttitude)
        ,("reverse_add_opinion"          , opinion MsgReverseAddOpinion MsgReverseAddOpinionDur)
        ,("area"                         , area)
        ,("change_price"                 , changePrice)
        ,("create_admiral"               , createMilitaryLeader "admiral" True MsgCreateAdmiral MsgDefineAdmiral)
        ,("create_conquistador"          , createMilitaryLeader "conquistador" False MsgCreateConquistador MsgDefineConquistador)
        ,("create_explorer"              , createMilitaryLeader "explorer" True MsgCreateExplorer MsgDefineExplorer)
        ,("create_general"               , createMilitaryLeader "general" False MsgCreateGeneral MsgDefineGeneral)
        ,("custom_trigger_tooltip"       , customTriggerTooltip)
        ,("build_to_forcelimit"          , buildToForcelimit)
        ,("country_event"                , scope EU4Country . triggerEvent MsgCountryEvent)
        ,("declare_war_with_cb"          , declareWarWithCB)
        ,("define_advisor"               , defineAdvisor False)
        ,("define_consort"               , defineConsort)
        ,("define_exiled_ruler"          , defineExiledRuler)
        ,("define_heir"                  , defineHeir)
        ,("define_ruler"                 , defineRuler)
        ,("define_admiral"               , defineMilitaryLeader "admiral" True MsgDefineAdmiral)
        ,("define_conquistador"          , defineMilitaryLeader "conquistador" False MsgDefineConquistador)
        ,("define_explorer"              , defineMilitaryLeader "explorer" True MsgDefineExplorer)
        ,("define_general"               , defineMilitaryLeader "general" False MsgDefineGeneral)
        ,("define_leader_to_ruler"       , defineDynMember (\_ -> MsgDefinerLeaderToRuler) (\_ -> \_ -> MsgDefinerLeaderToRuler) (\_ -> MsgDefinerLeaderToRuler) (\_ -> \_ -> MsgDefinerLeaderToRuler))
        ,("define_ruler_to_general"      , defineMilitaryLeader "general" False MsgDefineRulerToGeneral)
        ,("employed_advisor"             , employedAdvisor)
        ,("expulsion_target"             , expulsionTarget)
        ,("faction_influence"            , factionInfluence MsgFactionHasInfluence)
        ,("has_estate_led_regency"       , hasEstateLedRegency)
        ,("has_estate_influence_modifier", hasEstateModifier MsgEstateHasInfluenceModifier)
        ,("has_estate_loyalty_modifier"  , hasEstateModifier MsgEstateHasLoyaltyModifier)
        ,("has_great_project"            , hasGreatProject)
        ,("has_opinion"                  , hasOpinion MsgHasOpinion)
        ,("has_opinion_modifier"         , opinion MsgHasOpinionMod (\modid what who _years -> MsgHasOpinionMod modid what who))
        ,("has_reached_government_reform_tier" , hasGovernmentReforTier)
        ,("has_trade_company_investment_in_area", hasTradeCompanyInvestment)
        ,("is_in_war"                    , isInWar)
        ,("privateer_power"              , privateerPower)
        ,("province_event"               , scope EU4Province . triggerEvent MsgProvinceEvent)
        ,("region"                       , region)
        ,("remove_opinion"               , opinion MsgRemoveOpinionMod (\modid what who _years -> MsgRemoveOpinionMod modid what who))
        ,("reverse_has_opinion"          , hasOpinion MsgReverseHasOpinion)
        ,("reverse_has_opinion_modifier" , opinion MsgReverseHasOpinionMod (\modid what who _years -> MsgReverseHasOpinionMod modid what who))
        ,("reverse_remove_opinion"       , opinion MsgReverseRemoveOpinionMod (\modid what who _years -> MsgReverseRemoveOpinionMod modid what who))
        ,("religion_years"               , religionYears)
        ,("set_ai_attitude"              , aiAttitude MsgSetAiAttitude)
        ,("reverse_add_casus_belli"      , addCB False)
        ,("trading_bonus"                , tradingBonus)
        ,("trading_policy_in_node"       , tradingPolicyInNode)
        ,("trigger_switch"               , triggerSwitch)

        -- Effects/Triggers
        ,("add_loot_from_rich_province_general_effect" , simpleEffectAtom "looter" MsgAddLootFromRichProvince) -- Note: RHS ignored
        ,("allow_baseline_invite_scholar"   , simpleEffectAtom "religious_school" MsgAllowBaselineInviteScholar)
        ,("check_reducing_estate_revolt_size_trigger" , simpleEffectAtom "flag" (MsgCheckEstateRevoltSize False))
        ,("check_reducing_estate_revolt_size_more_trigger" , simpleEffectAtom "flag" (MsgCheckEstateRevoltSize True))
        ,("generate_exile_advisor_effect"   , simpleEffectAtom "advisor_type" MsgGenerateExileAdvisor)
        ,("generate_scaled_advisor_of_type_and_religion_effect" , defineAdvisor True)
        ,("generate_traitor_advisor_effect" , simpleEffectNum "skill_level" MsgGenerateTraitorAdvisor)
        ,("has_primary_cult"                , simpleEffectAtom "cult" MsgHasPrimaryCult)
        ,("our_scholar_matches_their_school_trigger" , simpleEffectAtom "school" MsgOurScholarMatchesTheirSchool)
        ,("kill_advisor_by_category_effect" , killAdvisorByCategory)
        ,("select_primary_cult"             , simpleEffectAtom "cult" MsgSelectPrimaryCult)
        ,("province_is_or_accepts_religion" , isOrAcceptsReligion)
        ,("province_is_or_accepts_religion_group" , isOrAcceptsReligionGroup)
        ,("set_great_project_tier_1"        , simpleEffectAtom "type" (MsgSetGreatProjectTier 1))
        ,("set_great_project_tier_2"        , simpleEffectAtom "type" (MsgSetGreatProjectTier 2))
        ,("set_great_project_tier_3"        , simpleEffectAtom "type" (MsgSetGreatProjectTier 3))
        ,("scaled_estate_land_share_reduce_effect" , simpleEffectAtom "estate" (MsgScaledEstateLandShareEffect False))
        ,("scaled_estate_land_share_add_effect" , simpleEffectAtom "estate" (MsgScaledEstateLandShareEffect True))
        ,("unlock_estate_privilege"         , simpleEffectAtom "estate_privilege" MsgUnlockEstatePrivilege)

        -- Variables
        ,("set_variable"                 , setVariable MsgSetVariable MsgSetVariableVal)
        ,("change_variable"              , setVariable MsgAddVariable MsgAddVariableVal)
        ,("subtract_variable"            , setVariable MsgSubVariable MsgSubVariableVal)
        ,("multiply_variable"            , setVariable MsgMulVariable MsgMulVariableVal)
        ,("divide_variable"              , setVariable MsgDivVariable MsgDivVariableVal)
        ,("check_variable"               , setVariable MsgChkVariable MsgChkVariableVal)
        ,("is_variable_equal"            , setVariable MsgEquVariable MsgEquVariableVal)
        ,("export_to_variable"           , exportVariable)

        -- Has building triggers (from common/scripted_triggers/00_scripted_triggers.txt)
        ,("has_courthouse_building_trigger" , hasBuildingTrigger ["courthouse", "town_hall"])
        ,("has_dock_building_trigger"       , hasBuildingTrigger ["dock", "drydock"])
        ,("has_forcelimit_building_trigger" , hasBuildingTrigger ["regimental_camp", "conscription_center"])
        ,("has_manpower_building_trigger"   , hasBuildingTrigger ["barracks", "training_fields"])
        ,("has_production_building_trigger" , hasBuildingTrigger ["workshop", "counting_house"])
        ,("has_shipyard_building_trigger"   , hasBuildingTrigger ["shipyard", "grand_shipyard"])
        ,("has_tax_building_trigger"        , hasBuildingTrigger ["temple", "cathedral"])
        ,("has_trade_building_trigger"      , hasBuildingTrigger ["marketplace", "trade_depot", "stock_exchange"])
        ]

-- | Handlers for statements pertaining to rebels
handlersRebels :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersRebels = Tr.fromList
        [("can_spawn_rebels"  , canSpawnRebels)
        ,("create_revolt"     , spawnRebels Nothing)
        ,("has_spawned_rebels", hasSpawnedRebels)
        ,("likely_rebels"     , canSpawnRebels)
        ,("spawn_rebels"      , spawnRebels Nothing)
        -- Specific rebels
        ,("anti_tax_rebels"      , spawnRebelsSimple)
        ,("nationalist_rebels"   , spawnRebelsSimple)
        ,("noble_rebels"         , spawnRebelsSimple)
        ,("pretender_rebels"     , spawnRebelsSimple)
        ,("polish_noble_rebels"  , spawnRebelsSimple)
        ,("revolutionary_rebels" , spawnRebelsSimple)
        ,("heretic_rebels"       , spawnRebelsSimple)
        ,("particularist_rebels" , spawnRebelsSimple)
        -- Scripted
        ,("spawn_small_scaled_rebels" , spawnScaledRebels False)
        ,("spawn_large_scaled_rebels" , spawnScaledRebels True)
        ]

-- | Handlers for idea groups
handlersIdeaGroups :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersIdeaGroups = Tr.fromList
        -- Idea groups
        [("aristocracy_ideas"   , hasIdea MsgHasAristocraticIdea)
        ,("defensive_ideas"     , hasIdea MsgHasDefensiveIdea)
        ,("economic_ideas"      , hasIdea MsgHasEconomicIdea)
        ,("innovativeness_ideas", hasIdea MsgHasInnovativeIdea)
        ,("maritime_ideas"      , hasIdea MsgHasMaritimeIdea)
        ,("offensive_ideas"     , hasIdea MsgHasOffensiveIdea)
        ]

-- | Handlers for miscellaneous statements
handlersMisc :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersMisc = Tr.fromList
        [("random", random)
        ,("random_list", randomList)
        -- Special
        ,("add_estate_loyalty_modifier" , addEstateLoyaltyModifier)
        ,("add_core"            , addCore)
        ,("add_manpower"        , gainMen)
        ,("add_sailors"         , gainMen)
        ,("calc_true_if"        , calcTrueIf)
        ,("change_estate_land_share" , changeEstateLandShare)
        ,("create_independent_estate" , createIndependentEstate)
        ,("create_subject"      , taTypeFlag "subject_type" "subject" MsgCreateSubject)
        ,("change_subject_type" , simpleEffectAtom "subject_type" MsgChangeSubjectType)
        ,("create_succession_crisis" , createSuccessionCrisis)
        ,("development_in_provinces" , numOwnedProvincesWith MsgDevelopmentInProvinces)
        ,("dominant_culture"    , dominantCulture)
        ,("dynasty"             , dynasty)
        ,("faction_in_power"    , factionInPower)
        ,("government_rank"     , govtRank)
        ,("has_casus_belli"     , taTypeFlag "type" "target" MsgHasCasusBelli)
        ,("has_dlc"             , hasDlc)
        ,("has_government_attribute" , hasGovermentAttribute)
        ,("has_heir"            , hasHeir)
        ,("has_leaders"         , hasLeaders)
        ,("has_leader_with"     , hasLeaderWith)
        ,("hre_reform_level"    , hreReformLevel)
        ,("is_month"            , isMonth)
        ,("kill_leader"         , killLeader)
        ,("kill_heir"           , killHeir)
        ,("kill_units"          , killUnits)
        ,("num_of_owned_provinces_with" , numOwnedProvincesWith MsgNumOwnedProvincesWith)
        ,("num_of_provinces_owned_or_owned_by_non_sovereign_subjects_with" , numOwnedProvincesWith MsgNumOwnedProvincesOrNonSovereignSubjectsWith)
        ,("num_of_religion"     , numOfReligion)
        ,("num_of_states_owned_or_owned_by_non_sovereign_subjects_with" , numOwnedProvincesWith MsgNumOwnedStatesOrNonSovereignSubjectsWith)
        ,("piety"               , piety)
        ,("production_leader"   , productionLeader)
        ,("range"               , range)
        ,("remove_casus_belli"  , taTypeFlag "type" "target" MsgRemoveCasusBelli)
        ,("remove_trade_modifier" , taTypeFlag "name" "who" MsgRemoveTradeModifier)
        ,("set_government_rank" , setGovtRank)
        ,("set_saved_name"      , setSavedName)
        ,("generate_advisor_of_type_and_semi_random_religion_effect" , randomAdvisor)
        ,("create_colony_mission_reward" , createColonyMissionReward)
        ,("has_idea_group"      , hasIdeaGroup)
        -- Estate monopoly privileges
        ,("apply_estate_monopoly_modifier"  , estatePrivilege MsgApplyEstateModifer)
        ,("reapply_estate_privilege"        , estatePrivilege MsgReapplyEstatePrivilege)
        ,("remove_estate_monopoly_modifier" , estatePrivilege MsgRemoveEstateModifer)
        -- Estate land share effects (from 01_scripted_effects_for_estates.txt)
        ,("give_estate_land_share_small"    , estateLandShareEffect 1)
        ,("give_estate_land_share_medium"   , estateLandShareEffect 2)
        ,("give_estate_land_share_large"    , estateLandShareEffect 3)
        ,("give_estate_land_share_massive"  , estateLandShareEffect 5)
        ,("give_estate_land_share_gigantic" , estateLandShareEffect 10)
        ,("take_estate_land_share_small"    , estateLandShareEffect (-1))
        ,("take_estate_land_share_medium"   , estateLandShareEffect (-2))
        ,("take_estate_land_share_large"    , estateLandShareEffect (-3))
        ,("take_estate_land_share_massive"  , estateLandShareEffect (-5))
        ,("take_estate_land_share_gigantic" , estateLandShareEffect (-10))
        -- Ancestor personality
        ,("add_heir_personality_ancestor"    , personalityAncestor (MsgAddHeirPersonality True))
        ,("add_queen_personality_ancestor"   , personalityAncestor (MsgAddConsortPersonality True))
        ,("add_ruler_personality_ancestor"   , personalityAncestor (MsgAddRulerPersonality True))
        ,("consort_has_personality_ancestor" , personalityAncestor (MsgConsortHasPersonality True))
        ,("heir_has_personality_ancestor"    , personalityAncestor (MsgHeirHasPersonality True))
        ,("remove_ruler_personality_ancestor", personalityAncestor (MsgRemoveRulerPersonality True))
        ,("ruler_has_personality_ancestor"   , personalityAncestor (MsgRulerHasPersonality True))
        -- Conditions that require a certain number of buildings
        ,("cathedral"                        , buildingCount)
        ,("counting_house"                   , buildingCount)
        ,("farm_estate"                      , buildingCount)
        ,("fort_15th"                        , buildingCount)
        ,("furnace"                          , buildingCount)
        ,("grand_shipyard"                   , buildingCount)
        ,("marketplace"                      , buildingCount)
        ,("mills"                            , buildingCount)
        ,("native_ceremonial_fire_pit"       , buildingCount)
        ,("native_longhouse"                 , buildingCount)
        ,("native_sweat_lodge"               , buildingCount)
        ,("plantations"                      , buildingCount)
        ,("shipyard"                         , buildingCount)
        ,("stock_exchange"                   , buildingCount)
        ,("temple"                           , buildingCount)
        ,("textile"                          , buildingCount)
        ,("trade_depot"                      , buildingCount)
        ,("university"                       , buildingCount)
        ,("wharf"                            , buildingCount)
        ,("workshop"                         , buildingCount)
        -- Institutions
        ,("feudalism"                        , institutionPresence)
        ,("renaissance"                      , institutionPresence)
        ,("new_world_i"                      , institutionPresence)
        ,("printing_press"                   , institutionPresence)
        ,("global_trade"                     , institutionPresence)
        ,("manufactories"                    , institutionPresence)
        ,("enlightenment"                    , institutionPresence)
        ,("industrialization"                , institutionPresence)
        ]

-- | Handlers for ignored statements
handlersIgnored :: (EU4Info g, Monad m) => Trie (StatementHandler g m)
handlersIgnored = Tr.fromList
        [("custom_tooltip", return $ return [])
        ,("goto"          , return $ return [])
        ,("log"           , return $ return [])
        ,("tooltip"       , return $ return [])
        ,("required_personality", return $ return[]) -- From the 1.30 patch notes: "The required_personality field will now be ignored"
        ,("highlight"     , return $ return [])
        ,("picture"       , return $ return []) -- Some modifiers have custom pictures
        ]

-- | Extract the appropriate message(s) from a single statement. Note that this
-- may produce many lines (via 'ppMany'), since some statements are compound.
ppOne :: (EU4Info g, Monad m) => StatementHandler g m
ppOne stmt@[pdx| %lhs = %rhs |] = case lhs of
    GenericLhs label _ -> case Tr.lookup (TE.encodeUtf8 (T.toLower label)) ppHandlers of
        Just handler -> handler stmt
        -- default
        Nothing -> if isTag label
             then case rhs of
                CompoundRhs scr ->
                    withCurrentIndent $ \_ -> do -- force indent level at least 1
                        lflag <- plainMsg' =<< (<> ":") <$> flagText (Just EU4Country) label
                        scriptMsgs <- scope EU4Country $ ppMany scr
                        return (lflag : scriptMsgs)
                _ -> preStatement stmt
             else do
                geoData <- getGeoData
                mloc <- getGameL10nIfPresent label
                case mloc of
                    -- Check for localizable atoms, e.g. regions
                    Just loc -> case rhs of
                        CompoundRhs scr -> ppMaybeGeo label loc scr
                        _ -> compound loc stmt
                    Nothing -> preStatement stmt
    AtLhs _ -> return [] -- don't know how to handle these
    IntLhs n -> do -- Treat as a province tag
        tradeNodes <- getTradeNodes
        case rhs of
            CompoundRhs scr ->
                -- Check if this is the main province of a trade node in which case we need
                -- to see if that needs to be displayed instead
                case HM.lookup n tradeNodes of
                    Just node | isTradeNodeQuery scr -> do
                        nodeLoc <- getGameL10n node
                        header <- msgToPP (MsgTradeNode nodeLoc)
                        scriptMsgs <- scope EU4TradeNode $ ppMany scr
                        return (header ++ scriptMsgs)
                    _ -> do
                        prov_loc <- getProvLoc n
                        header <- msgToPP (MsgProvince prov_loc)
                        scriptMsgs <- scope EU4Province $ ppMany scr
                        return (header ++ scriptMsgs)
            _ -> preStatement stmt
    CustomLhs _ -> preStatement stmt
ppOne stmt = preStatement stmt

isTradeNodeQuery :: GenericScript -> Bool
isTradeNodeQuery scr = any isTradeNodeQuery' scr
    where
        isTradeNodeQuery' :: GenericStatement -> Bool
        isTradeNodeQuery' stmt@[pdx| $lhs = @scr |] = case Tr.lookup (TE.encodeUtf8 (T.toLower lhs)) isTradeNodeScrTrie of
            Just True -> True
            Just False -> isTradeNodeQuery scr
            _ -> False
        isTradeNodeQuery' stmt@[pdx| $lhs = %_ |] = isJust $ Tr.lookup (TE.encodeUtf8 (T.toLower lhs)) isTradeNodeQueryTrie
        isTradeNodeQuery' _ = False
        -- Conditions/commands that are listed as Province (Trade node) on the wiki
        isTradeNodeQueryTrie :: Trie ()
        isTradeNodeQueryTrie = Tr.fromList
            [("add_trade_node_income",())
            ,("has_merchant",())
            ,("has_most_province_trade_power",())
            ,("has_trader",())
            ,("highest_value_trade_node",())
            ,("is_strongest_trade_power",())
            ,("recall_merchant",())
            ,("trade_range",())
            ]
        isTradeNodeScrTrie :: Trie Bool
        isTradeNodeScrTrie = Tr.fromList
            [("add_trade_modifier"                , True)
            ,("has_privateer_share_in_trade_node" , True)
            ,("has_trade_modifier"                , True)
            ,("most_province_trade_power"         , True)
            ,("privateer_power"                   , True)
            ,("strongest_trade_power"             , True)
            ,("remove_trade_modifier"             , True)
            ,("trade_share"                       , True)

            ,("and"                               , False)
            ,("else"                              , False)
            ,("if"                                , False)
            ,("not"                               , False)
            ,("or"                                , False)
            ]

ppMaybeGeo :: (EU4Info g, Monad m) => Text -> Text -> GenericScript -> PPT g m IndentedMessages
ppMaybeGeo label loc scr = do
    geoData <- getGeoData
    let (mtypeStmt, rest) = extractStmt (matchExactText "type" "all") scr
    case HM.lookup label geoData of
        Just geoType -> do
            inEffect <- getIsInEffect
            header <- plainMsg' $ (if isJust mtypeStmt || inEffect then "All provinces" else "Any province")
                <> " in the " <> loc <> " " <> (describe geoType) <> ":"
            scriptMsgs <- scope EU4Province $ ppMany rest
            return (header : scriptMsgs)
        Nothing -> do
            let actScope = if (T.toLower label) `elem` ["emperor", "revolution_target", "crusade_target"] then
                    EU4Country
                else
                    EU4Province
            header <- plainMsg' $ loc <> ":"
            scriptMsgs <- scope actScope $ ppMany scr
            return (header : scriptMsgs)

    where
        describe :: EU4GeoType -> Text
        describe EU4GeoArea = "area"
        describe EU4GeoRegion = "region"
        describe EU4GeoSuperRegion = "subcontinent"
        describe EU4GeoContinent = "continent"
        describe EU4GeoTradeCompany = "trade company region"
        describe EU4GeoColonialRegion = "region" -- No need to say "colonial region" since that's implied by the localized name

-- | Try to extra one matching statement
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
matchLhsText _ _ = False

-- | Predicate for matching text on boths sides
matchExactText :: Text -> Text -> GenericStatement -> Bool
matchExactText l r s@[pdx| $lhs = $rhs |] | l == lhs && r == T.toLower rhs = True
matchExactText _ _ _ = False
