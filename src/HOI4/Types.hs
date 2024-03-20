{-|
Module      : HOI4.Types
Description : Types specific to Hearts of Iron IV
-}
module HOI4.Types (
        -- * Parser state
        HOI4Data (..), HOI4State (..)
    ,   HOI4Info (..)
        -- * Features
    ,   HOI4EvtTitle (..), HOI4EvtDesc (..), HOI4Event (..), HOI4Option (..)
    ,   HOI4EventSource (..), HOI4EventTriggers, HOI4EventWeight
    ,   HOI4Decision (..), HOI4DecisionCost(..), HOI4DecisionIcon(..), HOI4Decisioncat (..)
    ,   HOI4DecisionSource (..), HOI4DecisionTriggers, HOI4DecisionWeight
    ,   HOI4Idea (..)
    ,   HOI4OpinionModifier (..)
    ,   HOI4DynamicModifier (..)
    ,   HOI4Modifier (..)
    ,   HOI4NationalFocus (..)

    ,   HOI4CountryHistory (..)
    ,   HOI4Character (..), HOI4Advisor (..)
    ,   HOI4CountryLeaderTrait (..)
    ,   HOI4UnitLeaderTrait (..)
    ,   HOI4BopRange (..)
    ,   HOI4Technology (..)
        -- * Low level types
    ,   HOI4Scope (..)
    ,   AIWillDo (..)
    ,   AIModifier (..)
    ,   aiWillDo
    ) where

import Data.List (foldl')
import Data.Text (Text)
import qualified Data.Text as T
import Data.HashMap.Strict (HashMap)

import Abstract -- everything
import QQ (pdx)
import SettingsTypes ( PPT, Settings
                     , IsGame (..), IsGameData (..), IsGameState (..))
import HOI4.Messages (ScriptMessage)
--import Doc

--------------------------------------------
-- Types used by toplevel Settings module --
--------------------------------------------

-- | Settings, raw scripts, and parsed scripts.
data HOI4Data = HOI4Data {
        hoi4settings :: Settings
    ,   hoi4events :: HashMap Text HOI4Event
    ,   hoi4decisioncats :: HashMap Text HOI4Decisioncat
    ,   hoi4decisions :: HashMap Text HOI4Decision
    ,   hoi4ideas :: HashMap Text HOI4Idea
    ,   hoi4opmods :: HashMap Text HOI4OpinionModifier
    ,   hoi4eventTriggers :: HOI4EventTriggers
    ,   hoi4decisionTriggers :: HOI4DecisionTriggers
    ,   hoi4dynamicmodifiers :: HashMap Text HOI4DynamicModifier
    ,   hoi4modifiers :: HashMap Text HOI4Modifier
    ,   hoi4nationalfocusScripts :: HashMap FilePath GenericScript
    ,   hoi4nationalfocus :: HashMap Text HOI4NationalFocus
    ,   hoi4countryHistory :: HashMap Text HOI4CountryHistory
    ,   hoi4eventScripts :: HashMap FilePath GenericScript
    ,   hoi4decisioncatScripts :: HashMap FilePath GenericScript
    ,   hoi4decisionScripts :: HashMap FilePath GenericScript
    ,   hoi4ideaScripts :: HashMap FilePath GenericScript
    ,   hoi4opmodScripts :: HashMap FilePath GenericScript
    ,   hoi4onactionsScripts :: HashMap FilePath GenericScript
    ,   hoi4dynamicmodifierScripts :: HashMap FilePath GenericScript
    ,   hoi4modifierScripts :: HashMap FilePath GenericScript

    ,   hoi4countryHistoryScripts :: HashMap FilePath GenericScript -- Country Tag -> country tag + ideology
    ,   hoi4extraScripts :: HashMap FilePath GenericScript -- Extra scripts parsed on the command line
--    ,   hoi4interfacegfxScripts :: HashMap FilePath GenericScript
--    ,   hoi4interfacegfx :: HashMap Text Text
    ,   hoi4characterScripts :: HashMap FilePath GenericScript
    ,   hoi4characters :: HashMap Text HOI4Character
    ,   hoi4countryleadertraitScripts :: HashMap FilePath GenericScript
    ,   hoi4countryleadertraits :: HashMap Text HOI4CountryLeaderTrait
    ,   hoi4unitleadertraitScripts :: HashMap FilePath GenericScript
    ,   hoi4unitleadertraits :: HashMap Text HOI4UnitLeaderTrait
    ,   hoi4terrainScripts :: HashMap FilePath GenericScript
    ,   hoi4terrain :: [Text]
    ,   hoi4ideologyScripts :: HashMap FilePath GenericScript
    ,   hoi4ideology :: HashMap Text Text
    ,   hoi4chartoken :: HashMap Text HOI4Advisor
    ,   hoi4scriptedeffectScripts :: HashMap FilePath GenericScript
    ,   hoi4scriptedeffects :: HashMap Text GenericStatement
    ,   hoi4scriptedtriggerScripts :: HashMap FilePath GenericScript
    ,   hoi4scriptedtriggers :: HashMap Text GenericStatement
    ,   hoi4modifierdefinitionScripts :: HashMap FilePath GenericScript
    ,   hoi4modifierdefinitions :: HashMap Text (Text -> Double -> ScriptMessage)
    ,   hoi4bopScripts :: HashMap FilePath GenericScript
    ,   hoi4bops :: HashMap Text HOI4BopRange
    ,   hoi4techScripts :: HashMap FilePath GenericScript
    ,   hoi4techs :: HashMap FilePath [HOI4Technology]
    ,   hoi4lockeys :: [Text]
    ,   hoi4modkeys :: [Text]

    ,   hoi4extraScriptsCountryScope :: HashMap FilePath GenericScript -- Extra scripts parsed on the command line
    ,   hoi4extraScriptsProvinceScope :: HashMap FilePath GenericScript -- Extra scripts parsed on the command line
    ,   hoi4extraScriptsModifier :: HashMap FilePath GenericScript -- Extra scripts parsed on the command line

    -- etc.
    }

-- | State type for HOI4.
data HOI4State = HOI4State {
        hoi4scopeStack :: [HOI4Scope]
    ,   hoi4currentFile :: Maybe FilePath
    ,   hoi4currentIndent :: Maybe Int
    ,   hoi4IsInEffect :: Bool
    } deriving (Show)

-- | Interface for HOI4 feature handlers. Most of the methods just get data
-- tables from the parser state. These are empty until the relevant parsing
-- stages have been done. In order to avoid import loops, handlers don't know
-- the 'HOI4.Settings.HOI4' type itself, only its instances.
class (IsGame g,
       Scope g ~ HOI4Scope,
       IsGameData (GameData g),
       IsGameState (GameState g)) => HOI4Info g where
    -- | Get the title of an event by its ID. Only works if event scripts have
    -- been parsed.
    getEventTitle :: Monad m => Text -> PPT g m (Maybe Text)
    -- | Get the contents of all event script files.
    getEventScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Save (or amend) the contents of script event files in state.
    setEventScripts :: Monad m => HashMap FilePath GenericScript -> PPT g m ()
    -- | Get the parsed events table (keyed on event ID).
    getEvents :: Monad m => PPT g m (HashMap Text HOI4Event)
    -- | Get the contents of all idea groups files.
    getIdeaScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the parsed idea groups table (keyed on idea group ID).
    getIdeas :: Monad m => PPT g m (HashMap Text HOI4Idea)
    -- | Get the contents of all opinion modifier script files.
    getOpinionModifierScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the parsed opinion modifiers table (keyed on modifier ID).
    getOpinionModifiers :: Monad m => PPT g m (HashMap Text HOI4OpinionModifier)
    -- | Get the contents of all decision categories script files.
    getDecisioncatScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the contents of all decision script files.
    getDecisionScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the parsed decision categories table (keyed on decision category ID).
    getDecisioncats :: Monad m => PPT g m (HashMap Text HOI4Decisioncat)
    -- | Get the parsed decisions table (keyed on decision ID).
    getDecisions :: Monad m => PPT g m (HashMap Text HOI4Decision)
    -- | Get the (known) event triggers
    getEventTriggers :: Monad m => PPT g m HOI4EventTriggers
    -- | Get the (known) event triggers
    getDecisionTriggers :: Monad m => PPT g m HOI4DecisionTriggers
    -- | Get the on actions script files
    getOnActionsScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the contents of all dynamic modifier script files.
    getDynamicModifierScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the parsed dynamic modifiers table (keyed on modifier ID).
    getDynamicModifiers :: Monad m => PPT g m (HashMap Text HOI4DynamicModifier)
    -- | Get the contents of all modifier script files.
    getModifierScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the parsed modifiers table (keyed on modifier ID).
    getModifiers :: Monad m => PPT g m (HashMap Text HOI4Modifier)
    -- | Get the content of all national focus files
    getNationalFocusScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get extra scripts parsed from command line arguments
    getNationalFocus :: Monad m => PPT g m (HashMap Text HOI4NationalFocus)

    -- | Get the country history files
    getCountryHistoryScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the country history parsed
    getCountryHistory :: Monad m => PPT g m (HashMap Text HOI4CountryHistory)
    -- | Get character script
    getCharacterScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the characters parsed
    getCharacters :: Monad m => PPT g m (HashMap Text HOI4Character)
    -- | Get leader traits script
    getCountryLeaderTraitScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the leader traits parsed
    getCountryLeaderTraits :: Monad m => PPT g m (HashMap Text HOI4CountryLeaderTrait)
    -- | Get leader traits script
    getUnitLeaderTraitScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the leader traits parsed
    getUnitLeaderTraits :: Monad m => PPT g m (HashMap Text HOI4UnitLeaderTrait)
    -- | Get terrain script
    getTerrainScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the terrain parsed
    getTerrain :: Monad m => PPT g m [Text]
    -- | Get leader traits script
    getIdeologyScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the leader traits parsed
    getIdeology :: Monad m => PPT g m (HashMap Text Text)
    -- | Get the advisors keyed on ideatoken
    getCharToken :: Monad m => PPT g m (HashMap Text HOI4Advisor)
    -- | Get scripted effects script
    getScriptedEffectScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the scripted effects parsed
    getScriptedEffects  :: Monad m => PPT g m (HashMap Text GenericStatement)
    -- | Get scripted triggers script
    getScriptedTriggerScripts  :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the scripted triggers parsed
    getScriptedTriggers  :: Monad m => PPT g m (HashMap Text GenericStatement)
    -- | Get modifier definition scripts
    getModifierDefintionScripts  :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the modifier definition  parsed
    getModifierDefinitions  :: Monad m => PPT g m (HashMap Text (Text -> Double -> ScriptMessage))
    -- | Get balance of power script
    getBopScripts  :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the balance of power parsed
    getBops  :: Monad m => PPT g m (HashMap Text HOI4BopRange)
    -- | Get technologies script
    getTechnologyScripts  :: Monad m => PPT g m (HashMap FilePath GenericScript)
    -- | Get the technologies parsed
    getTechnologies  :: Monad m => PPT g m (HashMap FilePath [HOI4Technology])
    -- | Get the lockeys
    getLocKeys :: Monad m => PPT g m [Text]
    -- | Get the modkeys parsed
    getModKeys :: Monad m => PPT g m [Text]

    -- | Get extra scripts parsed from command line arguments
    getExtraScripts :: Monad m => PPT g m (HashMap FilePath GenericScript)
    getExtraScriptsCountryScope :: Monad m => PPT g m (HashMap FilePath GenericScript)
    getExtraScriptsProvinceScope :: Monad m => PPT g m (HashMap FilePath GenericScript)
    getExtraScriptsModifier :: Monad m => PPT g m (HashMap FilePath GenericScript)

-------------------
-- Feature types --
-------------------

-- | Event title type. As of HoI4 whatever version, titles may be conditional.
data HOI4EvtTitle
    = HOI4EvtTitleSimple Text  -- title = key
    | HOI4EvtTitleConditional GenericScript Text
            -- title = { text = key trigger = conditions }
    | HOI4EvtTitleCompound GenericScript
            -- title = { trigger = { conditional_expressions } }
    deriving (Show)

-- | Event description type. As of HOI4 whatever version, descriptions may be conditional.
data HOI4EvtDesc
    = HOI4EvtDescSimple Text  -- desc = key
    | HOI4EvtDescConditional GenericScript Text
            -- desc = { text = key trigger = conditions }
    | HOI4EvtDescCompound GenericScript
            -- desc = { trigger = { conditional_expressions } }
    deriving (Show)

-- | Event data.
data HOI4Event = HOI4Event {
    -- | Event ID
        hoi4evt_id :: Maybe Text
    -- | Event title l10n key
    ,   hoi4evt_title :: [HOI4EvtTitle]
    -- | Description
    ,   hoi4evt_desc :: [HOI4EvtDesc]
    -- | Type of thing the event happens to (e.g.  for a @country_event@ this
    -- is 'HOI4Country'). This is used to set the top level scope for its
    -- scripts.
    ,   hoi4evt_scope :: HOI4Scope
    -- | What conditions allow the event to trigger.
    ,   hoi4evt_trigger :: Maybe GenericScript
    -- | Whether the event is only triggered by script commands. If this is
    -- @False@ and the event also has a @mean_time_to_happen@, it can happen
    -- randomly.
    ,   hoi4evt_is_triggered_only :: Maybe Bool
    -- | If this is a random event, how unlikely this event is to happen.
    ,   hoi4evt_mean_time_to_happen :: Maybe GenericScript
    -- | Commands to execute as soon as the event fires.
    ,   hoi4evt_immediate :: Maybe GenericScript
    -- | Whether this is a hidden event (it will have no options).
    ,   hoi4evt_hide_window :: Bool
    -- | Whether this event can only happen once per campaign
    ,   hoi4evt_fire_only_once :: Bool
    -- | Whether this event is show to all countries (for example news events)
    ,   hoi4evt_major :: Bool
    -- | If the event is major this restricts who it is or isn't shown for.
    ,   hoi4evt_show_major :: Maybe GenericScript
    -- | List of options for the player/AI to choose from.
    ,   hoi4evt_options :: Maybe [HOI4Option]
    -- | If the event show to sender
    ,   hoi4evt_fire_for_sender :: Maybe Bool
    -- | The event's source file.
    ,   hoi4evt_path :: FilePath
    } deriving (Show)
-- | Event option data.
data HOI4Option = HOI4Option
    {   hoi4opt_name :: Maybe Text               -- ^ Text of the option
    ,   hoi4opt_trigger :: Maybe GenericScript   -- ^ Condition for the option to be available
    ,   hoi4opt_ai_chance :: Maybe AIWillDo -- ^ Probability that the AI will choose this option
    ,   hoi4opt_effects :: Maybe GenericScript   -- ^ What happens if the player/AI chooses this option
    } deriving (Show)

type HOI4EventWeight = Maybe (Integer, Integer) -- Rational reduces the number, which we don't want

data HOI4EventSource =
      HOI4EvtSrcImmediate Text                      -- Immediate effect of an event (arg is event ID)
    | HOI4EvtSrcOption Text Text                    -- Effect of choosing an event option (args are event ID and option ID)
    | HOI4EvtSrcDecComplete Text Text               -- Effect of completing a decision (args are id and localized decision text)
    | HOI4EvtSrcDecRemove Text Text                 -- Effect of taking a timed decision and letting it finish (args are id and localized decision text)
    | HOI4EvtSrcDecCancel Text Text                 -- Effect of taking a decision and it being canceled (args are id and localized decision text)
    | HOI4EvtSrcDecTimeout Text Text                -- Effect of taking a decision/mission and letting it timeout (args are id and localized decision text)
    | HOI4EvtSrcOnAction Text HOI4EventWeight       -- An effect from on_actions (args are the trigger and weight)
    | HOI4EvtSrcNFComplete Text Text Text           -- Effect of completing a national focus
    | HOI4EvtSrcNFSelect Text Text Text             -- Effect of selecting a national focus
    | HOI4EvtSrcIdeaOnAdd Text Text Text Text       -- Effect of adding an idea
    | HOI4EvtSrcIdeaOnRemove Text Text Text Text    -- Effect of removing an idea
    | HOI4EvtSrcCharacterOnAdd Text Text Text            -- Effect of adding an advisor
    | HOI4EvtSrcCharacterOnRemove Text Text Text         -- Effect of removing an advisor
    | HOI4EvtSrcScriptedEffect Text HOI4EventWeight -- Effect of a scripted effect
    | HOI4EvtSrcBopOnActivate Text                  -- Effect of a balance of power range activation
    | HOI4EvtSrcBopOnDeactivate Text                -- Effect of a balance of power range deactivation
    deriving Show

type HOI4EventTriggers = HashMap Text [HOI4EventSource]

type HOI4DecisionWeight = Maybe (Integer, Integer) -- Rational reduces the number, which we don't want

data HOI4DecisionSource =
      HOI4DecSrcImmediate Text                      -- Immediate effect of an decision (arg is decision ID)
    | HOI4DecSrcOption Text Text                    -- Effect of choosing an decision option (args are decision ID and option ID)
    | HOI4DecSrcDecComplete Text Text               -- Effect of completing a decision (args are id and localized decision text)
    | HOI4DecSrcDecRemove Text Text                 -- Effect of taking a timed decision and letting it finish (args are id and localized decision text)
    | HOI4DecSrcDecCancel Text Text                 -- Effect of taking a decision and it being canceled (args are id and localized decision text)
    | HOI4DecSrcDecTimeout Text Text                -- Effect of taking a decision/mission and letting it timeout (args are id and localized decision text)
    | HOI4DecSrcOnAction Text HOI4DecisionWeight    -- An effect from on_actions (args are the trigger and weight)
    | HOI4DecSrcNFComplete Text Text Text           -- Effect of completing a national focus
    | HOI4DecSrcNFSelect Text Text Text             -- Effect of selecting a national focus
    | HOI4DecSrcIdeaOnAdd Text Text Text Text       -- Effect of adding an idea
    | HOI4DecSrcIdeaOnRemove Text Text Text Text    -- Effect of removing an idea
    | HOI4DecSrcCharacterOnAdd Text Text Text            -- Effect of adding an advisor
    | HOI4DecSrcCharacterOnRemove Text Text Text         -- Effect of removing an advisor
    | HOI4DecSrcScriptedEffect Text HOI4DecisionWeight -- Effect of a scripted effect
    | HOI4DecSrcBopOnActivate Text                  -- Effect of a balance of power range activation
    | HOI4DecSrcBopOnDeactivate Text                -- Effect of a balance of power range deactivation
    deriving Show

type HOI4DecisionTriggers = HashMap Text [HOI4DecisionSource]

-- | Idea data.
data HOI4Idea = HOI4Idea
    {   id_id :: Text -- ^ Idea ID
    ,   id_name :: Text -- ^ idea name
    ,   id_name_loc :: Text -- ^ Localized idea name
    ,   id_desc_loc :: Maybe Text
    ,   id_picture :: Text -- ^ uses idea ID unless filled in
    ,   id_allowed :: Maybe GenericScript
    ,   id_visible :: Maybe GenericScript
    ,   id_available :: Maybe GenericScript
    ,   id_modifier :: Maybe GenericStatement
    ,   id_targeted_modifier :: Maybe GenericScript
    ,   id_research_bonus :: Maybe GenericStatement
    ,   id_equipment_bonus :: Maybe GenericStatement
    ,   id_rule :: Maybe GenericScript
    ,   id_on_add :: Maybe GenericScript  -- ^ effects when the idea is added
    ,   id_on_remove :: Maybe GenericScript  -- ^ effects when the idea is removed
    ,   id_cancel :: Maybe GenericScript -- ^ tirggers for removing the idea
    ,   id_do_effect :: Maybe GenericScript -- ^ requirements for the idea's modifiers to work
    ,   id_allowed_civil_war :: Maybe GenericScript
    ,   id_traits :: Maybe GenericScript
    ,   id_category :: Text
    ,   id_path :: FilePath -- ^ Source file
    ,   id_cost :: Maybe Double
    } deriving (Show)

-- | Decision data.
data HOI4Decisioncat = HOI4Decisioncat
    {   decc_name :: Text -- ^ Decision category ID
    ,   decc_name_loc :: Maybe Text -- ^ Localized decision category name
    ,   decc_desc_loc :: Maybe Text
    ,   decc_icon :: Text
    ,   decc_picture :: Maybe Text
    ,   decc_custom_icon :: Maybe GenericScript
    ,   decc_visible :: Maybe GenericScript
    ,   decc_available :: Maybe GenericScript
    ,   decc_visiblity_type :: Maybe Text
    ,   decc_allowed :: Maybe GenericScript -- ^ Conditions that allow the category to appear
    ,   decc_visible_when_empty :: Maybe Text
    ,   decc_scripted_gui :: Maybe Text
    ,   decc_highlight_states :: Maybe GenericScript
    ,   decc_on_map_area :: Maybe GenericScript
    ,   decc_path :: FilePath -- ^ Source file
    } deriving (Show)

data HOI4DecisionCost
    = HOI4DecisionCostSimple Int
    | HOI4DecisionCostVariable Text
    deriving Show

data HOI4DecisionIcon
    = HOI4DecisionIconSimple Text
    | HOI4DecisionIconScript GenericScript
    deriving Show

-- | Decision data.
data HOI4Decision = HOI4Decision
    {   dec_name :: Text -- ^ Decision ID
    ,   dec_name_loc :: Text -- ^ Localized decision name
    ,   dec_desc :: Maybe Text -- ^ Descriptive text (shown on hover)
    ,   dec_icon :: Maybe HOI4DecisionIcon -- ^ Icon for the decision
    ,   dec_allowed :: Maybe GenericScript -- ^ Conditions that allow the player/AI to
                                           --   take the decision
    ,   dec_target_root_trigger :: Maybe GenericScript
    ,   dec_visible :: Maybe GenericScript
    ,   dec_available :: Maybe GenericScript
    ,   dec_is_good :: Bool -- ^ changes tooltip on whether timing out or compeleting mission is desirable, default is no and assumes complete_effect is desirable
    ,   dec_complete_effect :: Maybe GenericScript -- ^ the block of effects that gets executed immediately
                                                   --   when the decision is selected (Starting the timer if it has one).
    ,   dec_days_re_enable :: Maybe Int
    ,   dec_fire_only_once :: Bool
    ,   dec_cost :: Maybe HOI4DecisionCost
    ,   dec_custom_cost_trigger  :: Maybe GenericScript
    ,   dec_custom_cost_text :: Maybe Text
    ,   dec_days_remove :: Maybe Int
    ,   dec_remove_effect :: Maybe GenericScript
    ,   dec_remove_trigger :: Maybe GenericScript
    ,   dec_modifier :: Maybe GenericStatement
    ,   dec_cancel_trigger ::  Maybe GenericScript
    ,   dec_cancel_effect ::  Maybe GenericScript

    ,   dec_days_mission_timeout :: Maybe Int
    ,   dec_activation :: Maybe GenericScript
    ,   dec_selectable_mission :: Bool
    ,   dec_timeout_effect :: Maybe GenericScript
    ,   dec_cancel_if_not_visible :: Bool

    ,   dec_targets :: Maybe GenericScript
    ,   dec_target_array :: Maybe Text
    ,   dec_targets_dynamic :: Bool
    ,   dec_target_trigger :: Maybe GenericScript
    ,   dec_targeted_modifier :: Maybe GenericScript
    ,   dec_state_target :: Maybe Text
    ,   dec_ai_will_do :: Maybe AIWillDo -- ^ Factors affecting whether an AI
                                         --   will take the decision when available
    ,   dec_path :: FilePath -- ^ Source file
    ,   dec_cat :: Text -- ^ Category of the decision
    } deriving (Show)

data HOI4DynamicModifier = HOI4DynamicModifier
    {   dmodName :: Text
    ,   dmodLocName :: Maybe Text
    ,   dmodPath :: FilePath
    ,   dmodIcon :: Maybe Text
    ,   dmodEffects :: GenericScript        -- The modifier to apply when the triggered modifier is active
    ,   dmodEnable :: GenericScript      -- Whether the triggered modifier is active
    ,   dmodRemoveTrigger :: Maybe GenericScript        -- Whether the triggered modifier is removed
    } deriving (Show)

data HOI4Modifier = HOI4Modifier
    {   modName :: Text
    ,   modLocName :: Maybe Text
    ,   modPath :: FilePath
    ,   modIcon :: Maybe Text
    ,   modEffects :: GenericScript        -- The modifier to apply when the triggered modifier is active
    ,   modRemoveTrigger :: Maybe GenericScript        -- Whether the triggered modifier is removed
    } deriving (Show)

data HOI4OpinionModifier = HOI4OpinionModifier
    {   omodName :: Text
    ,   omodLocName :: Maybe Text
    ,   omodPath :: FilePath
    ,   omodValue :: Maybe Double
    ,   omodMax :: Maybe Double
    ,   omodMin :: Maybe Double
    ,   omodDecay :: Maybe Double
    ,   omodDays :: Maybe Double
    ,   omodMonths :: Maybe Double
    ,   omodYears :: Maybe Double
    ,   omodTrade :: Maybe Bool
    ,   omodTarget :: Maybe Bool
    } deriving (Show)

--data HOI4NationalFocusIcon
--    = HOI4NationalFocusIconSimple Text
--    | HOI4NationalFocusIconScript GenericScript
--    deriving Show

data HOI4NationalFocus = HOI4NationalFocus
    {   nf_id :: Text
    ,   nf_name_loc :: Text
    ,   nf_name_desc :: Maybe Text
    ,   nf_text :: Maybe Text
    ,   nf_icon :: Text
    ,   nf_cost :: Double
    ,   nf_allow_branch  :: Maybe GenericScript
    ,   nf_prerequisite  :: [Maybe GenericScript]
    ,   nf_mutually_exclusive :: Maybe GenericScript
    ,   nf_available :: Maybe GenericScript
    ,   nf_bypass :: Maybe GenericScript
    ,   nf_cancel :: Maybe GenericScript
    ,   nf_cancelable :: Maybe Text
    ,   nf_historical_ai :: Maybe Text
    ,   nf_available_if_capitulated :: Maybe Text
    ,   nf_cancel_if_invalid :: Maybe Text
    ,   nf_continue_if_invalid :: Maybe Text
    ,   nf_will_lead_to_war_with :: Maybe Text
    ,   nf_search_filters :: Maybe Text
    ,   nf_select_effect :: Maybe GenericScript
    ,   nf_ai_will_do :: Maybe Text
    ,   nf_completion_reward :: Maybe GenericScript
    ,   nf_complete_tooltip :: Maybe GenericScript
    ,   nf_joint_complete_origin :: Maybe GenericScript
    ,   nf_joint_complete_member :: Maybe GenericScript
    ,   nf_joint_trigger :: Maybe GenericScript
    ,   nf_path :: FilePath -- ^ Source file
    } deriving (Show)

data HOI4CountryHistory = HOI4CountryHistory
    {   chTag :: Text
    ,   chRulingTag :: Text
    } deriving (Show)

data HOI4Advisor = HOI4Advisor
    {   adv_advisor_slot :: Text
    ,   adv_cha_id     :: Text
    ,   adv_cha_name     :: Text
    ,   adv_idea_token   :: Text
    ,   adv_cha_portrait    :: Maybe Text
    ,   adv_traits       :: Maybe [Text]
    ,   adv_allowed      :: Maybe GenericScript
    ,   adv_visible      :: Maybe GenericScript
    ,   adv_available    :: Maybe GenericScript
    ,   adv_on_add       :: Maybe GenericScript
    ,   adv_on_remove    :: Maybe GenericScript
    ,   adv_modifier     :: Maybe GenericStatement
    ,   adv_research_bonus :: Maybe GenericStatement
    ,   adv_cost        :: Maybe Double
    ,   adv_can_be_fired :: Bool
    ,   adv_path         :: FilePath -- ^ Source file
    } deriving (Show)

data HOI4Character = HOI4Character
    {   cha_id          :: Text
    ,   cha_name        :: Text
    ,   cha_loc_name    :: Text
    ,   cha_portrait    :: Maybe Text
--    ,   chaId :: Maybe Int -- ^ legacy character id system is sometimes still used,
                         --   negative numbers count as not being there
    ,   cha_leader_traits :: Maybe [Text]
    ,   cha_leader_ideology :: Maybe Text
    ,   cha_advisor :: Maybe [HOI4Advisor]
    ,   cha_path         :: FilePath -- ^ Source file
    } deriving (Show)

data HOI4CountryLeaderTrait = HOI4CountryLeaderTrait
    {   clt_id :: Text
    ,   clt_name :: Text
    ,   clt_loc_name :: Maybe Text
    ,   clt_path :: FilePath
    ,   clt_targeted_modifier :: Maybe GenericScript
    ,   clt_equipment_bonus :: Maybe GenericStatement
    ,   clt_hidden_modifier :: Maybe GenericStatement
    ,   clt_modifier :: Maybe GenericScript
    } deriving (Show)

data HOI4UnitLeaderTrait = HOI4UnitLeaderTrait
    {   ult_id :: Text
    ,   ult_loc_name :: Maybe Text
    ,   ult_path :: FilePath
    ,   ult_modifier :: Maybe GenericStatement
    ,   ult_trait_xp_factor :: Maybe GenericStatement
    ,   ult_non_shared_modifier :: Maybe GenericStatement
    ,   ult_corps_commander_modifier :: Maybe GenericStatement
    ,   ult_field_marshal_modifier :: Maybe GenericStatement
    ,   ult_sub_unit_modifiers :: Maybe GenericStatement
    ,   ult_attack_skill :: Maybe Double
    ,   ult_defense_skill :: Maybe Double
    ,   ult_planning_skill :: Maybe Double
    ,   ult_logistics_skill :: Maybe Double
    ,   ult_maneuvering_skill :: Maybe Double
    ,   ult_coordination_skill :: Maybe Double
    } deriving (Show)

data HOI4BopRange = HOI4BopRange
    {   bop_id :: Text
    ,   bop_on_activate :: Maybe GenericScript
    ,   bop_on_deactivate :: Maybe GenericScript
    ,   bop_path :: FilePath
    } deriving (Show)

data HOI4Technology = HOI4Technology
    {   tech_id :: Text
    ,   tech_loc :: Text
    ,   tech_desc :: Maybe Text
    ,   tech_icon :: Text
    ,   tech_dependecies :: Maybe [Text]
    ,   tech_equipment :: Maybe [Text]
    ,   tech_units :: Maybe [Text]
    ,   tech_globalmod :: Maybe [Text]
    ,   tech_unitmod :: Maybe [Text]
    ,   tech_cost :: Double
    ,   tech_start_year :: Int
    ,   tech_doctrine :: Bool
    ,   tech_on_complete_limit :: Maybe GenericScript
    ,   tech_on_complete :: Maybe GenericScript
    ,   tech_filepath :: FilePath
    } deriving (Show)

------------------------------
-- Shared lower level types --
------------------------------

-- | Scopes
data HOI4Scope
    = HOI4NoScope
    | HOI4Country
    | HOI4ScopeState
    | HOI4UnitLeader
    | HOI4Operative
    | HOI4ScopeCharacter
    | HOI4Division
    | HOI4From -- ^ Usually country or state, varies by context
    | HOI4Misc -- ^ custom for the parser, is used for var and event_target,
               --   because the scope depends on what is loaded into the var
    | HOI4Custom -- ^ custom for the parser, is usually defined by the code
                 --   example for ace_killed_by_ace events in on_actions PREV = enemy ace
    deriving (Show, Eq, Ord, Enum, Bounded)

-- | AI decision factors.
data AIWillDo = AIWillDo
    {   awd_base :: Maybe Double
    ,   awd_modifiers :: [AIModifier]
    } deriving (Show)
-- | Modifiers for AI decision factors.
data AIModifier = AIModifier
    {   aim_factor :: Maybe Double
    ,   aim_add :: Maybe Double
    ,   aim_triggers :: GenericScript
    } deriving (Show)
-- | Empty decision factor.
newAIWillDo :: AIWillDo
newAIWillDo = AIWillDo Nothing []
-- | Empty modifier.
newAIModifier :: AIModifier
newAIModifier = AIModifier Nothing Nothing []

-- | Parse an @ai_will_do@ clause.
aiWillDo :: GenericScript -> AIWillDo
aiWillDo = foldl' aiWillDoAddSection newAIWillDo
aiWillDoAddSection :: AIWillDo -> GenericStatement -> AIWillDo
aiWillDoAddSection awd [pdx| $left = %right |] = case T.toLower left of
    "base" -> maybe awd
        (\fac -> awd { awd_base = Just fac })
        (floatRhs right)
    "factor" -> maybe awd
        (\fac -> awd { awd_base = Just fac })
        (floatRhs right)
    "modifier" -> case right of
        CompoundRhs scr -> awd { awd_modifiers = awd_modifiers awd ++ [awdModifier scr] }
        _               -> awd
    _ -> awd
aiWillDoAddSection awd _ = awd

-- | Parse a @modifier@ subclause for an @ai_will_do@ clause.
awdModifier :: GenericScript -> AIModifier
awdModifier = foldl' awdModifierAddSection newAIModifier
awdModifierAddSection :: AIModifier -> GenericStatement -> AIModifier
awdModifierAddSection aim stmt@[pdx| $left = %right |] = case T.toLower left of
    "factor" -> maybe aim
        (\fac -> aim { aim_factor = Just fac })
        (floatRhs right)
    "add" -> maybe aim
        (\add -> aim { aim_add = Just add })
        (floatRhs right)
    _ -> -- the rest of the statements are just the conditions.
        aim { aim_triggers = aim_triggers aim ++ [stmt] }
awdModifierAddSection aim stmt@[pdx| $_left > %_right |] = aim { aim_triggers = aim_triggers aim ++ [stmt] }
awdModifierAddSection aim stmt@[pdx| $_left < %_right |] = aim { aim_triggers = aim_triggers aim ++ [stmt] }
awdModifierAddSection aim _ = aim
