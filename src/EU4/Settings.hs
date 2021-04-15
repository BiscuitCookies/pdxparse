{-|
Module      : EU4.Settings
Description : Interface for Europa Universalis IV backend
-}
module EU4.Settings (
        EU4 (..)
    ,   module EU4.Types
    ) where

import Debug.Trace (trace, traceM)

import Control.Monad (join, when, forM, filterM, void)
import Control.Monad.Trans (MonadIO (..), liftIO)
import Control.Monad.Reader (MonadReader (..), ReaderT (..), asks)
import Control.Monad.State (MonadState (..), StateT (..), modify, gets)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import Data.Maybe (listToMaybe)

import Data.Text (Text)

import System.Directory (getDirectoryContents, doesFileExist)
import System.FilePath ((</>))
import System.IO (hPutStrLn, stderr)

import Abstract -- everything
import FileIO (buildPath, readScript)
import SettingsTypes ( PPT, Settings (..), Game (..), L10nScheme (..)
                     , IsGame (..), IsGameData (..), IsGameState (..)
                     , getGameL10nIfPresent
                     , safeIndex, safeLast)
import EU4.Types -- everything
--import Text.PrettyPrint.Leijen.Text (Doc)
--import qualified Text.PrettyPrint.Leijen.Text as PP

-- Handlers
import EU4.Decisions (parseEU4Decisions, writeEU4Decisions)
import EU4.IdeaGroups (parseEU4IdeaGroups, writeEU4IdeaGroups)
import EU4.Modifiers ( parseEU4Modifiers, writeEU4Modifiers
                     , parseEU4OpinionModifiers, writeEU4OpinionModifiers)
import EU4.Missions (parseEU4Missions , writeEU4Missions)
import EU4.Events (parseEU4Events, writeEU4Events
                   , findTriggeredEventsInEvents, findTriggeredEventsInDecisions
                   , findTriggeredEventsInOnActions, findTriggeredEventsInDisasters
                   , findTriggeredEventsInMissions)
--import EU4.Policies (parseEU4Policies, writeEU4Policies)

-- | EU4 game type. This is only interesting for its instances.
data EU4 = EU4
instance IsGame EU4 where
    locScheme _  = L10nQYAML
    readScripts  = readEU4Scripts
    parseScripts = parseEU4Scripts
    writeScripts = writeEU4Scripts
    data GameData EU4 = EU4D { eu4d :: EU4Data }
    data GameState EU4 = EU4S { eu4s :: EU4State }
    runWithInitState EU4 settings st =
        void (runReaderT
                (runStateT st (EU4D $ EU4Data {
                    eu4settings = settings
                ,   eu4events = HM.empty
                ,   eu4eventScripts = HM.empty
                ,   eu4decisions = HM.empty
                ,   eu4decisionScripts = HM.empty
                ,   eu4ideaGroups = HM.empty
                ,   eu4ideaGroupScripts = HM.empty
                ,   eu4modifiers = HM.empty
                ,   eu4modifierScripts = HM.empty
                ,   eu4opmods = HM.empty
                ,   eu4opmodScripts = HM.empty
                ,   eu4missionScripts = HM.empty
                ,   eu4missions = HM.empty
                ,   eu4eventTriggers = HM.empty
                ,   eu4onactionsScripts = HM.empty
                ,   eu4disasterScripts = HM.empty
                }))
                (EU4S $ EU4State {
                    eu4currentFile = Nothing
                ,   eu4currentIndent = Nothing
                ,   eu4scopeStack = []
                }))
    type Scope EU4 = EU4Scope
    scope s = local $ \(EU4S st) -> EU4S $
        st { eu4scopeStack = s : eu4scopeStack st }
    getCurrentScope = asks $ listToMaybe . eu4scopeStack . eu4s
    getPrevScope = asks $ safeIndex 1 . eu4scopeStack . eu4s
    getRootScope = asks $ safeLast . eu4scopeStack . eu4s
    getScopeStack = asks $ eu4scopeStack . eu4s

instance EU4Info EU4 where
    getEventTitle eid = do
        EU4D ed <- get
        let evts = eu4events ed
            mevt = HM.lookup eid evts
        case mevt of
            Nothing -> return Nothing
            Just evt -> case eu4evt_title evt of
                Nothing -> return Nothing
                Just title -> getGameL10nIfPresent title
    getEventScripts = do
        EU4D ed <- get
        return (eu4eventScripts ed)
    setEventScripts scr = modify $ \(EU4D ed) -> EU4D $ ed {
            eu4eventScripts = scr
        }
    getEvents = do
        EU4D ed <- get
        return (eu4events ed)
    getIdeaGroupScripts = do
        EU4D ed <- get
        return (eu4ideaGroupScripts ed)
    getIdeaGroups = do
        EU4D ed <- get
        return (eu4ideaGroups ed)
    getDecisionScripts = do
        EU4D ed <- get
        return (eu4decisionScripts ed)
    getDecisions = do
        EU4D ed <- get
        return (eu4decisions ed)
    getModifierScripts = do
        EU4D ed <- get
        return (eu4modifierScripts ed)
    getModifiers = do
        EU4D ed <- get
        return (eu4modifiers ed)
    getOpinionModifierScripts = do
        EU4D ed <- get
        return (eu4opmodScripts ed)
    getOpinionModifiers = do
        EU4D ed <- get
        return (eu4opmods ed)
    getMissionScripts = do
        EU4D ed <- get
        return (eu4missionScripts ed)
    getMissions = do
        EU4D ed <- get
        return (eu4missions ed)
    getEventTriggers = do
        EU4D ed <- get
        return (eu4eventTriggers ed)
    getOnActionsScripts = do
        EU4D ed <- get
        return (eu4onactionsScripts ed)
    getDisasterScripts = do
        EU4D ed <- get
        return (eu4disasterScripts ed)

instance IsGameData (GameData EU4) where
    getSettings (EU4D ed) = eu4settings ed

instance IsGameState (GameState EU4) where
    currentFile (EU4S es) = eu4currentFile es
    modifyCurrentFile cf (EU4S es) = EU4S $ es {
            eu4currentFile = cf
        }
    currentIndent (EU4S es) = eu4currentIndent es
    modifyCurrentIndent ci (EU4S es) = EU4S $ es {
            eu4currentIndent = ci
        }

-- | Read all scripts in a directory.
--
-- Return: for each file, its path relative to the game root and the parsed
--         script.
readEU4Scripts :: forall m. MonadIO m => PPT EU4 m ()
readEU4Scripts = do
    let readEU4Script :: String -> PPT EU4 m (HashMap String GenericScript)
        readEU4Script category = do
            settings <- gets getSettings
            let sourceSubdir = case category of
                    "policies" -> "common" </> "policies"
                    "ideagroups" -> "common" </> "ideas"
                    "modifiers" -> "common" </> "event_modifiers"
                    "opinion_modifiers" -> "common" </> "opinion_modifiers"
                    "on_actions" -> "common" </> "on_actions"
                    "disasters" -> "common" </> "disasters"
                    _          -> category
                sourceDir = buildPath settings sourceSubdir
            files <- liftIO (filterM (doesFileExist . buildPath settings . (sourceSubdir </>))
                                     =<< getDirectoryContents sourceDir)
            results <- forM files $ \filename -> do
                let target = sourceSubdir </> filename
                content <- liftIO $ readScript settings target
                when (null content) $
                    liftIO $ hPutStrLn stderr $
                        "Warning: " ++ target
                            ++ " contains no scripts - failed parse? Expected feature type "
                            ++ category
                return (target, content)
            return $ foldl (flip (uncurry HM.insert)) HM.empty results

    ideaGroups <- readEU4Script "ideagroups"
    decisions <- readEU4Script "decisions"
    events <- readEU4Script "events"
    modifiers <- readEU4Script "modifiers"
    opinion_modifiers <- readEU4Script "opinion_modifiers"
    missions <- readEU4Script "missions"
    on_actions <- readEU4Script "on_actions"
    disasters <- readEU4Script "disasters"
    modify $ \(EU4D s) -> EU4D $ s {
            eu4ideaGroupScripts = ideaGroups
        ,   eu4decisionScripts = decisions
        ,   eu4eventScripts = events
        ,   eu4modifierScripts = modifiers
        ,   eu4opmodScripts = opinion_modifiers
        ,   eu4missionScripts = missions
        ,   eu4onactionsScripts = on_actions
        ,   eu4disasterScripts = disasters
        }

-- | Interpret the script ASTs as usable data.
parseEU4Scripts :: Monad m => PPT EU4 m ()
parseEU4Scripts = do
    -- Need idea groups and modifiers before everything else
    ideaGroups <- parseEU4IdeaGroups =<< getIdeaGroupScripts
    modifiers <- parseEU4Modifiers =<< getModifierScripts
    opinionModifiers <- parseEU4OpinionModifiers =<< getOpinionModifierScripts
    decisions <- parseEU4Decisions =<< getDecisionScripts
    events <- parseEU4Events =<< getEventScripts
    missions <- parseEU4Missions =<< getMissionScripts
    on_actions <- getOnActionsScripts
    disasters <- getDisasterScripts
    let te1 = findTriggeredEventsInEvents HM.empty (HM.elems events)
        te2 = findTriggeredEventsInDecisions te1 (HM.elems decisions)
        te3 = findTriggeredEventsInOnActions te2 (concat (HM.elems on_actions))
        te4 = findTriggeredEventsInDisasters te3 (concat (HM.elems disasters))
        te5 = findTriggeredEventsInMissions te4 (HM.elems missions)
    --traceM $ concat (map (\(k,v) -> (show k) ++ " -> " ++ show v ++ "\n") (HM.toList $ te5))
    modify $ \(EU4D s) -> EU4D $
            s { eu4events = events
            ,   eu4decisions = decisions
            ,   eu4ideaGroups = ideaGroups
            ,   eu4modifiers = modifiers
            ,   eu4opmods = opinionModifiers
            ,   eu4missions = missions
            ,   eu4eventTriggers = te5
            }

-- | Output the game data as wiki text.
writeEU4Scripts :: (EU4Info g, MonadIO m) => PPT g m ()
writeEU4Scripts = do
    writeEU4IdeaGroups
    writeEU4Events
    writeEU4Decisions
    writeEU4Missions
