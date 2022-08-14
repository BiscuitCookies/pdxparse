{-|
Module      : HOI4.Settings
Description : Interface for Hearts of Iron IV backend
-}
module HOI4.Settings (
        HOI4 (..)
    ,   module HOI4.Types
    ) where

import Debug.Trace (trace, traceM)

import Control.Monad (join, when, forM, filterM, void, unless)
import Control.Monad.Trans (MonadIO (..), liftIO)
import Control.Monad.Reader (MonadReader (..), ReaderT (..), asks)
import Control.Monad.State (MonadState (..), StateT (..), modify, gets)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import Data.Maybe (listToMaybe, catMaybes)

import Data.Text (Text, toLower)
import Data.Monoid ((<>))

import System.Directory (getDirectoryContents, doesFileExist, doesDirectoryExist)
import System.FilePath ((</>), isExtensionOf)
import System.IO (hPutStrLn, stderr)

import Abstract -- everything
import QQ (pdx)
import FileIO (buildPath, readScript, readSpecificScript)
import SettingsTypes ( PPT, Settings (..), Game (..), L10nScheme (..)
                     , IsGame (..), IsGameData (..), IsGameState (..)
                     , getGameL10nIfPresent
                     , safeIndex, safeLast, CLArgs (..))
import HOI4.Types -- everything
import Yaml (LocEntry (..))

-- Handlers
import HOI4.Decisions (parseHOI4Decisioncats, writeHOI4DecisionCats
                      ,parseHOI4Decisions, writeHOI4Decisions
                      ,findActivatedDecisionsInEvents, findActivatedDecisionsInDecisions
                      ,findActivatedDecisionsInOnActions, findActivatedDecisionsInNationalFocus)
import HOI4.Ideas (parseHOI4Ideas
    --, writeHOI4Ideas
    )
import HOI4.Modifiers (
                      parseHOI4OpinionModifiers, writeHOI4OpinionModifiers
                    , parseHOI4DynamicModifiers, writeHOI4DynamicModifiers)
import HOI4.NationalFocus(parseHOI4NationalFocuses, writeHOI4NationalFocuses)
import HOI4.Events (parseHOI4Events, writeHOI4Events
                   , findTriggeredEventsInEvents, findTriggeredEventsInDecisions
                   , findTriggeredEventsInOnActions, findTriggeredEventsInNationalFocus)
import HOI4.Misc (parseHOI4CountryHistory, parseHOI4Interface, parseHOI4Characters)

-- | Temporary (?) fix for CHI and PRC both localizing to "China"
-- Can be extended/removed as necessary
fixLocalization :: Settings -> Settings
fixLocalization s =
    let
        lan  = language s
        l10n = gameL10n s
        l10nForLan = HM.findWithDefault HM.empty lan l10n
        findKey key = content $ HM.findWithDefault (LocEntry 0 key) key l10nForLan
        chiLoc = findKey "CHI"
        newHavLoc = chiLoc <> " (CHI)"
        newL10n = HM.insert "CHI" (LocEntry 0 newHavLoc) l10nForLan
    in
        if chiLoc == findKey "PRC" then
            trace ("Note: Applying localization fix for CHI/PRC: " ++ show chiLoc ++ " -> " ++ show newHavLoc) $
                s { gameL10n = HM.insert lan newL10n l10n }
        else
            trace "Warning: fixLocalization hack for CHI/PRC in HOI4/Settings.hs no longer needed!" s

-- | HOI4 game type. This is only interesting for its instances.
data HOI4 = HOI4
instance IsGame HOI4 where
    locScheme _  = L10nQYAML
    readScripts  = readHOI4Scripts
    parseScripts = parseHOI4Scripts
    writeScripts = writeHOI4Scripts
    data GameData HOI4 = HOI4D { hoi4d :: HOI4Data }
    data GameState HOI4 = HOI4S { hoi4s :: HOI4State }
    runWithInitState HOI4 settings st =
        void (runReaderT
                (runStateT st (HOI4D $ HOI4Data {
                    hoi4settings = fixLocalization settings
                ,   hoi4events = HM.empty
                ,   hoi4eventScripts = HM.empty
                ,   hoi4decisioncatScripts = HM.empty
                ,   hoi4decisioncats = HM.empty
                ,   hoi4decisions = HM.empty
                ,   hoi4decisionScripts = HM.empty
                ,   hoi4ideas = HM.empty
                ,   hoi4ideaScripts = HM.empty
                ,   hoi4opmods = HM.empty
                ,   hoi4opmodScripts = HM.empty
                ,   hoi4eventTriggers = HM.empty
                ,   hoi4decisionTriggers = HM.empty
                ,   hoi4onactionsScripts = HM.empty
                ,   hoi4dynamicmodifiers = HM.empty
                ,   hoi4dynamicmodifierScripts = HM.empty
                ,   hoi4nationalfocusScripts = HM.empty
                ,   hoi4nationalfocus = HM.empty
                ,   hoi4countryHistory = HM.empty
                ,   hoi4countryHistoryScripts = HM.empty
                ,   hoi4interfacegfxScripts = HM.empty
                ,   hoi4interfacegfx = HM.empty
                ,   hoi4characterScripts = HM.empty
                ,   hoi4characters = HM.empty
                -- unused
                ,   hoi4extraScripts = HM.empty
                ,   hoi4extraScriptsCountryScope = HM.empty
                ,   hoi4extraScriptsProvinceScope = HM.empty
                ,   hoi4extraScriptsModifier = HM.empty
                }))
                (HOI4S $ HOI4State {
                    hoi4currentFile = Nothing
                ,   hoi4currentIndent = Nothing
                ,   hoi4scopeStack = []
                ,   hoi4IsInEffect = False
                }))
    type Scope HOI4 = HOI4Scope
    scope s = local $ \(HOI4S st) -> HOI4S $
        st { hoi4scopeStack = s : hoi4scopeStack st }
    getCurrentScope = asks $ listToMaybe . hoi4scopeStack . hoi4s
    getPrevScope = asks $ safeIndex 1 . hoi4scopeStack . hoi4s
    getRootScope = asks $ safeLast . hoi4scopeStack . hoi4s
    getScopeStack = asks $ hoi4scopeStack . hoi4s
    getIsInEffect = asks $ hoi4IsInEffect . hoi4s
    setIsInEffect b = local $ \(HOI4S st) -> HOI4S $ st { hoi4IsInEffect = b }

instance HOI4Info HOI4 where
    getEventTitle eid = do
        HOI4D ed <- get
        let evts = hoi4events ed
            mevt = HM.lookup eid evts
        case mevt of
            Nothing -> return Nothing
            Just evt -> case hoi4evt_title evt of
                [] -> return Nothing
                [HOI4EvtTitleSimple key] -> getGameL10nIfPresent key
                titles -> return Nothing
    getEventScripts = do
        HOI4D ed <- get
        return (hoi4eventScripts ed)
    setEventScripts scr = modify $ \(HOI4D ed) -> HOI4D $ ed {
            hoi4eventScripts = scr
        }
    getEvents = do
        HOI4D ed <- get
        return (hoi4events ed)
    getIdeaScripts = do
        HOI4D ed <- get
        return (hoi4ideaScripts ed)
    getIdeas = do
        HOI4D ed <- get
        return (hoi4ideas ed)
    getDecisioncatScripts = do
        HOI4D ed <- get
        return (hoi4decisioncatScripts ed)
    getDecisionScripts = do
        HOI4D ed <- get
        return (hoi4decisionScripts ed)
    getDecisioncats = do
        HOI4D ed <- get
        return (hoi4decisioncats ed)
    getDecisions = do
        HOI4D ed <- get
        return (hoi4decisions ed)
    getOpinionModifierScripts = do
        HOI4D ed <- get
        return (hoi4opmodScripts ed)
    getOpinionModifiers = do
        HOI4D ed <- get
        return (hoi4opmods ed)
    getEventTriggers = do
        HOI4D ed <- get
        return (hoi4eventTriggers ed)
    getDecisionTriggers = do
        HOI4D ed <- get
        return (hoi4decisionTriggers ed)
    getOnActionsScripts = do
        HOI4D ed <- get
        return (hoi4onactionsScripts ed)
    getDynamicModifierScripts = do
        HOI4D ed <- get
        return (hoi4dynamicmodifierScripts ed)
    getDynamicModifiers = do
        HOI4D ed <- get
        return (hoi4dynamicmodifiers ed)
    getNationalFocusScripts = do
        HOI4D ed <- get
        return (hoi4nationalfocusScripts ed)
    getNationalFocus = do
        HOI4D ed <- get
        return (hoi4nationalfocus ed)

    getCountryHistoryScripts = do
        HOI4D ed <- get
        return (hoi4countryHistoryScripts ed)
    getCountryHistory = do
        HOI4D ed <- get
        return (hoi4countryHistory ed)
    getInterfaceGFXScripts = do
        HOI4D ed <- get
        return (hoi4interfacegfxScripts ed)
    getInterfaceGFX = do
        HOI4D ed <- get
        return (hoi4interfacegfx ed)
    getCharacterScripts = do
        HOI4D ed <- get
        return (hoi4characterScripts ed)
    getCharacters = do
        HOI4D ed <- get
        return (hoi4characters ed)
-- unused
    getExtraScripts = do
        HOI4D ed <- get
        return (hoi4extraScripts ed)
    getExtraScriptsCountryScope = do
        HOI4D ed <- get
        return (hoi4extraScriptsCountryScope ed)
    getExtraScriptsProvinceScope = do
        HOI4D ed <- get
        return (hoi4extraScriptsProvinceScope ed)
    getExtraScriptsModifier = do
        HOI4D ed <- get
        return (hoi4extraScriptsModifier ed)

instance IsGameData (GameData HOI4) where
    getSettings (HOI4D ed) = hoi4settings ed

instance IsGameState (GameState HOI4) where
    currentFile (HOI4S es) = hoi4currentFile es
    modifyCurrentFile cf (HOI4S es) = HOI4S $ es {
            hoi4currentFile = cf
        }
    currentIndent (HOI4S es) = hoi4currentIndent es
    modifyCurrentIndent ci (HOI4S es) = HOI4S $ es {
            hoi4currentIndent = ci
        }

-- | Read all scripts in a directory.
--
-- Return: for each file, its path relative to the game root and the parsed
--         script.
readHOI4Scripts :: forall m. MonadIO m => PPT HOI4 m ()
readHOI4Scripts = do
    settings <- gets getSettings
    let readOneScript :: Bool -> String -> String -> PPT HOI4 m (String, GenericScript)
        readOneScript specific category target = do
            content <- if specific then liftIO $ readScript settings target else liftIO $ readSpecificScript settings target
--            traceM (show target)
            when (null content) $
                liftIO $ hPutStrLn stderr $
                    "Warning: " ++ target
                        ++ " contains no scripts - failed parse? Expected feature type "
                        ++ category
            return (target, content)

        readHOI4Script :: String -> PPT HOI4 m (HashMap String GenericScript)
        readHOI4Script category = do
            let sourceSubdir = case category of
                    "ideas" -> "common" </> "ideas"
                    "opinion_modifiers" -> "common" </> "opinion_modifiers"
                    "on_actions" -> "common" </> "on_actions"
                    "dynamic_modifiers" -> "common" </> "dynamic_modifiers"
                    "decisions" -> "common" </> "decisions"
                    "decisioncats" -> "common" </> "decisions" </> "categories"
                    "national_focus" -> "common" </> "national_focus"

                    "country_history" -> "history" </> "countries"
                    "characters" -> "common" </> "characters"
                    _          -> category
                sourceDir = buildPath settings sourceSubdir
            files <- liftIO (filterM (doesFileExist . buildPath settings . (sourceSubdir </>))
                                    =<< filterM (pure . isExtensionOf ".txt")
                                     =<< getDirectoryContents sourceDir)
            results <- forM files $ \filename -> readOneScript True category (sourceSubdir </> filename)
            return $ foldl (flip (uncurry HM.insert)) HM.empty results

        readHOI4SpecificScript :: String -> PPT HOI4 m (HashMap String GenericScript)
        readHOI4SpecificScript category = do
            settings <- gets getSettings
            let sourceSubdir = case category of
                    "interfacegfx" -> "interface"
                    _          -> category
                sourceDirReplace = gameModPath settings </> sourceSubdir </> "replace"
                sourceDirMod = gameModPath settings </> sourceSubdir
                sourceDir = gamePath settings </> sourceSubdir
            replaceexists <- liftIO $ doesDirectoryExist sourceDirReplace
            modexists <- liftIO $ doesDirectoryExist sourceDirMod
            filesSource <- let result
                                | replaceexists && modexists = do
                                    repPath <- buildCompletePath sourceDirReplace
                                    modPath <- buildCompletePath sourceDirMod
                                    soPath <- buildCompletePath sourceDir
                                    return (Just repPath, Just modPath, Just soPath)
                                | modexists = do
                                    modPath <- buildCompletePath sourceDirMod
                                    soPath <- buildCompletePath sourceDir
                                    return (Nothing, Just modPath, Just soPath)
                                | otherwise = do
                                    soPath <- buildCompletePath sourceDir
                                    return (Nothing, Nothing, Just soPath)
                            in result
            let files = case filesSource of
                    (Just replaces, Just mods, Just sources) ->
                        map (sourceDirReplace </>) replaces ++
                        map (sourceDirMod </>) mods ++
                        map (sourceDir </>) sources
                    (_, Just mods, Just sources) ->
                        map (sourceDirMod </>) mods ++
                        map (sourceDir </>) sources
                    (_, _, Just sources) -> map (sourceDir </>) sources
                    _ -> error "Something went wrong with the gamepath"
            results <- forM files $ \filename -> readOneScript False category filename
            return $ foldl (flip (uncurry HM.insert)) HM.empty results

        buildCompletePath :: FilePath -> PPT HOI4 m [FilePath]
        buildCompletePath path = liftIO (filterM (doesFileExist . (path </>))
                                    =<< filterM (pure . isExtensionOf ".gfx")
                                     =<< getDirectoryContents path)

    ideasScripts <- readHOI4Script "ideas"
    decisioncats <- readHOI4Script "decisioncats"
    decisions <- readHOI4Script "decisions"
    events <- readHOI4Script "events"
    opinion_modifiers <- readHOI4Script "opinion_modifiers"
    on_actions <- readHOI4Script "on_actions"
    dynamic_modifiers <- readHOI4Script "dynamic_modifiers"
    national_focus <- readHOI4Script "national_focus"

    country_history <- readHOI4Script "country_history"
    characterScripts <- readHOI4Script "characters"
    interface_gfx <- readHOI4SpecificScript "interfacegfx"

    modify $ \(HOI4D s) -> HOI4D $ s {
            hoi4ideaScripts = ideasScripts
        ,   hoi4decisioncatScripts = decisioncats
        ,   hoi4decisionScripts = decisions
        ,   hoi4eventScripts = events
        ,   hoi4opmodScripts = opinion_modifiers
        ,   hoi4onactionsScripts = on_actions
        ,   hoi4dynamicmodifierScripts = dynamic_modifiers
        ,   hoi4countryHistoryScripts = country_history

        ,   hoi4nationalfocusScripts = national_focus
        ,   hoi4characterScripts = characterScripts
        ,   hoi4interfacegfxScripts = interface_gfx
        }


-- | Interpret the script ASTs as usable data.
parseHOI4Scripts :: Monad m => PPT HOI4 m ()
parseHOI4Scripts = do
    -- Need idea groups and modifiers before everything else
    ideas <- parseHOI4Ideas =<< getIdeaScripts
    opinionModifiers <- parseHOI4OpinionModifiers =<< getOpinionModifierScripts
    dynamicModifiers <- parseHOI4DynamicModifiers =<< getDynamicModifierScripts
    decisioncats <- parseHOI4Decisioncats =<< getDecisioncatScripts
    decisions <- parseHOI4Decisions =<< getDecisionScripts
    events <- parseHOI4Events =<< getEventScripts
    on_actions <- getOnActionsScripts
    nationalFocus <- parseHOI4NationalFocuses =<< getNationalFocusScripts

    countryHistory <- parseHOI4CountryHistory =<< getCountryHistoryScripts
    interfaceGFX <- parseHOI4Interface =<< getInterfaceGFXScripts
    characters <- parseHOI4Characters =<< getCharacterScripts

    let te1 = findTriggeredEventsInEvents HM.empty (HM.elems events)
        te2 = findTriggeredEventsInDecisions te1 (HM.elems decisions)
        te3 = findTriggeredEventsInOnActions te2 (concat (HM.elems on_actions))
        te4 = findTriggeredEventsInNationalFocus te3 (HM.elems nationalFocus)
    let td1 = findActivatedDecisionsInEvents HM.empty (HM.elems events)
        td2 = findActivatedDecisionsInDecisions td1 (HM.elems decisions)
        td3 = findActivatedDecisionsInOnActions td2 (concat (HM.elems on_actions))
        td4 = findActivatedDecisionsInNationalFocus td3 (HM.elems nationalFocus)
    modify $ \(HOI4D s) -> HOI4D $
            s { hoi4events = events
            ,   hoi4decisioncats = decisioncats
            ,   hoi4decisions = decisions
            ,   hoi4ideas = ideas
            ,   hoi4opmods = opinionModifiers
            ,   hoi4nationalfocus = nationalFocus
            ,   hoi4eventTriggers = te4
            ,   hoi4decisionTriggers = td4
            ,   hoi4dynamicmodifiers = dynamicModifiers

            ,   hoi4countryHistory = countryHistory
            ,   hoi4characters = characters
            ,   hoi4interfacegfx = interfaceGFX
            }

-- | Output the game data as wiki text.
writeHOI4Scripts :: (HOI4Info g, MonadIO m) => PPT g m ()
writeHOI4Scripts = do
--        liftIO $ putStrLn "Writing ideas."
--        writeHOI4Ideas
        liftIO $ putStrLn "Writing events."
        writeHOI4Events
        liftIO $ putStrLn "Writing decision categories."
        writeHOI4DecisionCats
        liftIO $ putStrLn "Writing decisions."
        writeHOI4Decisions
        liftIO $ putStrLn "Writing national focuses."
        writeHOI4NationalFocuses
        liftIO $ putStrLn "Writing opinion modifiers."
        writeHOI4OpinionModifiers
        liftIO $ putStrLn "Writing dynamic modifiers."
        writeHOI4DynamicModifiers
