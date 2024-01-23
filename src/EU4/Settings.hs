{-|
Module      : EU4.Settings
Description : Interface for Europa Universalis IV backend
-}
module EU4.Settings (
        EU4 (..)
    ,   module EU4.Types
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
import System.FilePath ((</>))
import System.IO (hPutStrLn, stderr)

import Abstract -- everything
import QQ (pdx)
import FileIO (buildPath, readScript, readFileRetry)
import SettingsTypes ( PPT, Settings (..), Game (..), L10nScheme (..)
                     , IsGame (..), IsGameData (..), IsGameState (..)
                     , getGameL10nIfPresent
                     , safeIndex, safeLast, CLArgs (..))
import EU4.Types -- everything
--import Text.PrettyPrint.Leijen.Text (Doc)
--import qualified Text.PrettyPrint.Leijen.Text as PP
import Yaml (LocEntry (..))

-- Handlers
import EU4.Decisions (parseEU4Decisions, writeEU4Decisions, findEstateActions)
import EU4.IdeaGroups (parseEU4IdeaGroups, writeEU4IdeaGroups)
import EU4.Modifiers ( parseEU4Modifiers, writeEU4Modifiers
                     , parseEU4OpinionModifiers, writeEU4OpinionModifiers
                     , parseEU4ProvTrigModifiers, writeEU4ProvTrigModifiers)
import EU4.Missions (parseEU4Missions , writeEU4Missions)
import EU4.Events (parseEU4Events, writeEU4Events
                   , findTriggeredEventsInEvents, findTriggeredEventsInDecisions
                   , findTriggeredEventsInOnActions, findTriggeredEventsInDisasters
                   , findTriggeredEventsInGenericScript, findTriggeredEventsInMissions
                   , findTriggeredEventsInProvinceTriggeredModifiers, findTriggeredEventsInGovernmentMechanics, findTriggeredEventsInImperialIncidents)
import EU4.Extra (writeEU4Extra, writeEU4ExtraCountryScope, writeEU4ExtraProvinceScope, writeEU4ExtraModifier)

-- | Temporary (?) fix for HAW and UHW both localizing to "Hawai'i'"
-- and for horde_ideas+horde_gov_ideas both localiying to "Horde Ideas"
-- Can be extended/removed as necessary
fixLocalizations :: Settings -> Settings
fixLocalizations s = foldr fixLocalization s [
    ("UHW", "HAW", "Hawai'i (HAW)"),
    ("horde_ideas", "horde_gov_ideas", "Horde Government Ideas")]
fixLocalization :: (Text, Text, Text) -> Settings -> Settings
fixLocalization (lockey1, lockey2, newLocForKey2) s =
    let
        lan  = language s
        l10n = gameL10n s
        l10nForLan = HM.lookupDefault HM.empty lan l10n
        findKey key = content $ HM.lookupDefault (LocEntry 0 key) key l10nForLan
        oldLocForKey2 = findKey lockey2
        newL10n = HM.insert lockey2 (LocEntry 0 newLocForKey2) l10nForLan
    in
        if oldLocForKey2 == findKey lockey1 then
            trace ("Note: Applying localization fix: " ++ show oldLocForKey2 ++ " -> " ++ show newLocForKey2) $
                s { gameL10n = HM.insert lan newL10n l10n }
        else
            trace ("Warning: fixLocalization hack for " ++ show lockey1 ++ " " ++ show lockey2 ++ " in EU4/Settings.hs no longer needed!") s

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
                    eu4settings = fixLocalizations settings
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
                ,   eu4genericScriptsForEventTriggers = HM.empty
                ,   eu4geoData = HM.empty
                ,   eu4provtrigmodifiers = HM.empty
                ,   eu4provtrigmodifierScripts = HM.empty
                ,   eu4tradeNodes = HM.empty
                ,   eu4estateActions = HM.empty
                ,   eu4scriptedEffectsForEstates = ""
                ,   eu4extraScripts = HM.empty
                ,   eu4extraScriptsCountryScope = HM.empty
                ,   eu4extraScriptsProvinceScope = HM.empty
                ,   eu4extraScriptsModifier = HM.empty
                }))
                (EU4S $ EU4State {
                    eu4currentFile = Nothing
                ,   eu4currentIndent = Nothing
                ,   eu4scopeStack = []
                ,   eu4IsInEffect = False
                }))
    type Scope EU4 = EU4Scope
    scope s = local $ \(EU4S st) -> EU4S $
        st { eu4scopeStack = s : eu4scopeStack st }
    getCurrentScope = asks $ listToMaybe . eu4scopeStack . eu4s
    getPrevScope = asks $ safeIndex 1 . eu4scopeStack . eu4s
    getPrevScopeCustom i = asks $ safeIndex i . eu4scopeStack . eu4s
    getRootScope = asks $ safeLast . eu4scopeStack . eu4s
    getScopeStack = asks $ eu4scopeStack . eu4s
    getIsInEffect = asks $ eu4IsInEffect . eu4s
    setIsInEffect b = local $ \(EU4S st) -> EU4S $ st { eu4IsInEffect = b }

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
    getGenericScriptsForEventTriggers = do
        EU4D ed <- get
        return (eu4genericScriptsForEventTriggers ed)
    getGeoData = do
        EU4D ed <- get
        return (eu4geoData ed)
    getProvinceTriggeredModifierScripts = do
        EU4D ed <- get
        return (eu4provtrigmodifierScripts ed)
    getProvinceTriggeredModifiers = do
        EU4D ed <- get
        return (eu4provtrigmodifiers ed)
    getTradeNodes = do
        EU4D ed <- get
        return (eu4tradeNodes ed)
    getEstateActions = do
        EU4D ed <- get
        return (eu4estateActions ed)
    getScriptedEffectsForEstates = do
        EU4D ed <- get
        return (eu4scriptedEffectsForEstates ed)
    getExtraScripts = do
        EU4D ed <- get
        return (eu4extraScripts ed)
    getExtraScriptsCountryScope = do
        EU4D ed <- get
        return (eu4extraScriptsCountryScope ed)
    getExtraScriptsProvinceScope = do
        EU4D ed <- get
        return (eu4extraScriptsProvinceScope ed)
    getExtraScriptsModifier = do
        EU4D ed <- get
        return (eu4extraScriptsModifier ed)

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
    settings <- gets getSettings
    let readOneScript :: String -> String -> PPT EU4 m (String, GenericScript)
        readOneScript category target = do
            content <- liftIO $ readScript settings target
            when (null content) $
                liftIO $ hPutStrLn stderr $
                    "Warning: " ++ target
                        ++ " contains no scripts - failed parse? Expected feature type "
                        ++ category
            return (target, content)

        readEU4Script :: String -> PPT EU4 m (HashMap String GenericScript)
        readEU4Script category = do
            let sourceSubdir = case category of
                    "colonial_regions" -> "common" </> "colonial_regions"
                    "disasters" -> "common" </> "disasters"
                    "ideagroups" -> "common" </> "ideas"
                    "modifiers" -> "common" </> "event_modifiers"
                    "on_actions" -> "common" </> "on_actions"
                    "opinion_modifiers" -> "common" </> "opinion_modifiers"
                    "policies" -> "common" </> "policies"
                    "province_triggered_modifiers" -> "common" </> "province_triggered_modifiers"
                    "trade_companies" -> "common" </> "trade_companies"
                    "tradenodes" -> "common" </> "tradenodes"
                    _          -> category
                sourceDir = buildPath settings sourceSubdir
            sourceDirExists <- liftIO $ doesDirectoryExist sourceDir
            if sourceDirExists then
                readEU4Script' category sourceDir sourceSubdir
            else
                trace ("Warning: Folder " ++ sourceDir ++ " does not exist")
                return HM.empty
            where
                readEU4Script' :: String -> String -> String -> PPT EU4 m (HashMap String GenericScript)
                readEU4Script' category sourceDir sourceSubdir = do
                    files <- liftIO (filterM (doesFileExist . buildPath settings . (sourceSubdir </>))
                                            =<< getDirectoryContents sourceDir)
                    results <- forM files $ \filename -> readOneScript category (sourceSubdir </> filename)
                    return $ foldl (flip (uncurry HM.insert)) HM.empty results

        getOnlyLhs :: GenericStatement -> Maybe Text
        getOnlyLhs (Statement (GenericLhs lhs _) _ _) = Just (toLower lhs)
        getOnlyLhs stmt = (trace $ "Unsupported statement: " ++ (show stmt)) $ Nothing

        toHashMap :: EU4GeoType -> [Text] -> HashMap Text EU4GeoType
        toHashMap gt l = foldr (\t -> HM.insert t gt) HM.empty l

        geoDirs = [ (EU4GeoTradeCompany, "trade_companies")
                  , (EU4GeoColonialRegion, "colonial_regions")
                  -- Tradenodes handled below
                  ]

        mapGeoFiles = [ (EU4GeoArea, "area.txt")
                      , (EU4GeoContinent, "continent.txt")
                      , (EU4GeoRegion, "region.txt")
                      , (EU4GeoSuperRegion, "superregion.txt")]

        readGeoData :: (EU4GeoType, String) -> PPT EU4 m (HashMap Text EU4GeoType)
        readGeoData (gt, dir) = do
            hm <- readEU4Script dir
            return $ toHashMap gt (catMaybes $ map getOnlyLhs (concat (HM.elems hm)))


        processTradeNode [pdx| $name = @scr |] = case findPrimary scr of
            Just id -> Just (id, name)
            _ -> (trace $ "Warning: Could not determine main province id for " ++ show name) $ Nothing
            where
                findPrimary :: GenericScript -> Maybe Int
                findPrimary ([pdx| location = !id |]:_) = Just id
                findPrimary (s:ss) = findPrimary ss
                findPrimary _ = Nothing
        processTradeNode stmt = (trace $ "Not handled in processTradeNode: " ++ show stmt) $ Nothing

        readGenericScriptsForEventTriggers :: PPT EU4 m (HashMap String GenericScript)
        readGenericScriptsForEventTriggers = do
            scripts <- mapM readScriptFromFolder (HM.keys locationsForEventTriggers ++ HM.keys locationsForEventTriggersWithExtraHandling)
            return $ HM.fromList scripts
            where
                readScriptFromFolder :: String -> PPT EU4 m (String, GenericScript)
                readScriptFromFolder folder = do
                    scriptsWithFilenames <- readEU4Script ("common" </> folder)
                    return (folder, concat (HM.elems scriptsWithFilenames))

        getFileFromOpts (ProcessFile f) = [f]
        getFileFromOpts _ = []

        getCountryScopeFileFromOpts (ProcessCountryScopeFile c) = [c]
        getCountryScopeFileFromOpts _ = []
        getProvinceScopeFileFromOpts (ProcessProvinceScopeFile s) = [s]
        getProvinceScopeFileFromOpts _ = []
        getModifierFileFromOpts (ProcessModifierFile m) = [m]
        getModifierFileFromOpts _ = []

    ideaGroups <- readEU4Script "ideagroups"
    decisions <- readEU4Script "decisions"
    events <- readEU4Script "events"
    modifiers <- readEU4Script "modifiers"
    opinion_modifiers <- readEU4Script "opinion_modifiers"
    missions <- readEU4Script "missions"
    provTrigModifiers <- readEU4Script "province_triggered_modifiers"
    genericScriptsForEventTriggers <- readGenericScriptsForEventTriggers
    scriptedEffectsForEstates <- liftIO (readFileRetry (buildPath settings "common/scripted_effects/01_scripted_effects_for_estates.txt"))

    extra <- mapM (readOneScript "extra") (concatMap getFileFromOpts (clargs settings))
    extraCountryScope <- mapM (readOneScript "extraCountryScope") (concatMap getCountryScopeFileFromOpts (clargs settings))
    extraProvinceScope <- mapM (readOneScript "extraProvinceScope") (concatMap getProvinceScopeFileFromOpts (clargs settings))
    extraModifier <- mapM (readOneScript "extraModifier") (concatMap getModifierFileFromOpts (clargs settings))
    ---------------------
    -- Geographic data --
    ---------------------
    --
    -- Arguably this shouldn't be parsed here, but we don't care
    -- about the actual script data.
    --
    geoData <- forM geoDirs readGeoData
    geoMapData <- forM mapGeoFiles  $ \(geoType, filename) -> do
        (_, d) <- readOneScript "map" (buildPath settings "map" </> filename)
        return $ toHashMap geoType (catMaybes $ map getOnlyLhs d)

    tradeNodeScripts <- readEU4Script "tradenodes"

    modify $ \(EU4D s) -> EU4D $ s {
            eu4ideaGroupScripts = ideaGroups
        ,   eu4decisionScripts = decisions
        ,   eu4eventScripts = events
        ,   eu4modifierScripts = modifiers
        ,   eu4opmodScripts = opinion_modifiers
        ,   eu4missionScripts = missions
        ,   eu4genericScriptsForEventTriggers = genericScriptsForEventTriggers
        ,   eu4geoData = HM.union (foldl HM.union HM.empty geoData) (foldl HM.union HM.empty geoMapData)
        ,   eu4provtrigmodifierScripts = provTrigModifiers
        ,   eu4tradeNodes = HM.fromList (catMaybes (map processTradeNode (concatMap snd (HM.toList tradeNodeScripts))))
        ,   eu4scriptedEffectsForEstates = scriptedEffectsForEstates
        ,   eu4extraScripts = foldl (flip (uncurry HM.insert)) HM.empty extra
        ,   eu4extraScriptsCountryScope = foldl (flip (uncurry HM.insert)) HM.empty extraCountryScope
        ,   eu4extraScriptsProvinceScope = foldl (flip (uncurry HM.insert)) HM.empty extraProvinceScope
        ,   eu4extraScriptsModifier = foldl (flip (uncurry HM.insert)) HM.empty extraModifier
        }

locationsForEventTriggers :: HashMap String [(Text, Text)]
locationsForEventTriggers =  HM.fromList [
                ("diplomatic_actions",
                    [("effect", "The diplomatic action")
                    ,("pre_effect", "The diplomatic action")])
                ,("estate_agendas",
                    [("pre_effect", "pre_effect of the agenda")
                    ,("immediate_effect", "Selecting the estate agenda")
                    ,("on_invalid", "Invalidation of the estate agenda")
                    ,("failing_effect", "Failing the estate agenda")
                    ,("task_completed_effect", "Completing the estate agenda")])
                ,("estate_crown_land", [("effect", "An estate interaction")])
                ,("estate_privileges",
                    [("on_cooldown_expires", "When the following estate privilege can be revoked:")
                    ,("on_granted", "Granting the estate privilege")
                    ,("on_granted_province", "Granting the estate privilege (for each province)")
                    ,("on_invalid", "When the following estate privilege becomes invalid:")
                    ,("on_invalid_province", "When the following estate privilege becomes invalid (for each province):")
                    ,("on_revoked", "Revoking the estate privilege")
                    ,("on_revoked_province", "Revoking the estate privilege (for each province)")
                    ])
                ,("government_reforms",
                    [("effect", "Enacting the government reform")
                    ,("removed_effect", "Revoking the government reform")
                    ,("post_removed_effect", "After revoking the government reform")
                    ])
                ,("imperial_reforms",
                    [("on_effect", "Enacting the imperial reform")
                    ,("off_effect", "Revoking the imperial reform")])
                ,("incidents", [("immediate_effect", "Start of the Shinto incident")])
                ,("new_diplomatic_actions",
                    [("on_accept", "Accepting the diplomatic action")
                    ,("on_decline", "Declining the diplomatic action")])
                ,("parliament_issues", [("effect", "Enacting the parliament issue")])
                ,("peace_treaties", [("effect", "When a peace treaty with the folloing term gets signed:")])
                ]
locationsForEventTriggersWithExtraHandling :: HashMap String (EU4EventTriggers -> [GenericStatement] -> EU4EventTriggers)
locationsForEventTriggersWithExtraHandling = HM.fromList
    [("disasters", findTriggeredEventsInDisasters)
    ,("government_mechanics", findTriggeredEventsInGovernmentMechanics)
    ,("imperial_incidents", findTriggeredEventsInImperialIncidents)
    ,("on_actions", findTriggeredEventsInOnActions)
    ]

findTriggeredEventsInUnhandledFiles :: EU4EventTriggers -> HashMap String GenericScript -> EU4EventTriggers
findTriggeredEventsInUnhandledFiles hm foldersMap = HM.foldlWithKey' findTriggeredEventsInUnhandledFolder hm foldersMap
    where
        findTriggeredEventsInUnhandledFolder :: EU4EventTriggers -> String -> GenericScript -> EU4EventTriggers
        findTriggeredEventsInUnhandledFolder hm folder script = case HM.lookup folder locationsForEventTriggers of
            (Just sectionMap) -> findTriggeredEventsInGenericScript hm (HM.fromList sectionMap) script
            Nothing -> case HM.lookup folder locationsForEventTriggersWithExtraHandling of
              Just handler -> handler hm script
              Nothing -> hm -- it should not get here as long as all the code uses the folders from locationsForEventTriggers

-- | Interpret the script ASTs as usable data.
parseEU4Scripts :: Monad m => PPT EU4 m ()
parseEU4Scripts = do
    -- Need idea groups and modifiers before everything else
    ideaGroups <- parseEU4IdeaGroups =<< getIdeaGroupScripts
    modifiers <- parseEU4Modifiers =<< getModifierScripts
    opinionModifiers <- parseEU4OpinionModifiers =<< getOpinionModifierScripts
    provTrigModifiers <- parseEU4ProvTrigModifiers =<< getProvinceTriggeredModifierScripts
    decisions <- parseEU4Decisions =<< getDecisionScripts
    events <- parseEU4Events =<< getEventScripts
    missions <- parseEU4Missions =<< getMissionScripts
    genericScriptsForEventTriggers <- getGenericScriptsForEventTriggers
    scriptedEffectsForEstates <- getScriptedEffectsForEstates
    let te1 = findTriggeredEventsInEvents HM.empty (HM.elems events)
        te2 = findTriggeredEventsInDecisions te1 (HM.elems decisions)
        te3 = findTriggeredEventsInMissions te2 (HM.elems missions)
        te4 = findTriggeredEventsInProvinceTriggeredModifiers te3 (HM.elems provTrigModifiers)
        te5 = findTriggeredEventsInUnhandledFiles te4 genericScriptsForEventTriggers
        estateActions = findEstateActions (HM.elems decisions) (HM.findWithDefault [] "estate_privileges" genericScriptsForEventTriggers) scriptedEffectsForEstates
    --traceM $ concat (map (\(k,v) -> (show k) ++ " -> " ++ show v ++ "\n") (HM.toList $ te5))
    modify $ \(EU4D s) -> EU4D $
            s { eu4events = events
            ,   eu4decisions = decisions
            ,   eu4ideaGroups = ideaGroups
            ,   eu4modifiers = modifiers
            ,   eu4opmods = opinionModifiers
            ,   eu4missions = missions
            ,   eu4eventTriggers = te5
            ,   eu4provtrigmodifiers = provTrigModifiers
            ,   eu4estateActions = estateActions
            }

-- | Output the game data as wiki text.
writeEU4Scripts :: (EU4Info g, MonadIO m) => PPT g m ()
writeEU4Scripts = do
    settings <- gets getSettings
    unless (Onlyextra `elem` (clargs settings)) $ do
        writeEU4IdeaGroups
        writeEU4Events
        writeEU4Decisions
        writeEU4Missions
        writeEU4OpinionModifiers
        writeEU4ProvTrigModifiers
    writeEU4Extra
    writeEU4ExtraCountryScope
    writeEU4ExtraProvinceScope
    writeEU4ExtraModifier
