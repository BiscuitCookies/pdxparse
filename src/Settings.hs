{- |
Module      : Settings
Description : Load configuration files and localization
-}
module Settings (
        Settings (..)
    ,   readSettings
    ,   readCommandLineOptions
    ) where

import Data.Maybe (fromMaybe)

import Data.Char (toLower)
import Data.List (intercalate)
import qualified Data.HashMap.Strict as HM
import qualified Data.HashMap.Strict.InsOrd as HMO
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Version as V

import Data.Yaml (FromJSON (..), Value (..), decodeFileEither, (.:), (.:?))

import System.Console.GetOpt (OptDescr (..), ArgDescr (..), ArgOrder (..), getOpt, usageInfo)
import System.Directory (getHomeDirectory, doesFileExist)
import System.Environment (getArgs, getExecutablePath)
import System.Exit (exitFailure, exitSuccess)
import System.IO (hPutStrLn, stderr)
import qualified System.Info
import System.FilePath ((</>), replaceFileName)

import Control.Monad (when, forM_, unless)

import Localization (readL10n)
import Interface (readInterface)
import SettingsTypes ( CLArgs (..), Settings (..), Game (..), IsGame (..)
                     , setGameL10n)
import Paths_pdxparse (version, getDataFileName)
import EU4.Settings (EU4 (..))
import HOI4.Settings (HOI4 (..))
import Stellaris.Settings (Stellaris (..))
import Vic2.Settings (Vic2 (..))

-- | Intermediate structure. Maybe values don't need to be present in the
-- settings file.
data SettingsInput = SettingsInput {
        steamDriveI  :: Maybe String
    ,   steamDirI    :: Maybe FilePath
    ,   steamAppsI   :: Maybe FilePath
    ,   gameFolderI  :: String
    ,   languageI    :: Text
    ,   gameVersionI :: String
    ,   modNameI     :: Maybe String
    ,   modDirI      :: Maybe FilePath
    } deriving (Show)
-- Settings is defined in SettingsTypes

instance FromJSON SettingsInput where
    parseJSON (Object o) = do
        settingsIn <- o .: "settings"
        case settingsIn of
            Object o' -> SettingsInput
                            <$> fmap (fmap T.unpack) (o' .:? "steam_drive")
                            <*> fmap (fmap T.unpack) (o' .:? "steam_dir")
                            <*> fmap (fmap T.unpack) (o' .:? "steam_apps")
                            <*> fmap T.unpack (o' .: "game")
                            <*> (o' .: "language")
                            <*> fmap T.unpack (o' .: "version")
                            <*> fmap (fmap T.unpack) (o' .:? "mod_name")
                            <*> fmap (fmap T.unpack) (o' .:? "mod_path")
            _ -> fail "bad settings file"
    parseJSON _ = fail "bad settings file"

-- | Supported platforms. As far as I know, these are the only platforms that
-- Steam supports.
data Platform
    = Linux
    | MacOS
    | WindowsXP
    | Windows -- ^ 7 or later (and Vista?)
    | Unknown
    deriving (Eq, Show)
-- | Which platform this program was compiled on.
platform :: Platform
platform = case map toLower System.Info.os of
    "linux" -> Linux
    "darwin" -> MacOS
    "cygwin_nt-5.1"  -> WindowsXP
    "mingw32_nt-5.1" -> WindowsXP
    "mingw64_nt-5.1" -> Unknown -- Steam doesn't support 64 bit XP afaik
    osid -- Windows: running under either Cygwin or MinGW (more likely the latter).
        | take 6 osid == "cygwin"  -> Windows
        | take 5 osid == "mingw"   -> Windows
        | otherwise                -> Unknown
{-# INLINE platform #-}

-- | Supported command-line options.
--
-- [@-p@ or @--paths@] Show location of configuration files
-- [@-v@ or @--version@] Show version information
programOpts :: [OptDescr CLArgs]
programOpts =
    [ Option ['p'] ["paths"]         (NoArg Paths)   "show location of configuration files"
    , Option ['v'] ["version"]       (NoArg Version) "show version information"
    , Option ['h'] ["help"]          (NoArg Help) "show this message"
    , Option ['n'] ["nowait"]        (NoArg Nowait) "don't wait for the user to press a key before exiting"
    , Option ['w'] ["withlabels"]    (NoArg WithLabels)  "the top level of the extra files is considered a label which gets localized, but not processed further"
    , Option ['e'] ["onlyextra"]     (NoArg Onlyextra) "skip writing normal game files and only write the result of parsing the file, countryscope, provincescope and modifiers arguments"
    , Option ['f'] ["file"]          (ReqArg ProcessFile "FILE")  "also process FILE"
    , Option ['c'] ["countryscope"]  (ReqArg ProcessCountryScopeFile "FILE")  "also process FILE as containing code in the counrty scope"
    , Option ['s'] ["provincescope"] (ReqArg ProcessProvinceScopeFile "FILE")  "also process FILE as containing code in the province scope"
    , Option ['m'] ["modifiers"]     (ReqArg ProcessModifierFile "FILE")  "also process FILE as containing modifiers"
    ]

readCommandLineOptions :: IO ([CLArgs], [String], [String])
readCommandLineOptions = getOpt Permute programOpts <$> getArgs

-- | Process command-line arguments, then read the settings and localization
-- files. If we can't, abort.
readSettings :: IO Settings
readSettings = do
    (opts, nonopts, errs) <- readCommandLineOptions
    unless (null errs) $ do
        forM_ errs $ \err -> putStrLn err
        putStrLn $ usageInfo "pdxparse" programOpts
        exitFailure

    -- if there is a settings.yml in the same folder as the executable, we use it
    -- otherwise we use the one which cabal installed
    globalSettingsPath <- getDataFileName "settings.yml"
    exePath <- getExecutablePath
    let settingsPathInExePath = replaceFileName exePath "settings.yml"
    settingsExistsInExePath <- doesFileExist settingsPathInExePath

    let settingsFilePath = if settingsExistsInExePath then settingsPathInExePath else globalSettingsPath

    -- Check if info args were specified. If so, honour them, then exit.
    when (Paths `elem` opts || Version `elem` opts || Help `elem` opts) $ do
        when (Version `elem` opts) $
            let V.Version branch _ = version
            in putStrLn $ "pdxparse " ++ intercalate "." (map show branch)
        when (Paths `elem` opts) $
            putStrLn $ "Settings file is at " ++ settingsFilePath
        when (Help `elem` opts) $
            putStrLn $ usageInfo "pdxparse" programOpts
        exitSuccess

    result <- decodeFileEither settingsFilePath
    case result of
        Right settingsIn -> do
            steamDirCanonicalized <- case steamDirI settingsIn of
                Just path -> return path
                Nothing -> case platform of
                    Linux -> do
                        home <- getHomeDirectory
                        return $ home </> ".local/share"
                    MacOS -> do
                        home <- getHomeDirectory
                        return $ home </> "Library/Application Support"
                    -- TODO: allow user to specify drive only.
                    WindowsXP -> return $ fromMaybe "C" (steamDriveI settingsIn) ++ ":"
                                      </> fromMaybe "Program Files" (steamDirI settingsIn)
                    Windows -> return $ fromMaybe "C" (steamDriveI settingsIn) ++ ":"
                                      </> fromMaybe "Program Files (x86)" (steamDirI settingsIn)
                    Unknown -> fail $ "Unknown platform: " ++ System.Info.os
            let steamAppsCanonicalized = fromMaybe "Steam/steamapps/common" (steamAppsI settingsIn)
                lang = languageI settingsIn
                gamefolder = gameFolderI settingsIn
                modfolder = fromMaybe "" (modNameI settingsIn)
                modlocation = fromMaybe "C:/thisgoesnowhere" (modDirI settingsIn)

            (game, gameString) <- case gamefolder of
                "Europa Universalis IV" -> return (Game EU4, "EU4")
                "Hearts of Iron IV" -> return (Game HOI4, "HOI4")
                "Stellaris" -> return (Game Stellaris, "Stellaris")
                "Victoria 2" -> return (Game Vic2, "Vic2")
                other -> do
                    putStrLn $ "I don't know how to handle " ++ other ++ "!"
                    exitFailure

            langFolder <- case gamefolder of
                "Hearts of Iron IV" -> return $ "localisation" </> T.unpack lang
                _other -> return "localisation"

            gameormodfolder <- case modNameI settingsIn of
                Just _mname -> return modfolder
                _ -> return gamefolder

            let provisionalSettings = Settings
                            { steamDir = steamDirCanonicalized
                            , steamApps = steamAppsCanonicalized
                            , l10nScheme = case game of Game g -> locScheme g
                            , game = game
                            , gameString = gameString
                            , gameFolder = gamefolder
                            , gameOrModFolder = gameormodfolder
                            , gameModPath = modlocation
                            , gamePath = steamDirCanonicalized </> steamAppsCanonicalized </> gamefolder
                            , justLanguage = T.unpack lang
                            , language = "l_" <> lang
                            , languageFolder = langFolder
                            , languageS = "l_" <> T.unpack lang
                            , gameVersion = T.pack (gameVersionI settingsIn)
                            , gameInterface = HM.empty -- filled in later
                            , gameL10n = HM.empty -- filled in later
                            , gameL10nKeys = [] -- filled in later
                            , langs = ["en"]
                            , settingsFile = settingsFilePath
                            , clargs = opts
                            , filesToProcess = nonopts }

            (game_l10n, ordered) <- readL10n provisionalSettings
            interface <- readInterface provisionalSettings
            let l10nkeys = HMO.keys $ HMO.unions (HMO.elems ordered)
            return $ setGameL10n provisionalSettings game_l10n l10nkeys interface

        Left exc -> do
            hPutStrLn stderr $ "Couldn't parse settings: " ++ show exc
            exitFailure
