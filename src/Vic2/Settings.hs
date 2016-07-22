{-# LANGUAGE OverloadedStrings #-}
module Vic2.Settings (
        fillSettings
    ,   writeVic2Scripts
    ,   module Vic2.Types
    ) where

import Control.Monad.State

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import System.Directory
import System.FilePath

import Abstract
import FileIO
import SettingsTypes
import Vic2.Types

-- Handlers
--import Vic2.Decisions (parseVic2Decisions, writeVic2Decisions)
--import Vic2.Missions (parseVic2Missions, writeVic2Missions)
--import Vic2.Events (parseVic2Events, writeVic2Events)
--import Vic2.Policies (parseVic2Policies, writeVic2Policies)

fillSettings :: Settings -> IO (Settings, GameState)
fillSettings settings = return $
    (settings {
        game = GameVic2 {
            readScripts = ScriptReader readVic2Scripts
        ,   parseScripts = ScriptParser parseVic2Scripts
        ,   writeScripts = ScriptWriter writeVic2Scripts
        ,   vic2data = Vic2Data HM.empty HM.empty
        }
    }, Vic2State (Vic2 {
        scopeStack = []
       }) Nothing Nothing)

-- Read all scripts in a directory.
-- Return: for each file, its path relative to the game root and the parsed
--         script.
readVic2Scripts :: PPT IO GameScripts
readVic2Scripts = GameScriptsVic2 <$> do
    let readVic2Script :: String -> PPT IO (HashMap String GenericScript)
        readVic2Script category = do
            settings <- get
            let sourceSubdir = case category of
                    "policies" -> "common" </> "policies"
                    "ideagroups" -> "common" </> "ideas"
                    _          -> category
                sourceDir = buildPath settings sourceSubdir
            files <- liftIO (filterM (doesFileExist . buildPath settings . (sourceSubdir </>))
                                     =<< getDirectoryContents sourceDir)
            results <- forM files $ \filename -> do
                let target = sourceSubdir </> filename
                content <- join (liftIO . flip readScript target <$> get)
                when (null content) $
                    liftIO $ hPutStrLn stderr $
                        "Warning: " ++ target
                            ++ " contains no scripts - failed parse? Expected feature type "
                            ++ category
                return (target, content)
            return $ foldl (flip (uncurry HM.insert)) HM.empty results

    ideaGroups <- readVic2Script "ideagroups"
    decisions <- readVic2Script "decisions"
    events <- readVic2Script "events"
    return $ Vic2Scripts {
            vic2decisionScripts = decisions
        ,   vic2eventScripts = events
        }

parseVic2Scripts :: Monad m => GameScripts -> PPT m ()
parseVic2Scripts (GameScriptsVic2 (Vic2Scripts {
                    vic2decisionScripts = decisionScripts
                ,   vic2eventScripts = eventScripts
                })) = do
    decisions <- parseVic2Decisions decisionScripts
    events <- parseVic2Events eventScripts

    modify $ \s -> case game s of
        GameVic2 { vic2data = gdata }
            -> s {
                game = (game s) {
                    vic2data = gdata {
                        vic2events = events
                    ,   vic2decisions = decisions
                    ,   vic2ideagroups = ideaGroups
                    }
                }
            }
        _ -> error "parseVic2Scripts passed wrong kind of scripts!"

writeVic2Scripts :: PPT IO ()
writeVic2Scripts = do
    writeVic2IdeaGroups
    writeVic2Events
    writeVic2Decisions