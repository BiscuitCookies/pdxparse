{-|
Module      : Main
Description : Entry point for pdxparse executable
-}
module Main where

import Control.Monad (join, unless)
import Control.Monad.Reader (MonadReader (..), runReaderT)
import Control.Monad.State (MonadState (..), gets, evalStateT)
import Control.Monad.Trans (MonadIO (..))
import Control.Exception

import System.Directory (createDirectoryIfMissing)
import System.Exit
import System.IO

import Data.Text (Text, unpack)

import Platform (initPlatform)
import Settings (readSettings, readCommandLineOptions)
import SettingsTypes ( Settings (..), Game (..), IsGame (..)
                     , readScripts, parseScripts, writeScripts
                     , hoistExceptions, CLArgs (..))
import HOI4.Settings

-- | Entry point for the program.
main :: IO ()
main = withExitOnInput $ do
    -- Do platform-specific initialization
    initPlatform

    -- Read the settings file
    settings <- readSettings

    createDirectoryIfMissing False "output"

    -- StateT Settings (ReaderT GameState IO) ()
    case game settings of
        Game g -> runWithInitState g settings $ do
            -- 1) Read the game's scripts
            liftIO $ putStrLn "Reading scripts."
            errs <- hoistExceptions readScripts
            case errs of
                Right () -> return () -- carry on
                Left e -> liftIO $ do
                    hPutStrLn stderr $ "Failed reading scripts: " ++ unpack e
                    exitFailure

            -- 2) Parse the game's scripts (into state)
            liftIO $ putStrLn "Parsing scripts."
            parseScripts

            -- 3) Output the result of parsing and/or report errors
            writeScripts

withExitOnInput :: IO () -> IO ()
withExitOnInput theMain = do
  exitCode <- run `catch` onError
  exitOnInput exitCode
 where
  exitOnInput exitCode = do
    (opts, nonopts, errs) <- readCommandLineOptions
    unless (Nowait `elem` opts) $ do
      putStrLn "Press any key to exit."
      hSetBuffering stdin NoBuffering
      hSetEcho stdin False
      getChar
      exitWith exitCode

  run = do
    theMain
    pure ExitSuccess

  onError :: SomeException -> IO ExitCode
  onError e = case fromException e of
    Nothing -> do
      putStrLn $ "\nException: " ++ show e ++ "\n"
      pure (ExitFailure 1)
    Just (SomeAsyncException ae) -> throwIO ae