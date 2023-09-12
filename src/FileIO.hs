{-|
Module      : FileIO
Description : High level I/O for Clausewitz scripts
-}
module FileIO (
        readFileRetry
    ,   buildPath
    ,   readScript
    ,   readPathScript
    ,   readScriptFromText
    ,   Feature (..)
    ,   writeFeatures
    ) where

import Debug.Trace (trace)

import Control.Monad (forM, forM_)
import Control.Monad.Except (ExceptT)
import Control.Monad.Trans (MonadIO (..))
import Control.Monad.State (gets)
import Control.Exception (try)

import qualified Data.ByteString as B

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Text.Encoding.Error (UnicodeException)
import qualified Data.Text.Encoding as TE

import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>), takeDirectory, dropDrive)
import System.IO (withFile, IOMode (..), hPutStrLn, stderr)

import qualified Data.Attoparsec.Text as Ap
import Text.PrettyPrint.Leijen.Text (Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP

import Abstract -- everything
import SettingsTypes (Settings (..), IsGameData (..), GameData (..), PPT, hoistExceptions)
import Data.List (intercalate)

-- | Read a file as Text. Unfortunately EU4 script files use several incompatible
-- encodings. Try the following encodings in order:
--
-- 1. UTF-8
-- 2. ISO 8859-1
--
-- (Decoding as 8859-1 can't fail, but I don't know if it will always be correct.)
readFileRetry :: FilePath -> IO Text
readFileRetry path = do
    raw <- B.readFile path
    -- Catching exceptions in pure code is a rather convoluted process...
    e <- try (let e = TE.decodeUtf8 raw in e `seq` return e)
    case (e::Either UnicodeException Text) of
        Right result -> return result
        Left _ -> return $ TE.decodeLatin1 raw

-- | Given a path under the game's root directory, build a fully qualified path
-- referring to that file.
--
-- For example, if we're parsing EU4 on Windows with the usual install
-- location:
--
-- @
--  buildPath settings "events/FlavorENG.txt" = "C:\Program Files (x86)\Steam\steamapps\common\Europa Universalis IV\events\FlavorENG.txt"
-- @
buildPath :: Settings -> FilePath -> FilePath
buildPath settings path =
    if gameOrModFolder settings == gameFolder settings then
        gamePath settings </> path
    else
        gameModPath settings </> path

-------------------------------
-- Reading scripts from file --
-------------------------------

-- | Read and parse a script file. On error, report to standard error and
-- return an empty script.
readScript :: Settings -> FilePath -> IO GenericScript
readScript settings file = do
    let filepath = buildPath settings file
    readPathScript filepath
readPathScript :: FilePath -> IO GenericScript
readPathScript filepath = do
    contents <- readFileRetry filepath
    case runparserAndAddClosingCurlyBrackets filepath contents of
        -- this case probably can't happen with our parser
        Ap.Fail _ context err -> do
            hPutStrLn stderr $ "Couldn't parse " ++ filepath ++ ": " ++ err
            hPutStrLn stderr $ "Context: " ++ intercalate ", " context
            return []
        Ap.Partial _ -> do
            hPutStrLn stderr $ "Got partial from file: " ++ filepath ++ " This should not happen"
            return []
        -- no result, but also not leftovers
        Ap.Done "" [] -> do
            hPutStrLn stderr $ "The file " ++ filepath ++ " seems to only contain whitespace and comments"
            return []
        Ap.Done "" result -> return result
        Ap.Done leftover result -> do
            hPutStrLn stderr $ "Warning: The file \"" ++ filepath ++ "\" was not fully parsed. The following lines were discarded:"
            hPutStrLn stderr $ T.unpack leftover
            return result
    where
        runparser contents = case Ap.parse
                (Ap.option undefined (Ap.char '\xFEFF') *> skipSpace
                   *> genericScript
                   -- discard extra whitespace and comments at the end of the file. This is needed so that
                   -- a successful parse has no leftovers
                   <* skipSpace
                   ) contents of
            -- pass an empty string to the partial to tell it that there is no more input
            Ap.Partial f -> f ""
            -- just pass on all other cases
            x -> x

        runparserAndAddClosingCurlyBrackets filepath contents = case runparser contents of
            -- no leftovers means that the parsing was successful (result could be empty in case of a file which just has whitespace and comments)
            Ap.Done "" result -> Ap.Done "" result
            -- we have some leftover, so the file was either not parsed at all or just partially parsed
            -- so we try again with an extra closing }
            Ap.Done originalLeftover originalResult -> case runparser (contents<>"}") of
                -- good, it worked now and we can return the new result
                Ap.Done "" newResult -> do
                    trace ( "File " ++ filepath ++ ": Missing closing curly bracket, applied fix" )
                        Ap.Done "" newResult
                -- still didn't work, so we try with two }
                Ap.Done _newLeftover _newResult -> case runparser (contents<>"}}") of
                    -- good, it worked now and we can return the new result
                    Ap.Done "" newResult -> do
                        trace ("File " ++ filepath ++ ": Missing 2 closing curly brackets, applied fix")
                            Ap.Done "" newResult
                    -- to not make matters worse, we return the original results if adding } didn't result in a successful parse
                    _ -> Ap.Done originalLeftover originalResult
                _ -> Ap.Done originalLeftover originalResult
            -- just pass on all other cases
            x -> x

readScriptFromText :: Text -> GenericScript
readScriptFromText contents = case Ap.parseOnly
    ( skipSpace
        *> genericScript
    ) contents of
    Right result -> result
    Left err -> trace ("Error \"" ++ err ++ "\" in readScriptFromText with the text:" ++ show contents) []

------------------------------
-- Writing features to file --
------------------------------

-- | An individual game feature. For example, a value for this exists for each
-- EU4 event, one for each idea group, one for each decision, etc.
--
-- The parameter is a type containing data relevant to that feature, or an
-- error message from processing.
data Feature a = Feature {
        featureId :: Maybe Text
    ,   featurePath :: Maybe FilePath
    ,   theFeature :: Either Text a
    } deriving (Show)

-- TODO: allow writing to a different output directory
-- | Write a parsed and presented feature to the given file under the directory
-- @./output@. If the filename includes directories, create them first.
writeFeature :: FilePath -> String -> Doc -> IO ()
writeFeature path gamefold output = do
    let destinationGame = "output" </> gamefold
        destinationFile = destinationGame </> dropDrive path
        destinationDir  = takeDirectory destinationFile
    createDirectoryIfMissing True (takeDirectory destinationGame)
    createDirectoryIfMissing True destinationDir
    withFile destinationFile WriteMode $ \h -> do
        result <- try $
            PP.displayIO h (PP.renderPretty 0.9 80 output)
        case result of
            Right () -> return ()
            Left err -> hPutStrLn stderr $
                "Error writing " ++ show (err::IOError)

-- | Given a list of features, present them and output to the appropriate files
-- under the directory @./output@.
writeFeatures :: (IsGameData (GameData g), MonadIO m) =>
    Text -- ^ Name of feature (e.g. "idea groups")
        -> [Feature a]
        -> (a -> PPT g (ExceptT Text m) Doc) -- ^ Rendering function
        -- PPT g (ExceptT Text IO) = StateT Settings (ReaderT GameState (ExceptT Text IO))
        -> PPT g m ()
writeFeatures featureName features pprint = do
    gamefoldr <- gets (gameOrModFolder . getSettings)
    efeatures_pathed_pp'd <- forM features $ \feature ->
        case theFeature feature of
            Left err ->
                -- Error was passed to us - report it
                return (feature {
                        theFeature = Left $ "Error while parsing" <> featureName <> ":" <> err
                    })
            Right thing -> case (featurePath feature, featureId feature) of
                (Just _, Just _) -> do
                    doc <- hoistExceptions (pprint thing)
                    return (feature { theFeature = Right doc })
                (Nothing, Nothing) -> return (feature {
                        theFeature = Left $ "Error while writing " <> featureName
                                        <> ": missing path and id"
                    })
                (Nothing, Just oid) -> return (feature {
                        theFeature = Left $ "Error while writing " <> featureName
                                        <> " " <> oid <> ": missing path"
                    })
                (Just path, Nothing) -> return (feature {
                        theFeature = Left $ "Error while writing " <> featureName
                                        <> " " <> T.pack path <> ": missing id"
                    })
    liftIO $ forM_ efeatures_pathed_pp'd $ \feature -> case theFeature feature of
        Right (Right output) -> case (featurePath feature, featureId feature) of
            (Just sourcePath, Just feature_id) ->
                writeFeature (sourcePath </> T.unpack feature_id) gamefoldr output
            (Just sourcePath, Nothing) -> liftIO . TIO.putStrLn $
                "Error while writing " <> featureName <> " in " <> T.pack sourcePath <> ": missing id"
            (Nothing, Just fid) -> liftIO . TIO.putStrLn $
                "Error while writing " <> featureName <> " " <> fid <> ": missing source path"
            (Nothing, Nothing) -> liftIO . TIO.putStrLn $
                "Error while writing " <> featureName <> ": missing source path and id"
        e -> TIO.putStrLn (eitherError e) where
            eitherError (Right (Right _)) = error "impossible: fall through in writeFeatures"
            eitherError (Right (Left err)) = err
            eitherError (Left err) = err
    -- TODO: within each input file, sort by id, then write to a
    -- consolidated file.
