{-|
Module      : Localization
Description : Load localization files
-}
module Localization (
        readL10n -- :: Settings -> IO L10n
    ,   L10n -- re-exported from Yaml
    ) where

import Control.Monad (liftM, filterM, forM)

import Data.List (isInfixOf, foldl')
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as B8

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import qualified Data.Yaml as Y
import Data.Attoparsec.Text (Parser)
import qualified Data.Attoparsec.Text as Ap

import System.Directory (doesFileExist, getDirectoryContents)
import System.FilePath ((</>))
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import SettingsTypes (Settings (..), L10nScheme (..))
import Yaml (L10n, LocEntry (..), parseLocFile, mergeLangs, mergeLangList)

-- | Read and parse localization files for the current game.
--
-- This function is capable of dealing with both the old CSV-style localisation
-- and the newer quasi-YAML localization. It does not understand the old EU4
-- true YAML localisation, which, as far as I know, no PDS game uses any more.
readL10n :: Settings -> IO L10n
readL10n settings = do
    let dir = steamDir settings
              </> steamApps settings
              </> gameFolder settings
              </> "localisation"
              </> T.unpack (languageFolder settings)
    files <- filterM doesFileExist
                . map (dir </>)
                . (case l10nScheme settings of
                    -- CK2 and earlier use semicolon-delimited CSV.
                    --  KEY;English;French;German;;Spanish;;;;;;;;;x
                    L10nCSV -> id
                    -- EU4 and later use a quasi-YAML format, one file per language.
                    --  l_language: (e.g. l_english)
                    --   KEY:0 "Content with "unescaped" quotation marks"
                    -- where the 0 is a version number. We discard languages we
                    -- don't care about.
                    L10nQYAML -> filter (T.unpack (language settings) `isInfixOf`))
                    =<< getDirectoryContents dir
    case l10nScheme settings of
        L10nCSV ->
            let csvField :: Parser Text
                csvField = Ap.takeWhile (/=';')
                langs = [(0, "l_english")
                        ,(1, "l_french")
                        ,(2, "l_german")
                        ,(4, "l_spanish")]
                -- Key and value in the chosen language
                parseLine :: Parser L10n
                parseLine = do
                    tag:fields <- csvField `Ap.sepBy` (Ap.string ";")
                    -- fields :: [Text]
                    let addField (fieldnum, lang)
                            = HM.singleton
                                lang
                                (HM.singleton tag (LocEntry 0 (fields!!fieldnum)))
                    return $ mergeLangList (map addField langs)
            in liftM mconcat . forM files $ \file -> do
                fileContents <- T.lines <$> TIO.readFile file
                let parsedLines = mapM (Ap.parseOnly parseLine) fileContents
                case parsedLines of
                    Left err -> do
                        hPutStrLn stderr ("Error reading localization file "
                            ++ file
                            ++ ": " ++ err)
                        exitFailure
                    Right lines -> return (mconcat lines)
        L10nQYAML -> liftM (foldl' mergeLangs HM.empty) . forM files $ \file -> do
            parseResult <- parseLocFile <$> TIO.readFile file
            case parseResult of
                Left exc -> do
                    hPutStrLn stderr $ "Parsing localisation file " ++ file ++ " failed: " ++ show exc
                    return HM.empty
                Right contents -> return contents
