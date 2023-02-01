{-|
Module      : Interface
Description : Load interface files
-}
module Interface (
        readInterface -- :: Settings -> IO L10n
    ) where


import Control.Monad (filterM, forM)
import Control.Monad.Trans (MonadIO (..), liftIO)

import Data.HashMap.Strict.InsOrd(InsOrdHashMap)
import qualified Data.HashMap.Strict.InsOrd as HMO

import Data.Text (Text)
import qualified Data.Text as T

import Data.Maybe (catMaybes)
import Data.HashMap.Strict (HashMap)

import System.Directory (doesFileExist, getDirectoryContents, doesDirectoryExist)
import System.Directory.Recursive (getSubdirsRecursive)
import System.FilePath ((</>),takeBaseName, isExtensionOf)

import Abstract -- everything
import SettingsTypes ( Settings (..)


                     , concatMapM)
import QQ (pdx)
import FileIO (readPathScript)

-- | Read and parse localization files for the current game.
--
-- This function is capable of dealing with both the old CSV-style localisation
-- and the newer quasi-YAML localization. It does not understand the old EU4
-- true YAML localisation, which, as far as I know, no PDS game uses any more.
readInterface :: Settings -> IO (HashMap Text Text)
readInterface settings = do
    let dir           = gamePath settings
                        </> "interface"
        dirmod        = gameModPath settings
                        </> "interface"
    modexist <- doesDirectoryExist dirmod
    dirmod' <- if modexist then do
        dirmodsub <- getSubdirsRecursive dirmod
        return $ dirmod : dirmodsub else return []
    let dirs = dirmod'++ [dir]
    files <- concatMapM readInterfaceDirs dirs
    scripts <- forM files $ \filename -> liftIO $ readPathScript filename
    let tryParse = map (map processInterface . concatMap (\case
                    [pdx| $spriteTypes = @spr |] | T.toLower spriteTypes == "spritetypes" -> spr
                    _ -> []))
                scripts
        interfacemap = map (mkInterMap . catMaybes) tryParse
    return $ HMO.toHashMap $ HMO.unions interfacemap
    where
        mkInterMap :: [(Text,Text)] -> InsOrdHashMap Text Text
        mkInterMap interfacelist = HMO.fromList interfacelist

processInterface :: GenericStatement -> Maybe (Text, Text)
processInterface stmt@[pdx| $spriteType = @spr |] | T.toLower spriteType == "spritetype"
    =  case (getId spr, getPic spr) of
        (Just id, Just pic) -> Just (id, pic)
        (Nothing, Just pic) -> Nothing
        (Just id, Nothing) -> Nothing
        _ -> Nothing
    where
        getId :: [GenericStatement] -> Maybe Text
        getId [] = Nothing
        getId (stmt@[pdx| $name = $id |] : _)
            | T.toLower name == "name" = Just id
        getId (stmt@[pdx| $name = ?id |] : _)
            | T.toLower name == "name" = Just id
        getId (_ : ss) = getId ss
        getPic :: [GenericStatement] -> Maybe Text
        getPic [] = Nothing
        getPic (stmt@[pdx| $texturefile = $id |] : _)
            | T.toLower texturefile == "texturefile" = Just $ T.pack $ takeBaseName $ T.unpack id
        getPic (stmt@[pdx| $texturefile = ?id |] : _)
            | T.toLower texturefile == "texturefile" = Just $ T.pack $ takeBaseName $ T.unpack id
        getPic (_ : ss) = getPic ss
processInterface stmt = Nothing

readInterfaceDirs :: FilePath -> IO [FilePath]
readInterfaceDirs dirs = filterM doesFileExist
                . map (dirs </>)
                . filter (".gfx" `isExtensionOf`)
                    =<< getDirectoryContents dirs
