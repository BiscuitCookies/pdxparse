{-
Module      : HOI4.Misc
Description : Feature handler for miscellaneous features in Hearts of Iron IV
-}
{-# LANGUAGE LambdaCase #-}
module HOI4.Misc (
         parseHOI4CountryHistory
        ,parseHOI4Terrain
        ,parseHOI4Ideology
        ,parseHOI4Effects
        ,parseHOI4Triggers
        ,parseHOI4BopRanges
        ,parseHOI4ModifierDefinitions
        ,parseHOI4LocKeys
    ) where

import Debug.Trace (trace, traceM)

import Control.Arrow ((&&&))
import Control.Monad (foldM, forM)
import Control.Monad.Except (MonadError (..))

import Data.Char (isUpper, isAlphaNum)
import Data.List ( sortOn, foldl', elemIndex )
import Data.Maybe (catMaybes, mapMaybe)

import System.FilePath (takeFileName)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import qualified Data.HashMap.Strict.InsOrd as HMO
import Data.Text (Text)
import qualified Data.Text as T

import Abstract -- everything
 -- everything
import QQ (pdx)
import SettingsTypes ( PPT
                     , IsGame (..), IsGameData (..), IsGameState (..)

                     , setCurrentFile, withCurrentFile
                     , hoistErrors, hoistExceptions
                     , indentUp, withCurrentIndent
                     , concatMapM)
import HOI4.Common -- everything
import HOI4.SpecialHandlers ( modifiersTable)
import HOI4.Messages (ScriptMessage (..))

newHOI4CountryHistory :: Text -> HOI4CountryHistory
newHOI4CountryHistory chtag = HOI4CountryHistory chtag undefined

parseHOI4CountryHistory :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text HOI4CountryHistory)
parseHOI4CountryHistory scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr -> setCurrentFile sourceFile $ mapM processPolitics $ concatMap mapHisto scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing country history: " ++ T.unpack err
            return HM.empty
        Right countryHistoryFilesOrErrors ->
            flip HM.traverseWithKey countryHistoryFilesOrErrors $ \sourceFile echist ->
                fmap (mkCHMap . catMaybes) . forM echist $ \case
                    Left err -> do
                        traceM $ "Error parsing country history in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right cchist -> return cchist
    where
        mkCHMap :: [HOI4CountryHistory] -> HashMap Text HOI4CountryHistory
        mkCHMap = HM.fromList . map (chTag &&& id)

        mapHisto scr = case scr of
            stmt@[pdx| set_politics = @pol |] -> [stmt]
            _ -> []

processPolitics :: (IsGameState (GameState g), IsGameData (GameData g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe HOI4CountryHistory))
processPolitics (StatementBare _) = throwError "bare statement at top level"
processPolitics [pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] -> withCurrentFile $ \file -> do
            let chtag = T.pack $ take 3 $ takeFileName file
            cchist <- hoistErrors $ foldM processPoliticsAddSection
                                        (Just (newHOI4CountryHistory chtag))
                                        parts
            case cchist of
                Left err -> return (Left err)
                Right Nothing -> return (Right Nothing)
                Right (Just chist) -> withCurrentFile $ \file ->
                    return (Right (Just chist ))
        _ -> throwError "unrecognized form for set_politics"
    _ -> throwError "unrecognized form for set_politics@content"
processPolitics _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for set_politics in " <> T.pack file)

processPoliticsAddSection :: (IsGameState (GameState g), MonadError Text m) =>
    Maybe HOI4CountryHistory -> GenericStatement -> PPT g m (Maybe HOI4CountryHistory)
processPoliticsAddSection Nothing _ = return Nothing
processPoliticsAddSection cohi stmt
    = sequence (processPoliticsAddSection' <$> cohi <*> pure stmt)
    where
        processPoliticsAddSection' cohi stmt@[pdx| ruling_party = $id |] =
            let tag = chTag cohi in
            return cohi { chRulingTag = T.pack (concat[T.unpack tag , "_" , T.unpack id])}
        processPoliticsAddSection' cohi stmt@[pdx| last_election = %_ |]
            = return cohi
        processPoliticsAddSection' cohi stmt@[pdx| election_frequency = %_ |]
            = return cohi
        processPoliticsAddSection' cohi stmt@[pdx| elections_allowed = %_ |]
            = return cohi
        processPoliticsAddSection' cohi [pdx| $other = %_ |]
            = trace ("unknown set_politics in history: " ++ T.unpack other) $ return cohi
        processPoliticsAddSection' cohi _
            = trace "unrecognised form for set_politics in history" $ return cohi

{-
parseHOI4Interface :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text Text)
parseHOI4Interface scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr -> setCurrentFile sourceFile $ mapM processInterface $ concatMap (\case
                [pdx| $spriteTypes = @spr |] | T.toLower spriteTypes == "spritetypes" -> spr
                _ -> []) scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing interface: " ++ T.unpack err
            return HM.empty
        Right interfaceFilesOrErrors ->
            flip HM.traverseWithKey interfaceFilesOrErrors $ \sourceFile einterface ->
                fmap (mkInterMap . catMaybes) . forM einterface $ \case
                    Left err -> do
                        traceM $ "Error parsing interface in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right iinterface -> return iinterface
    where
        mkInterMap :: [(Text,Text)] -> HashMap Text Text
        mkInterMap interfacelist = HM.fromList interfacelist

processInterface :: (IsGameState (GameState g), MonadError Text m) => GenericStatement -> PPT g m (Either Text  (Maybe (Text, Text)))
processInterface stmt@[pdx| $spriteType = @spr |] | T.toLower spriteType == "spritetype"
    =  case (getId spr, getPic spr) of
        (Just id, Just pic) -> withCurrentFile $ \file -> return $ Right $ Just (id, pic)
        (Nothing, Just pic) -> return (Right Nothing)
        (Just id, Nothing) -> return (Right Nothing)
        _ -> return (Right Nothing)
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
processInterface stmt = return (Right Nothing)
-}
-------------
-- terrain --
-------------

parseHOI4Terrain :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m [Text]
parseHOI4Terrain scripts = do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr -> setCurrentFile sourceFile $ mapM processTerrain $ concatMap getcat scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing terrain: " ++ T.unpack err
            return []
        Right terrainFilesOrErrors ->
            return $ catMaybes $ concat $ concat $ HM.elems (HM.mapWithKey (\sourceFile eterrain -> -- probably better ways to this
                map (\case
                    Left err -> do
                        traceM $ "Error parsing terrain in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right tterrain -> return tterrain) eterrain) terrainFilesOrErrors)
    where
        getcat = \case
            [pdx| categories = @cat |] -> cat
            _ -> []

processTerrain :: (IsGameState (GameState g), IsGameData (GameData g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe Text))
processTerrain (StatementBare _) = throwError "bare statement at top level"
processTerrain [pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] -> withCurrentFile $ \file -> return (Right (Just id))
        _ -> throwError "unrecognized form for terrain"
    _ -> throwError "unrecognized form for terrain@content"
processTerrain _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for terrain in " <> T.pack file)

----------------
-- ideologies --
----------------

parseHOI4Ideology :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text Text)
parseHOI4Ideology scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr -> setCurrentFile sourceFile $ mapM processIdeology $ concatMap getideo scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing ideology: " ++ T.unpack err
            return HM.empty
        Right ideologyFilesOrErrors ->
            flip HM.traverseWithKey ideologyFilesOrErrors $ \sourceFile eideology ->
                fmap (mkIdeoMap . catMaybes) . forM eideology $ \case
                    Left err -> do
                        traceM $ "Error parsing ideology in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right iideology -> return iideology
    where
        mkIdeoMap :: [(Text,[Text])] -> HashMap Text Text
        mkIdeoMap subideolist = HM.fromList $ concatMap switchideos subideolist
        switchideos :: (Text,[Text]) -> [(Text, Text)]
        switchideos (ideo, subideo) = map (switcheroo ideo) subideo
        switcheroo :: Text -> Text -> (Text, Text)
        switcheroo ideo subideo = (subideo, ideo)

        getideo = \case
            [pdx| ideologies = @cat |] -> cat
            _ -> []

processIdeology :: (IsGameState (GameState g), IsGameData (GameData g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe (Text,[Text])))
processIdeology (StatementBare _) = throwError "bare statement at top level"
processIdeology [pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] -> withCurrentFile $ \file -> do
            let subideos = concat $ mapMaybe (\case
                    [pdx| types = @scr |] -> Just $ mapMaybe getsubs scr
                    _-> Nothing) parts
            return (Right (Just (id , subideos)))
        _ -> throwError "unrecognized form for ideology"
    _ -> throwError "unrecognized form for ideology@content"
    where
        getsubs [pdx| $subideo = @_|] = Just subideo
        getsubs stmt = Nothing
processIdeology _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for ideology in " <> T.pack file)


-----------------
-- scripted_<> --
-----------------

parseHOI4Effects :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text GenericStatement)
parseHOI4Effects scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr -> setCurrentFile sourceFile $ mapM parseHOI4Effect $ concatMap onlyscripts scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing scripted effects: " ++ T.unpack err
            return HM.empty
        Right effectFilesOrErrors ->
            flip HM.traverseWithKey effectFilesOrErrors $ \sourceFile eeffect ->
                fmap (mkEffectMap . catMaybes) . forM eeffect $ \case
                    Left err -> do
                        traceM $ "Error parsing scripted effects in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right feffect -> return feffect
    where
        mkEffectMap :: [(Text,GenericStatement)] -> HashMap Text GenericStatement
        mkEffectMap = HM.fromList
        onlyscripts = \case
            stmt@[pdx| %_ = @_|] -> [stmt]
            _ -> []

parseHOI4Effect :: (IsGameState (GameState g), IsGameData (GameData g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe (Text, GenericStatement)))
parseHOI4Effect (StatementBare _) = throwError "bare statement at top level"
parseHOI4Effect stmt@[pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] -> withCurrentFile $ \file ->
            return (Right (Just (id , stmt)))
        _ -> throwError "unrecognized form for scripted effect"
    _ -> throwError "unrecognized form for scripted effect@content"
parseHOI4Effect _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for scripted effect in " <> T.pack file)

parseHOI4Triggers :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text GenericStatement)
parseHOI4Triggers scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr -> setCurrentFile sourceFile $ mapM parseHOI4Trigger $ concatMap onlyscripts scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing scripted triggers: " ++ T.unpack err
            return HM.empty
        Right triggerFilesOrErrors ->
            flip HM.traverseWithKey triggerFilesOrErrors $ \sourceFile etrigger ->
                fmap (mkTriggerMap . catMaybes) . forM etrigger $ \case
                    Left err -> do
                        traceM $ "Error parsing scripted triggers in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right ttrigger -> return ttrigger
    where
        mkTriggerMap :: [(Text,GenericStatement)] -> HashMap Text GenericStatement
        mkTriggerMap = HM.fromList
        onlyscripts = \case
            stmt@[pdx| %_ = @_|] -> [stmt]
            _ -> []

parseHOI4Trigger :: (IsGameState (GameState g), IsGameData (GameData g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe (Text, GenericStatement)))
parseHOI4Trigger (StatementBare _) = throwError "bare statement at top level"
parseHOI4Trigger stmt@[pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] -> withCurrentFile $ \file ->
            return (Right (Just (id , stmt)))
        _ -> throwError "unrecognized form for scripted trigger"
    _ -> throwError "unrecognized form for scripted trigger@content"
parseHOI4Trigger _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for scripted trigger in " <> T.pack file)

------------------------------
-- Balance of power rangers --
------------------------------

parseHOI4BopRanges :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text HOI4BopRange)
parseHOI4BopRanges scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr -> setCurrentFile sourceFile $ mapM parseHOI4BopRange $ concatMap getRanges scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing bop ranges: " ++ T.unpack err
            return HM.empty
        Right bopFilesOrErrors ->
            flip HM.traverseWithKey bopFilesOrErrors $ \sourceFile ebop ->
                fmap (mkBopMap . catMaybes) . forM ebop $ \case
                    Left err -> do
                        traceM $ "Error parsing bop rangess in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right bbop -> return bbop
    where
        mkBopMap :: [HOI4BopRange] -> HashMap Text HOI4BopRange
        mkBopMap = HM.fromList . map (bop_id &&& id)
        getRanges :: GenericStatement -> [GenericStatement]
        getRanges = \case
            [pdx| %_ = @scrs |] -> concatMap (\case
                stmt@[pdx| range = @_ |] -> [stmt]
                stmt@[pdx| side = @scr |] -> getRanges stmt
                _ -> [])
                scrs
            _ -> []

parseHOI4BopRange :: (IsGameState (GameState g), IsGameData (GameData g), MonadError Text m) =>
    GenericStatement ->PPT g m (Either Text (Maybe HOI4BopRange))
parseHOI4BopRange (StatementBare _) = throwError "bare statement at top level"
parseHOI4BopRange stmt@[pdx| range = @scr |]
    = withCurrentFile $ \file ->
        let bop = foldl' addSection (HOI4BopRange {
                bop_id = ""
            ,   bop_on_activate = Nothing
            ,   bop_on_deactivate = Nothing
            ,   bop_path = file
            }) scr in
        return $ Right (Just bop)
    where
        addSection :: HOI4BopRange -> GenericStatement -> HOI4BopRange
        addSection bop [pdx| id = $txt |] = bop { bop_id = txt }
        addSection bop [pdx| on_activate = %rhs |] = case rhs of
                CompoundRhs [] -> bop
                CompoundRhs scr -> bop { bop_on_activate = Just scr }
                _-> trace "bad bop on_activate" bop
        addSection bop [pdx| on_deactivate = %rhs |] = case rhs of
                CompoundRhs [] -> bop
                CompoundRhs scr -> bop { bop_on_deactivate = Just scr }
                _-> trace "bad bop on_activate" bop
        addSection bop [pdx| min = %_ |] = bop
        addSection bop [pdx| max = %_ |] = bop
        addSection bop [pdx| modifier = %_ |] = bop
        addSection bop stmt = trace ("Urecognized statement in bop range: " ++ show stmt) bop
parseHOI4BopRange stmt = trace (show stmt) $ withCurrentFile $ \file ->
    throwError ("unrecognised form for range in bop in " <> T.pack file)

-- Modifier Definitions

parseHOI4ModifierDefinitions scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr -> setCurrentFile sourceFile $ mapM parseHOI4ModifierDefinition $ concatMap onlyscripts scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing modifier definitions: " ++ T.unpack err
            return HM.empty
        Right moddefFilesOrErrors ->
            flip HM.traverseWithKey moddefFilesOrErrors $ \sourceFile emoddef ->
                fmap (mkTriggerMap . catMaybes) . forM emoddef $ \case
                    Left err -> do
                        traceM $ "Error parsing modifier definitions in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right mmoddef -> return mmoddef
    where
        mkTriggerMap :: [(Text,Text-> Double -> ScriptMessage)] -> HashMap Text (Text-> Double -> ScriptMessage)
        mkTriggerMap = HM.fromList
        onlyscripts = \case
            stmt@[pdx| %_ = @_|] -> [stmt]
            _ -> []

data ModDef = ModDef
        {   mdef_color_type :: Text
        ,   mdef_value_type :: Text
        ,   mdef_precision :: Double
        ,   mdef_postfix :: Maybe Text
        }

newMDF :: ModDef
newMDF = ModDef "<!--Check Script-->" "<!--Check Script-->" 0 Nothing

parseHOI4ModifierDefinition :: (IsGameState (GameState g), IsGameData (GameData g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe (Text, Text-> Double -> ScriptMessage)))
parseHOI4ModifierDefinition (StatementBare _) = throwError "bare statement at top level"
parseHOI4ModifierDefinition stmt@[pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] -> withCurrentFile $ \file -> do
            let mdefdata = getscrmess id =<< foldM addSection newMDF parts
            return $ Right mdefdata
        _ -> throwError "unrecognized form for scripted trigger"
    _ -> throwError "unrecognized form for scripted trigger@content"
    where
        addSection mdf [pdx| color_type = $ctype |] = return $ mdf { mdef_color_type = ctype }
        addSection mdf [pdx| value_type = $vtype |] = return $ mdf { mdef_value_type = vtype }
        addSection mdf [pdx| category = %_ |] = return mdf
        addSection mdf [pdx| precision = !precision |] = return $ mdf { mdef_precision = precision }
        addSection mdf [pdx| postfix = $psfix |] = return mdf { mdef_postfix = Just psfix }
        addSection mdf stmt = return $ trace ("Urecognized statement in modifier definition: " ++ show stmt) mdf

        getscrmess :: Text -> ModDef -> Maybe (Text, Text -> Double -> ScriptMessage)
        getscrmess mdid mdf = case T.toLower $ mdef_color_type mdf of
            "good" -> case T.toLower $ mdef_value_type mdf of
                "number" -> Just (mdid, MsgModifierColourPos)
                "percentage" -> Just (mdid, MsgModifierPcPosReduced)
                "percentage_in_hundred" -> Just (mdid, MsgModifierPcPos)
                "yes_no" -> Just (mdid, MsgModifierYesNo)
                _ -> Nothing
            "neutral" -> case T.toLower $ mdef_value_type mdf of
                "number" -> Just (mdid, MsgModifierSign)
                "percentage" -> Just (mdid, MsgModifierPcReducedSign)
                "percentage_in_hundred" -> Just (mdid, MsgModifierPcSign)
                "yes_no" -> Just (mdid, MsgModifierYesNo)
                _ -> Nothing
            "bad" -> case T.toLower $ mdef_value_type mdf of
                "number" -> Just (mdid, MsgModifierColourNeg)
                "percentage" -> Just (mdid, MsgModifierPcNegReduced)
                "percentage_in_hundred" -> Just (mdid, MsgModifierPcNeg)
                "yes_no" -> Just (mdid, MsgModifierYesNo)
                _ -> Nothing
            _ -> Nothing

parseHOI4ModifierDefinition _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for scripted trigger in " <> T.pack file)


parseHOI4LocKeys order = return $ map fst (sortOn (\x -> elemIndex (snd x) order) . filter (modchk . snd) . HM.toList . HM.map fst $ modifiersTable)
    where modchk = T.all (\xs -> isUpper xs || not (isAlphaNum xs))
