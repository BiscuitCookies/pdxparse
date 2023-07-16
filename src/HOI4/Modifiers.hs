{-|
Module      : HOI4.Modifiers
Description : Country, ruler, dynamic and opinion modifiers
-}
module HOI4.Modifiers (
--        parseHOI4Modifiers, writeHOI4Modifiers,
        parseHOI4OpinionModifiers, writeHOI4OpinionModifiers
    ,   parseHOI4DynamicModifiers, writeHOI4DynamicModifiers
    ,   parseHOI4Modifiers
    ) where

import Control.Arrow ((&&&))
import Control.Monad (foldM, forM, join)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Trans (MonadIO (..))
import Control.Monad.State (gets)

import Data.Foldable (fold)
import Data.Maybe (isJust, fromJust, fromMaybe, catMaybes)
import Data.Monoid ((<>))
import Data.List ( sortOn, intersperse, foldl', intercalate )
import Data.Set (toList, fromList)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import Data.Text (Text)
import qualified Data.Text as T

import Abstract -- everything
import QQ (pdx)
import SettingsTypes ( PPT, Settings (..){-, Game (..)-}
                     {-, IsGame (..)-}, IsGameData (..), IsGameState (..), GameState (..)
                     , getGameL10n, getGameL10nIfPresent
                     , setCurrentFile, withCurrentFile, withCurrentIndent
                     , hoistErrors, hoistExceptions
                     , getGameInterface)
import HOI4.Types -- everything
import HOI4.Common (extractStmt, matchExactText, ppMany)
import FileIO (Feature (..), writeFeatures)
import Text.PrettyPrint.Leijen.Text (Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP
import qualified Doc
import HOI4.Messages
import MessageTools

import Debug.Trace (trace, traceM)
import HOI4.SpecialHandlers (modifierMSG)

parseHOI4OpinionModifiers :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text HOI4OpinionModifier)
parseHOI4OpinionModifiers scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr -> setCurrentFile sourceFile $ mapM parseHOI4OpinionModifier $ concatMap (\case
                [pdx| opinion_modifiers = @mods |] -> mods
                _ -> scr)
                scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing opinion modifiers: " ++ T.unpack err
            return HM.empty
        Right modifiersFilesOrErrors ->
            flip HM.traverseWithKey modifiersFilesOrErrors $ \sourceFile emods ->
                fmap (mkModMap . catMaybes) . forM emods $ \case
                    Left err -> do
                        traceM $ "Error parsing modifiers in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right mmod -> return mmod
                where mkModMap :: [HOI4OpinionModifier] -> HashMap Text HOI4OpinionModifier
                      mkModMap = HM.fromList . map (omodName &&& id)

newHOI4OpinionModifier :: Text -> Maybe Text -> FilePath -> HOI4OpinionModifier
newHOI4OpinionModifier id locid path = HOI4OpinionModifier id locid path Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing

-- | Parse a statement in an opinion modifiers file. Some statements aren't
-- modifiers; for those, and for any obvious errors, return Right Nothing.
parseHOI4OpinionModifier :: (IsGameState (GameState g), IsGameData (GameData g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe HOI4OpinionModifier))
parseHOI4OpinionModifier (StatementBare _) = throwError "bare statement at top level"
parseHOI4OpinionModifier [pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] -> withCurrentFile $ \file -> do
            locid <- getGameL10nIfPresent id
            mmod <- hoistErrors $ foldM opinionModifierAddSection
                                        (Just (newHOI4OpinionModifier id locid file))
                                        parts
            case mmod of
                Left err -> return (Left err)
                Right Nothing -> return (Right Nothing)
                Right (Just mod) -> withCurrentFile $ \file ->
                    return (Right (Just mod ))
        _ -> throwError "unrecognized form for opinion modifier"
    _ -> throwError "unrecognized form for opinion modifier"
parseHOI4OpinionModifier _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for opinion modifier in " <> T.pack file)

-- | Interpret one section of an opinion modifier. If understood, add it to the
-- event data. If not understood, throw an exception.
opinionModifierAddSection :: (IsGameState (GameState g), MonadError Text m) =>
    Maybe HOI4OpinionModifier -> GenericStatement -> PPT g m (Maybe HOI4OpinionModifier)
opinionModifierAddSection Nothing _ = return Nothing
opinionModifierAddSection mmod stmt
    = sequence (opinionModifierAddSection' <$> mmod <*> pure stmt)
    where
        opinionModifierAddSection' mod stmt@[pdx| value = !rhs |]
            = return (mod { omodValue = Just rhs })
        opinionModifierAddSection' mod stmt@[pdx| max_trust = !rhs |]
            = return (mod { omodMax = Just rhs })
        opinionModifierAddSection' mod stmt@[pdx| min_trust = !rhs |]
            = return (mod { omodMin = Just rhs })
        opinionModifierAddSection' mod stmt@[pdx| decay = !rhs |]
            = return (mod { omodDecay = Just rhs })
        opinionModifierAddSection' mod stmt@[pdx| days = !rhs |]
            = return (mod { omodDays = Just rhs })
        opinionModifierAddSection' mod stmt@[pdx| months = !rhs |]
            = return (mod { omodMonths = Just rhs })
        opinionModifierAddSection' mod stmt@[pdx| years = !rhs |]
            = return (mod { omodYears = Just rhs })
        opinionModifierAddSection' mod stmt@[pdx| trade = %rhs |] = case rhs of
            GenericRhs "yes" [] -> return mod { omodTrade = Just True }
            -- no is the default, so I don't think this is ever used
            GenericRhs "no" [] -> return mod { omodTrade = Just False }
            _ -> throwError "bad trade opinion"
        opinionModifierAddSection' mod stmt@[pdx| target = %rhs |] = case rhs of
            GenericRhs "yes" [] -> return mod { omodTarget = Just True }
            -- no is the default, so I don't think this is ever used
            GenericRhs "no" [] -> return mod { omodTarget = Just False }
            _ -> throwError "bad target opinion"
        opinionModifierAddSection' mod [pdx| $other = %_ |]
            = trace ("unknown opinion modifier section: " ++ T.unpack other) $ return mod
        opinionModifierAddSection' mod _
            = trace "unrecognised form for opinion modifier section" $ return mod

writeHOI4OpinionModifiers :: (HOI4Info g, MonadIO m) => PPT g m ()
writeHOI4OpinionModifiers = do
    opinionModifiers <- getOpinionModifiers
    writeFeatures "opinion_modifiers"
                  [Feature { featurePath = Just "templates"
                           , featureId = Just "opinion_modifier.txt"
                           , theFeature = Right (HM.elems opinionModifiers)
                           }]
                  ppOpinionModifiers

-- Based on https://hoi4.paradoxwikis.com/Template:Opinion
ppOpinionModifiers :: (HOI4Info g, Monad m) => [HOI4OpinionModifier] -> PPT g m Doc
ppOpinionModifiers modifiers = do
    version <- gets (gameVersion . getSettings)
    modifiers_pp'd <- mapM ppOpinionModifier (sortOn (T.toCaseFold . omodName) modifiers)
    return . mconcat $ ["<includeonly>{{#switch:{{ lc:{{{1}}} }}", PP.line
        ,"| #default = <span style=\"color: red; font-size: 11px;\">(unrecognized string \"{{{1}}}\" for [[Template:Opinion]])</span>[[Category:Pages with unrecognized opinion modifier strings]]", PP.line]
        ++ modifiers_pp'd ++
        ["}}</includeonly><noinclude>{{Version|", Doc.strictText version, "}}"
        , PP.line
        , "Automatically generated from the file(s): "
        , Doc.strictText $ T.pack $ intercalate ", " (map (\p -> "{{path|"++p++"}}") ((toList . fromList) (map omodPath modifiers)))
        , PP.line, PP.line
        , "{{template doc}}", PP.line
        , "[[Category:Templates]]</noinclude>"
        , PP.line
        ]



ppOpinionModifier :: (HOI4Info g, Monad m) => HOI4OpinionModifier -> PPT g m Doc
ppOpinionModifier mod = do
    locName <- getGameL10n (omodName mod)
    return . mconcat $
        [ "| "
        , Doc.strictText $ T.toLower (omodName mod)
        , " = "
        , iquotes locName
        , " {{#ifeq:{{{2|}}}|0|| ("
        ] ++
        intersperse " / " (
            if isTrade then
                modText "" " Trade relation" (omodValue mod)
                else
                   modText "{{icon|opinion}} " " opinion" (omodValue mod)
            ++ modText "" " min" (omodMin mod)
            ++ modText "" " max" (omodMax mod)
            ++ duration (omodDays mod) (omodMonths mod) (omodYears mod)
            ++ monthlyDecay (omodValue mod) (omodDecay mod)
        ) ++
        [ ") }}"
        , PP.line
        ]

    where
        modText :: Text -> Text -> Maybe Double -> [Doc]
        modText p s (Just val) | val /= 0 = [mconcat [ Doc.strictText p, templateColor $ colourNumSign True val, Doc.strictText s ]]
        modText _ _ _ = []

        isTrade = fromMaybe False $ omodTrade mod
        isTarget = fromMaybe False $ omodTarget mod

        monthlyDecay :: Maybe Double -> Maybe Double -> [Doc]
        monthlyDecay (Just op) (Just decay) = [mconcat [
                templateColor $ colourNumSign True (if op < 0 then decay else -decay)
                , Doc.strictText " Monthly decay"
            ]]
        monthlyDecay _ _ = []

        duration :: Maybe Double -> Maybe Double -> Maybe Double -> [Doc]
        duration (Just d) Nothing Nothing   | d /= 0 = [mconcat ["{{icon|time}} ", Doc.strictText $ formatDays d]]
        duration Nothing (Just m) Nothing   | m /= 0 = [mconcat ["{{icon|time}} ", Doc.strictText $ formatMonths m]]
        duration Nothing Nothing (Just y)   | y /= 0 = [mconcat ["{{icon|time}} ", Doc.strictText $ formatYears $ floor y]]
        duration (Just d) (Just m) Nothing  | d /= 0 || m /= 0 = [mconcat ["{{icon|time}} ", fmt "month" m, " and ", fmt "day" d]]
        duration (Just d) Nothing (Just y)  | d /= 0 || y /= 0 = [mconcat ["{{icon|time}} ", Doc.strictText $ formatDays (y*356+d)]]
        duration Nothing (Just m) (Just y)  | m /= 0 || y /= 0 = [mconcat ["{{icon|time}} ", Doc.strictText $ formatMonths (y*12+m)]]
        duration (Just d) (Just m) (Just y) | d /= 0 || m /= 0 || y /= 0 = [mconcat ["{{icon|time}} ", fmt "year" y, " and ", fmt "month" m, " and ", fmt "day" d]]
        duration _ _ _ = []

        fmt :: Text -> Double -> Doc
        fmt t v = mconcat [ plainNum v, " ", Doc.strictText $ t <> (if v == 1.0 then "" else "s") ]

parseHOI4DynamicModifiers :: (IsGameData (GameData g), IsGameState (GameState g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text HOI4DynamicModifier)
parseHOI4DynamicModifiers scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr ->
                setCurrentFile sourceFile $ mapM parseHOI4DynamicModifier scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing dynamic modifiers: " ++ T.unpack err
            return HM.empty
        Right modifiersFilesOrErrors ->
            flip HM.traverseWithKey modifiersFilesOrErrors $ \sourceFile emods ->
                fmap (mkModMap . catMaybes) . forM emods $ \case
                    Left err -> do
                        traceM $ "Error parsing dynamic modifiers in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right mmod -> return mmod
                where mkModMap :: [HOI4DynamicModifier] -> HashMap Text HOI4DynamicModifier
                      mkModMap = HM.fromList . map (dmodName &&& id)

parseHOI4DynamicModifier :: (IsGameData (GameData g), IsGameState (GameState g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe HOI4DynamicModifier))
parseHOI4DynamicModifier [pdx| $modid = @effects |]
    = withCurrentFile $ \file -> do
        mlocid <- getGameL10nIfPresent modid
        let dmd = foldl' addSection (HOI4DynamicModifier {
                dmodName = modid
            ,   dmodLocName = mlocid
            ,   dmodPath = file
            ,   dmodIcon = Nothing
            ,   dmodEffects = []
            ,   dmodEnable = []
            ,   dmodRemoveTrigger = Nothing
            }) effects
        return $ Right (Just dmd)
    where
        addSection :: HOI4DynamicModifier -> GenericStatement -> HOI4DynamicModifier
        addSection dmd stmt@[pdx| $lhs = @scr |] = case lhs of
            "enable"       -> dmd { dmodEnable = scr }
            "remove_trigger" -> dmd { dmodRemoveTrigger = Just scr }
            _ -> trace ("Urecognized statement in dynamic modifier: " ++ show stmt) dmd
        addSection dmd stmt@[pdx| icon = $txt |] = dmd  { dmodIcon = Just txt }
         -- Must be an effect
        addSection dmd stmt = dmd { dmodEffects = dmodEffects dmd ++ [stmt] }
parseHOI4DynamicModifier stmt = trace (show stmt) $ withCurrentFile $ \file ->
    throwError ("unrecognised form for dynamic modifier in " <> T.pack file)

writeHOI4DynamicModifiers :: (HOI4Info g, MonadIO m) => PPT g m ()
writeHOI4DynamicModifiers = do
    dynamicModifiers <- getDynamicModifiers
    writeFeatures "dynamic_modifiers"
                  [Feature { featurePath = Just "tables"
                           , featureId = Just "dynamic_modifiers.txt"
                           , theFeature = Right (HM.elems dynamicModifiers)
                           }]
                  pp_dynamic_modifiers
    where
        pp_dynamic_modifiers :: (HOI4Info g, Monad m) => [HOI4DynamicModifier] -> PPT g m Doc
        pp_dynamic_modifiers mods = do
            version <- gets (gameVersion . getSettings)
            modDoc <- mapM pp_dynamic_modifier (sortOn (sortName . dmodLocName) mods)
            return $ mconcat $
                [ "{{Version|", Doc.strictText version, "}}", PP.line
                , "{| class=\"mildtable\"", PP.line
                , "! ", PP.line
                , "! style=\"min-width:260px; text-align:center\" | Name", PP.line
                , "! style=\"text-align:center\" | Requirements", PP.line
                , "! style=\"min-width:260px; text-align:center\" | Effects", PP.line
                ] ++ modDoc ++
                [ "|}", PP.line
                ]

        sortName (Just n) =
            let ln = T.toLower n
                nn = T.stripPrefix "the " ln
            in fromMaybe ln nn
        sortName _ = ""

        pp_dynamic_modifier :: (HOI4Info g, Monad m) => HOI4DynamicModifier -> PPT g m Doc
        pp_dynamic_modifier mod = do
            req <- imsg2doc =<< ppMany (dmodEnable mod)
            icon <- maybe (return mempty) (\i -> do
                icond <- getGameInterface "idea_unknown" i
                return $ "[[File:" <> icond <> ".png]]") (dmodIcon mod)
            loc <- do
                mloc <- getGameL10nIfPresent (dmodName mod <> "_desc")
                case mloc of
                    Just locd -> do
                        let docloc = Doc.strictText locd
                        return $ mconcat [docloc, PP.line]
                    _ -> return ""
            eff <- withCurrentIndent $ \_ -> do imsg2doc . fold =<< traverse (modifierMSG False "") (dmodEffects mod)
            return $ mconcat
                [ "|- style=\"vertical-align:top;\"", PP.line
                , "| ", Doc.strictText icon, PP.line
                , "| ", PP.line
                , "==== ", Doc.strictText $ fromMaybe (dmodName mod) (dmodLocName mod) , " ===="
                , " <!-- ", Doc.strictText (dmodName mod), " -->", PP.line
                , loc
                , "| ", PP.line
                , req , PP.line
                , "|", PP.line
                , eff, PP.line
                ]


parseHOI4Modifiers :: (IsGameData (GameData g), IsGameState (GameState g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text HOI4Modifier)
parseHOI4Modifiers scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr ->
                setCurrentFile sourceFile $ mapM parseHOI4Modifier scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing modifiers: " ++ T.unpack err
            return HM.empty
        Right modifiersFilesOrErrors ->
            flip HM.traverseWithKey modifiersFilesOrErrors $ \sourceFile emods ->
                fmap (mkModMap . catMaybes) . forM emods $ \case
                    Left err -> do
                        traceM $ "Error parsing modifiers in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right mmod -> return mmod
                where mkModMap :: [HOI4Modifier] -> HashMap Text HOI4Modifier
                      mkModMap = HM.fromList . map (modName &&& id)

parseHOI4Modifier :: (IsGameData (GameData g), IsGameState (GameState g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe HOI4Modifier))
parseHOI4Modifier [pdx| $modid = @effects |]
    = withCurrentFile $ \file -> do
        mlocid <- getGameL10nIfPresent modid
        let modi = foldl' addSection (HOI4Modifier {
                modName = modid
            ,   modLocName = mlocid
            ,   modPath = file
            ,   modIcon = Nothing
            ,   modEffects = []
            ,   modRemoveTrigger = Nothing
            }) effects
        return $ Right (Just modi)
    where
        addSection :: HOI4Modifier -> GenericStatement -> HOI4Modifier
        addSection modi stmt@[pdx| $lhs = @scr |] = case lhs of
            "valid_relation_trigger" -> modi { modRemoveTrigger = Just scr }
            _ -> trace ("Urecognized statement in modifier: " ++ show stmt) modi
        addSection modi stmt@[pdx| icon = $txt |] = modi  { modIcon = Just txt }
         -- Must be an effect
        addSection modi stmt = modi { modEffects = modEffects modi ++ [stmt] }
parseHOI4Modifier stmt = trace (show stmt) $ withCurrentFile $ \file ->
    throwError ("unrecognised form for modifier in " <> T.pack file)