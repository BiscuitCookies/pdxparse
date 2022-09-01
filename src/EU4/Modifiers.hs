{-|
Module      : EU4.Modifiers
Description : Country, ruler, province and opinion modifiers
-}
module EU4.Modifiers (
        parseEU4Modifiers, writeEU4Modifiers
    ,   parseEU4OpinionModifiers, writeEU4OpinionModifiers
    ,   parseEU4ProvTrigModifiers, writeEU4ProvTrigModifiers
    ) where

import Control.Arrow ((&&&))
import Control.Monad (foldM, forM, join)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Trans (MonadIO (..))
import Control.Monad.State (gets)

import Data.Maybe (isJust, fromJust, fromMaybe, catMaybes)
import Data.Monoid ((<>))
import Data.List (sortOn, intersperse, foldl')
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
                     , setCurrentFile, withCurrentFile
                     , hoistErrors, hoistExceptions)
import EU4.Types -- everything
import EU4.Common (extractStmt, matchExactText, ppMany)
import FileIO (Feature (..), writeFeatures)
import Text.PrettyPrint.Leijen.Text (Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP
import qualified Doc
import Messages
import MessageTools

import Debug.Trace (trace, traceM)

parseEU4Modifiers :: (IsGameData (GameData g), IsGameState (GameState g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text EU4Modifier)
parseEU4Modifiers scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr ->
                setCurrentFile sourceFile $ mapM parseEU4Modifier scr)
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
                where mkModMap :: [EU4Modifier] -> HashMap Text EU4Modifier
                      mkModMap = HM.fromList . map (modName &&& id)

parseEU4Modifier :: (IsGameData (GameData g), IsGameState (GameState g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe EU4Modifier))
parseEU4Modifier [pdx| $modid = @effects |]
    = withCurrentFile $ \file -> do
        mlocid <- getGameL10nIfPresent modid

        -- Handle religions modifiers
        let (mrelstmt, rest) = extractStmt (matchExactText "religion" "yes") effects
        return . Right . Just $ EU4Modifier {
                modName = modid
            ,   modLocName = mlocid
            ,   modPath = file
            ,   modReligious = isJust mrelstmt
            ,   modEffects = rest
            }
parseEU4Modifier _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for modifier in " <> T.pack file)

-- | Present the parsed modifiers as wiki text and write them to the
-- appropriate files.
writeEU4Modifiers :: (EU4Info g, MonadError Text m, MonadIO m) => PPT g m ()
writeEU4Modifiers = throwError "Sorry, writing all modifiers currently not supported."

parseEU4OpinionModifiers :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text EU4OpinionModifier)
parseEU4OpinionModifiers scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr ->
                setCurrentFile sourceFile $ mapM parseEU4OpinionModifier scr)
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
                where mkModMap :: [EU4OpinionModifier] -> HashMap Text EU4OpinionModifier
                      mkModMap = HM.fromList . map (omodName &&& id)

newEU4OpinionModifier id locid path = EU4OpinionModifier id locid path Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing

-- | Parse a statement in an opinion modifiers file. Some statements aren't
-- modifiers; for those, and for any obvious errors, return Right Nothing.
parseEU4OpinionModifier :: (IsGameState (GameState g), IsGameData (GameData g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe EU4OpinionModifier))
parseEU4OpinionModifier (StatementBare _) = throwError "bare statement at top level"
parseEU4OpinionModifier [pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] -> withCurrentFile $ \file -> do
            locid <- getGameL10nIfPresent id
            mmod <- hoistErrors $ foldM opinionModifierAddSection
                                        (Just (newEU4OpinionModifier id locid file))
                                        parts
            case mmod of
                Left err -> return (Left err)
                Right Nothing -> return (Right Nothing)
                Right (Just mod) -> withCurrentFile $ \file ->
                    return (Right (Just mod ))
        _ -> throwError "unrecognized form for opinion modifier"
    _ -> throwError "unrecognized form for opinion modifier"
parseEU4OpinionModifier _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for opinion modifier in " <> T.pack file)

-- | Interpret one section of an opinion modifier. If understood, add it to the
-- event data. If not understood, throw an exception.
opinionModifierAddSection :: (IsGameState (GameState g), MonadError Text m) =>
    Maybe EU4OpinionModifier -> GenericStatement -> PPT g m (Maybe EU4OpinionModifier)
opinionModifierAddSection Nothing _ = return Nothing
opinionModifierAddSection mmod stmt
    = sequence (opinionModifierAddSection' <$> mmod <*> pure stmt)
    where
        opinionModifierAddSection' mod stmt@[pdx| opinion = !rhs |]
            = return (mod { omodOpinion = Just rhs })
        opinionModifierAddSection' mod stmt@[pdx| max = !rhs |]
            = return (mod { omodMax = Just rhs })
        opinionModifierAddSection' mod stmt@[pdx| min = !rhs |]
            = return (mod { omodMin = Just rhs })
        opinionModifierAddSection' mod stmt@[pdx| yearly_decay = !rhs |]
            = return (mod { omodYearlyDecay = Just rhs })
        opinionModifierAddSection' mod stmt@[pdx| months = !rhs |]
            = return (mod { omodMonths = Just rhs })
        opinionModifierAddSection' mod stmt@[pdx| years = !rhs |]
            = return (mod { omodYears = Just rhs })
        opinionModifierAddSection' mod stmt@[pdx| max_vassal = !rhs |]
            = return (mod { omodMaxVassal = Just rhs })
        opinionModifierAddSection' mod stmt@[pdx| max_in_other_direction = !rhs |]
            = return (mod { omodMaxInOtherDirection = Just rhs })
        opinionModifierAddSection' mod [pdx| $other = %_ |]
            = trace ("unknown opinion modifier section: " ++ T.unpack other) $ return mod
        opinionModifierAddSection' mod _
            = trace ("unrecognised form for opinion modifier section") $ return mod

writeEU4OpinionModifiers :: (EU4Info g, MonadIO m) => PPT g m ()
writeEU4OpinionModifiers = do
    opinionModifiers <- getOpinionModifiers
    writeFeatures "opinion_modifiers"
                  [Feature { featurePath = Just "templates"
                           , featureId = Just "opinion_modifier.txt"
                           , theFeature = Right (HM.elems opinionModifiers)
                           }]
                  pp_opinion_modifers

-- Based on https://hoi4.paradoxwikis.com/Template:Opinion
pp_opinion_modifers :: (EU4Info g, Monad m) => [EU4OpinionModifier] -> PPT g m Doc
pp_opinion_modifers modifiers = do
    version <- gets (gameVersion . getSettings)
    modifiers_pp'd <- mapM pp_opinion_modifer (sortOn omodName modifiers)
    return . mconcat $ ["<includeonly>{{#switch:{{lc:{{{1}}} }}", PP.line]
        ++ modifiers_pp'd ++
        ["}}</includeonly><noinclude>{{Version|", Doc.strictText version, "}}"
        , PP.line
        , "Automatically generated from the file(s): "
        , Doc.strictText $ T.pack $ concat $ intersperse ", " (map (\p -> "{{path|"++p++"}}") ((toList . fromList) (map omodPath modifiers)))
        , PP.line, PP.line
        , "{{template doc}}", PP.line
        , "[[Category:Templates]]</noinclude>"
        , PP.line
        ]



pp_opinion_modifer :: (EU4Info g, Monad m) => EU4OpinionModifier -> PPT g m Doc
pp_opinion_modifer mod = do
    locName <- getGameL10n (omodName mod)
    return . mconcat $
        [ "| "
        , Doc.strictText (omodName mod)
        , " = "
        , iquotes locName
        , " {{#ifeq:{{{2|}}}|0|| ("
        ] ++
        intersperse " / " (
            (modText "{{icon|opinion}} " " Opinion" (omodOpinion mod))
            ++ (yearlyDecay (omodOpinion mod) (omodYearlyDecay mod))
            ++ (modText "" " Min" (omodMin mod))
            ++ (modText "" " Max" (omodMax mod))
            ++ (modText "" " Max for vassal" (omodMaxVassal mod))
            ++ (modText "" " Max for sender" (omodMaxInOtherDirection mod))
            ++ (duration (omodMonths mod) (omodYears mod))
        ) ++
        [ ") }}"
        , PP.line
        ]

    where
        modText :: Text -> Text -> Maybe Double -> [Doc]
        modText p s (Just val) | val /= 0 = [mconcat [ Doc.strictText p, colourNumSign True val, Doc.strictText s ]]
        modText _ _ _ = []

        yearlyDecay :: Maybe Double -> Maybe Double -> [Doc]
        yearlyDecay (Just op) (Just decay) = [mconcat [
                colourNumSign True (if op < 0 then decay else -decay)
                , Doc.strictText " Yearly decay"
            ]]
        yearlyDecay _ _ = []

        duration :: Maybe Double -> Maybe Double -> [Doc]
        duration (Just m) Nothing | m /= 0 = [fmt "Month" m]
        duration Nothing (Just y) | y /= 0 = [fmt "Year" y]
        duration (Just m) (Just y) | m /= 0 || y /= 0 = [mconcat [fmt "Year" y, " and ", fmt "Month" m]]
        duration _ _ = []

        fmt :: Text -> Double -> Doc
        fmt t v = mconcat [ plainNum v, " ", Doc.strictText $ t <> (if v == 1.0 then "" else "s") ]

parseEU4ProvTrigModifiers :: (IsGameData (GameData g), IsGameState (GameState g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text EU4ProvinceTriggeredModifier)
parseEU4ProvTrigModifiers scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr ->
                setCurrentFile sourceFile $ mapM parseEU4ProvTrigModifier scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing province triggered modifiers: " ++ T.unpack err
            return HM.empty
        Right modifiersFilesOrErrors ->
            flip HM.traverseWithKey modifiersFilesOrErrors $ \sourceFile emods ->
                fmap (mkModMap . catMaybes) . forM emods $ \case
                    Left err -> do
                        traceM $ "Error parsing province triggered modifiers in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right mmod -> return mmod
                where mkModMap :: [EU4ProvinceTriggeredModifier] -> HashMap Text EU4ProvinceTriggeredModifier
                      mkModMap = HM.fromList . map (ptmodName &&& id)

parseEU4ProvTrigModifier :: (IsGameData (GameData g), IsGameState (GameState g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe EU4ProvinceTriggeredModifier))
parseEU4ProvTrigModifier [pdx| $modid = @effects |]
    = withCurrentFile $ \file -> do
        mlocid <- getGameL10nIfPresent modid
        let ptm = foldl' addSection (EU4ProvinceTriggeredModifier {
                ptmodName = modid
            ,   ptmodLocName = mlocid
            ,   ptmodPath = file
            ,   ptmodEffects = []
            ,   ptmodPotential = []
            ,   ptmodTrigger = []
            ,   ptmodOnActivation = []
            ,   ptmodOnDeactivation = []
            }) effects
        return $ Right (Just ptm)
    where
        addSection :: EU4ProvinceTriggeredModifier -> GenericStatement -> EU4ProvinceTriggeredModifier
        addSection ptm stmt@[pdx| $lhs = @scr |] = case lhs of
            "potential"       -> ptm { ptmodPotential = scr }
            "trigger"         -> ptm { ptmodTrigger = scr }
            "on_activation"   -> ptm { ptmodOnActivation = scr }
            "on_deactivation" -> ptm { ptmodOnDeactivation = scr }
            _ -> (trace $ "Urecognized statement in province triggered modifier: " ++ show stmt) $ ptm
         -- Must be an effect
        addSection ptm stmt = ptm { ptmodEffects = (ptmodEffects ptm) ++ [stmt] }
parseEU4ProvTrigModifier stmt = (trace $ show stmt) $ withCurrentFile $ \file ->
    throwError ("unrecognised form for province triggered modifier in " <> T.pack file)

writeEU4ProvTrigModifiers :: (EU4Info g, MonadIO m) => PPT g m ()
writeEU4ProvTrigModifiers = do
    provTrigModifiers <- getProvinceTriggeredModifiers
    writeFeatures "province_triggered_modifiers"
                  [Feature { featurePath = Just "tables"
                           , featureId = Just "province_triggered_modifiers.txt"
                           , theFeature = Right (HM.elems provTrigModifiers)
                           }]
                  pp_prov_trig_modifiers
    where
        pp_prov_trig_modifiers :: (EU4Info g, Monad m) => [EU4ProvinceTriggeredModifier] -> PPT g m Doc
        pp_prov_trig_modifiers mods = do
            version <- gets (gameVersion . getSettings)
            modDoc <- mapM pp_prov_trig_modifier (sortOn (sortName . ptmodLocName) mods)
            return $ mconcat $
                [ "{{Version|", Doc.strictText version, "}}", PP.line
                , "{| class=\"mildtable\"", PP.line
                , "! style=\"min-width:260px; text-align:center\" | Name", PP.line
                , "! style=\"text-align:center\" | Requirements", PP.line
                , "! style=\"min-width:260px; text-align:center\" | Effects", PP.line
                , "! | Additional effects", PP.line
                ] ++ modDoc ++
                [ "|}", PP.line
                ]

        sortName (Just n) =
            let ln = T.toLower n
                nn = T.stripPrefix "the " ln
            in fromMaybe ln nn
        sortName _ = ""

        pp_prov_trig_modifier :: (EU4Info g, Monad m) => EU4ProvinceTriggeredModifier -> PPT g m Doc
        pp_prov_trig_modifier mod = do
            req <- imsg2doc =<< ppMany ((ptmodPotential mod) ++ (ptmodTrigger mod))
            eff <- imsg2doc =<< scope EU4Bonus (ppMany (ptmodEffects mod))
            act <- withHeader "When activated:" (ptmodOnActivation mod)
            dea <- withHeader "When deactivated:" (ptmodOnDeactivation mod)
            return $ mconcat
                [ "|- style=\"vertical-align:top;\"", PP.line
                , "|" , PP.line
                , "==== ", Doc.strictText $ fromMaybe (ptmodName mod) (ptmodLocName mod) , " ====", PP.line
                , "| <!-- ", Doc.strictText (ptmodName mod), " -->", PP.line
                , req , PP.line
                , "|", PP.line
                , eff, PP.line
                , "|", PP.line
                , act, dea, PP.line
                ]

        withHeader :: (EU4Info g, Monad m) => Text -> GenericScript -> PPT g m Doc
        withHeader _ [] = return $ mconcat []
        withHeader hdr stmts = do
            stpp'd <- imsg2doc =<< ppMany stmts
            return $ mconcat
                [ Doc.strictText hdr, PP.line
                , stpp'd, PP.line
                ]

