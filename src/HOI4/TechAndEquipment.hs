{-
Module      : HOI4.TechAndEquipment
Description : Feature handler for tech and equipment features in Hearts of Iron IV
-}
module HOI4.TechAndEquipment (
        parseHOI4TechnologiesPath, writeHOI4Technologies
    ) where

import Debug.Trace (trace, traceM)

import Control.Arrow ((&&&))
import Control.Monad (foldM, forM)
import Control.Monad.Except (ExceptT (..), MonadError (..))
import Control.Monad.State (MonadState (..), gets)
import Control.Monad.Trans (MonadIO (..))

import Data.List ( foldl', sortOn )
import Data.Maybe (catMaybes, fromMaybe, mapMaybe, isJust)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T
import Text.PrettyPrint.Leijen.Text (Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP
import System.FilePath ((</>), takeBaseName)

import Abstract -- everything
import qualified Doc
import FileIO (Feature (..), writeFeatures)
import HOI4.Messages -- everything
import MessageTools
import QQ (pdx)
import SettingsTypes ( PPT, Settings (..)
                     , IsGame (..), IsGameData (..), IsGameState (..)
                     , withCurrentIndent, getGameInterface
                     , getGameL10n, getGameL10nIfPresent
                     , setCurrentFile, withCurrentFile
                     , hoistErrors, hoistExceptions, getGameInterfaceIfPresent, concatMapM, indentUp, getGameL10nDefault)
import HOI4.Common -- everything

parseHOI4TechnologiesPath :: (IsGameData (GameData g), IsGameState (GameState g), Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap FilePath [HOI4Technology])
parseHOI4TechnologiesPath scripts = do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr -> setCurrentFile sourceFile $ mapM parseHOI4Technology $ concatMap (\case
                [pdx| technologies = @techs |] -> techs
                _ -> scr)
                scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing technology paths: " ++ T.unpack err
            return HM.empty
        Right techFilesOrErrors ->
            return $ HM.filter (not . null) $ flip HM.mapWithKey techFilesOrErrors $ \sourceFile etechs ->
                mapMaybe (\case
                    Left err -> do
                        traceM $ "Error parsing technology paths in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        Nothing
                    Right techs -> techs)
                    etechs

newHOI4Technology :: Text -> Text -> FilePath -> HOI4Technology
newHOI4Technology id locid = HOI4Technology id locid Nothing "" Nothing Nothing Nothing Nothing Nothing 0 0 False Nothing Nothing

-- | Parse a statement in an opinion modifiers file. Some statements aren't
-- modifiers; for those, and for any obvious errors, return Right Nothing.
parseHOI4Technology :: (IsGameState (GameState g), IsGameData (GameData g), MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe HOI4Technology))
parseHOI4Technology (StatementBare _) = throwError "bare statement at top level"
parseHOI4Technology [pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs id [] -> withCurrentFile $ \file -> do
            locid <- getGameL10n id
            mtech <- hoistErrors $ foldM technologyAddSection
                                        (Just (newHOI4Technology id locid file))
                                        parts
            case mtech of
                Left err -> return (Left err)
                Right Nothing -> return (Right Nothing)
                Right (Just tech) -> withCurrentFile $ \file ->
                    return (Right (Just tech ))
        _ -> throwError "unrecognized form for technology"
    _ -> return (Right Nothing)
parseHOI4Technology _ = withCurrentFile $ \file ->
    throwError ("unrecognised form for technology in " <> T.pack file)

-- | Interpret one section of an opinion modifier. If understood, add it to the
-- event data. If not understood, throw an exception.
technologyAddSection :: (IsGameState (GameState g), MonadError Text m) =>
    Maybe HOI4Technology -> GenericStatement -> PPT g m (Maybe HOI4Technology)
technologyAddSection Nothing _ = return Nothing
technologyAddSection mmod stmt
    = sequence (technologyAddSection' <$> mmod <*> pure stmt)
    where
        technologyAddSection' tech stmt@[pdx| dependencies = %rhs |]
            = return tech
        technologyAddSection' tech stmt@[pdx| research_cost = !rhs |]
            = return (tech { tech_cost = rhs })
        technologyAddSection' tech stmt@[pdx| start_year = !rhs |]
            = return (tech { tech_start_year = rhs })
        technologyAddSection' tech stmt@[pdx| desc = $rhs |]
            = return (tech { tech_desc = Just rhs })
        technologyAddSection' tech stmt@[pdx| folder = %_ |]
            = return tech
        technologyAddSection' tech stmt@[pdx| ai_will_do = %_ |]
            = return tech
        technologyAddSection' tech stmt@[pdx| categories = %_ |]
            = return tech
        technologyAddSection' tech stmt@[pdx| path =  %_ |]
            = return tech
        technologyAddSection' tech stmt@[pdx| enable_equipments = %rhs |] = case rhs of
            CompoundRhs [] -> return tech
            CompoundRhs scr -> let equips = mapMaybe getbareTech scr in
                return tech { tech_equipment = Just equips }
            _-> trace "bad enable_equipments in tech" return tech
        technologyAddSection' tech stmt@[pdx| enable_equipment_modules =  %_ |]
            = return tech
        technologyAddSection' tech stmt@[pdx| enable_subunits = %rhs |]= case rhs of
            CompoundRhs [] -> return tech
            CompoundRhs scr -> let units = mapMaybe getbareTech scr in
                return tech { tech_units = Just units }
            _-> trace "bad enable_equipments in tech" return tech
        technologyAddSection' tech stmt@[pdx| allow =  %_ |]
            = return tech
        technologyAddSection' tech stmt@[pdx| allow_branch =  %_ |]
            = return tech
        technologyAddSection' tech stmt@[pdx| ai_research_weights =  %_ |]
            = return tech
        technologyAddSection' tech stmt@[pdx| on_research_complete =  %_ |]
            = return tech
        technologyAddSection' tech stmt@[pdx| on_research_complete_limit =  %_ |]
            = return tech
        technologyAddSection' tech stmt@[pdx| doctrine = %rhs |] = case rhs of
            GenericRhs "yes" [] -> return tech { tech_doctrine = True }
            -- no is the default, so I don't think this is ever used
            GenericRhs "no" [] -> return tech { tech_doctrine = False }
            _ -> throwError "bad trigger"
        technologyAddSection' tech [pdx| $other = %_ |]
            = return tech -- trace ("unknown tech section: " ++ T.unpack other) $ 
        technologyAddSection' tech _
            = trace "unrecognised form for techr section" $ return tech

        getbareTech (StatementBare (GenericLhs e [])) = Just e
        getbareTech stmt = trace ("Unknown in getting tech array statement: " ++ show stmt) Nothing

writeHOI4Technologies :: (HOI4Info g, MonadIO m) => PPT g m ()
writeHOI4Technologies = do
    pathTech <- getTechnologies
    let pathedTechnologies :: [Feature [HOI4Technology]]
        pathedTechnologies = map (\techs -> Feature {
                                        featurePath = Just $ tech_filepath $ head techs
                                    ,   featureId = Just (T.pack $ takeBaseName $ tech_filepath $ head techs) <> Just ".txt"
                                    ,   theFeature = Right techs })
                              (HM.elems pathTech)
    writeFeatures "technologies"
                  pathedTechnologies
                  ppTechnologies




ppTechnologies :: forall g m. (HOI4Info g, Monad m) => [HOI4Technology] -> PPT g m Doc
ppTechnologies techs = do
    version <- gets (gameVersion . getSettings)
    techDoc <- mapM ppTechnology techs
    return . mconcat $
        [ "{{Version|", Doc.strictText version, "}}", PP.line
        , "{| class=\"wikitable\"", PP.line
        , "! style=\"width:146px;\" | Icon (generic)", PP.line
        , "! style=\"width:15em;\" | Technology", PP.line
        , "! style=\"width:1px;\" | Year", PP.line
        , "! style=\"width:67px;\" | Base cost", PP.line
        , "! style=\"width:13em;\" | Prerequisites", PP.line
        , "! Description", PP.line
        , "! style=\"width:526.5px;\" | Statistics", PP.line
        ] ++ techDoc ++
        [ "|}", PP.line
        ]



ppTechnology :: forall g m. (HOI4Info g, Monad m) => HOI4Technology -> PPT g m Doc
ppTechnology tech = setCurrentFile (tech_filepath tech) $ do
    let nfArg :: (HOI4Technology -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
        nfArg field fmt
            = maybe (return [])
                (\field_content -> do
                    content_pp'd <- fmt field_content
                    return
                        [content_pp'd
                        ,PP.line])
            (field tech)
        nfArgExtra :: Doc -> (HOI4Technology -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
        nfArgExtra extra field fmt
            = maybe (return [])
                (\field_content -> do
                    content_pp'd <- fmt field_content
                    return
                        ["{{",extra,"|",PP.line
                        ,content_pp'd
                        ,"}}"
                        ,PP.line])
            (field tech)
        nfArgClari :: Doc -> (HOI4Technology -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
        nfArgClari extra field fmt
            = maybe (return [])
                (\field_content -> do
                    content_pp'd <- fmt field_content
                    return
                        [extra, PP.line
                        ,content_pp'd
                        ,PP.line])
            (field tech)
        unitdesc = case tech_units tech of
            Just unit ->
                getGameL10nDefault "" (head unit <> "_desc")
            Nothing -> return ""

    if tech_doctrine tech then return . mconcat $ [] else do
        desc <- case tech_desc tech of
            Just spec -> getGameL10n spec
            Nothing -> do
                mdesc <- getGameL10nIfPresent (tech_id tech <> "_desc")
                case mdesc of
                    Just desc -> return desc
                    Nothing -> do
                        case tech_equipment tech of
                            Just equ -> do
                                mdesc <- getGameL10nIfPresent (head equ <> "_desc")
                                maybe unitdesc return mdesc
                            Nothing -> unitdesc

        gfx <- do
            let techgfx = do
                    mgfx <- getGameInterfaceIfPresent ("GFX_" <> tech_id tech <> "_medium")
                    return $ fromMaybe "" mgfx
            case tech_equipment tech of
                Just equ -> do
                    mgfx <- getGameInterfaceIfPresent ("GFX_" <> head equ <> "_medium")
                    maybe techgfx return mgfx
                Nothing -> techgfx
        techEffDoc <- ppTechEffects (tech_id tech) (fromMaybe [] (tech_equipment tech)) (fromMaybe [] (tech_units tech))
        return . mconcat $
            [ "|- ", PP.line
            , "| style=\"width:1px; text-align: center;\" | [[File:", Doc.strictText gfx, ".png|", Doc.strictText (tech_loc tech),"]]", PP.line
            , "! ", Doc.strictText (tech_loc tech), "<!-- ", Doc.strictText (tech_id tech), " -->", PP.line
            , "| ", Doc.strictText (T.pack $ show $ tech_start_year tech), PP.line
            , "| ", Doc.strictText (T.pack $ show $ round (tech_cost tech * 80)), " days",PP.line
            , "| ", PP.line
            , "| ", italic $ Doc.strictText desc,PP.line
            , "| <!-- research effects here -->", PP.line
            , techEffDoc,PP.line,PP.line]

ppTechEffects :: forall g m. (HOI4Info g, Monad m) => Text -> [Text] -> [Text] -> PPT g m Doc
ppTechEffects tech equip units = if all null [equip, units] then return . mconcat $ [] else do
    equipDoc <-(if null equip then return [] else concatMapM (equipthing tech) equip)
    unitDoc <- (if null units then return [] else concatMapM unitthing units)
    return . mconcat $
        ["{| class=\"wikitable mw-collapsible innercollapse mw-collapsed\" style=\"margin-right:2px\"", PP.line
        ,"! style=\"width:551px;\" colspan=\"2\" |", PP.line]++
        equipDoc++
        unitDoc++
        ["|}"]
    where
        equipthing :: forall g m. (HOI4Info g, Monad m) => Text -> Text -> PPT g m [Doc]
        equipthing equ tech = do
            gfx <- do
                techgfx <- do
                    mgfx <- getGameInterfaceIfPresent ("GFX_" <> tech <> "_medium")
                    return $ fromMaybe "" mgfx
                mequgfx <- getGameInterfaceIfPresent ("GFX_" <> equ <> "_medium")
                return $ fromMaybe techgfx mequgfx
            equname <- getGameL10n equ
            return
                ["|-", PP.line
                ,"| colspan=\"2\" style=\"border: none;\" | <!-- resource cost like steel -->", PP.line
                ,"|-", PP.line
                ,"| colspan=\"2\" style=\"text-align: center; border: none;\" | [[File:", Doc.strictText gfx,".png|", Doc.strictText equname,"]]", PP.line
                ,"|-", PP.line
                ,"| colspan=\"2\" style=\"text-align: center; border: none;\" |", PP.line
                ,"|-", PP.line
                ,"| colspan=\"2\" style=\"text-align: center; border: none;\" |", PP.line
                ,"|-", PP.line
                ,"| style=\"border: none; width: 50%; padding-right: 10px;\"| '''<!--statname here-->:''' <span style=\"float:right;\"><!-- number here --></span>", PP.line
                ,"| style=\"border: none; width: 50%; padding-left: 10px;\"| '''<!--statname here-->:''' <span style=\"float:right;\"><!-- number here --></span>", PP.line
                ,"|-", PP.line
                ,"| style=\"border: none; width: 50%; padding-right: 10px;\"| {{icon|production cost}} '''Production Cost:''' <span style=\"float:right;\"><!-- number here --></span>", PP.line
                ,"| style=\"border: none; width: 50%; padding-left: 10px;\"|", PP.line]
        unitthing :: forall g m. (HOI4Info g, Monad m) => Text -> PPT g m [Doc]
        unitthing unit = do
            unitname <- getGameL10n unit
            return
                ["|-", PP.line
                ,"| colspan=\"2\" style=\"text-align: center; font-size: 150%; border: none;\" | <br>Unlocks", PP.line
                ,"|-", PP.line
                ,"| colspan=\"2\" style=\"text-align: center; border: none;\" | [[File:<!--iconnamehere-->.png|link=<!--linknamehere-->]] ", Doc.strictText unitname , PP.line
                ,"|-", PP.line
                ,"| colspan=\"2\" style=\"text-align: center; border: none;\" |", PP.line
                ,"|-", PP.line
                ,"| style=\"border: none; width: 50%; padding-right: 10px;\"| '''<!--statname here-->:''' <span style=\"float:right;\"><!-- number here --></span>", PP.line
                ,"| style=\"border: none; width: 50%; padding-left: 10px;\"| '''<!--statname here-->:''' <span style=\"float:right;\"><!-- number here --></span>", PP.line]