{-|
Module      : EU4.Events
Description : Feature handler for Europa Universalis IV events
-}
module EU4.Events (
        parseEU4Events
    ,   writeEU4Events
    ,   findTriggeredEventsInEvents
    ,   findTriggeredEventsInDecisions
    ,   findTriggeredEventsInOnActions
    ,   findTriggeredEventsInDisasters
    ,   findTriggeredEventsInGenericScript
    ,   findTriggeredEventsInMissions
    ,   findTriggeredEventsInProvinceTriggeredModifiers
    ,   findTriggeredEventsInGovernmentMechanics
    ,   findTriggeredEventsInImperialIncidents
    ) where

import Debug.Trace (trace, traceM)

import Control.Arrow ((&&&))
import Control.Monad (liftM, forM, foldM, when, (<=<))
import Control.Monad.Except (MonadError (..))
import Control.Monad.State (MonadState (..), gets)
import Control.Monad.Trans (MonadIO (..))

import Data.Array ((!))
import Data.ByteString (ByteString)
import Data.List (intersperse, foldl', sortOn)
import Data.Maybe (isJust, isNothing, fromMaybe, fromJust, catMaybes)
import Data.Monoid ((<>))

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL

import Text.PrettyPrint.Leijen.Text (Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP

import Text.Regex.TDFA (Regex)
import qualified Text.Regex.TDFA as RE

import Abstract -- everything
import qualified Doc
import EU4.Common -- everything
import FileIO (Feature (..), writeFeatures)
import Messages (imsg2doc)
import MessageTools (iquotes)
import QQ (pdx)
import SettingsTypes ( PPT, Settings (..), Game (..)
                     , IsGame (..), IsGameData (..), IsGameState (..)
                     , getGameL10n, getGameL10nIfPresent
                     , setCurrentFile, withCurrentFile
                     , hoistErrors, hoistExceptions)

-- | Empty event value. Starts off Nothing/empty everywhere.
newEU4Event :: EU4Scope -> FilePath -> EU4Event
newEU4Event escope path = EU4Event Nothing Nothing [] escope Nothing Nothing Nothing Nothing False False Nothing Nothing path
-- | Empty event option vaule. Starts off Nothing everywhere.
newEU4Option :: EU4Option
newEU4Option = EU4Option Nothing Nothing Nothing Nothing

-- | Take the event scripts from game data and parse them into event data
-- structures.
parseEU4Events :: (EU4Info g, Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text EU4Event)
parseEU4Events scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr ->
                setCurrentFile sourceFile $ mapM parseEU4Event scr)
            scripts
    case tryParse of
        Left err -> do
            traceM $ "Completely failed parsing events: " ++ T.unpack err
            return HM.empty
        Right eventsFilesOrErrors ->
            flip HM.traverseWithKey eventsFilesOrErrors $ \sourceFile eevts -> do
                fmap (mkEvtMap . catMaybes) . forM eevts $ \case
                    Left err -> do
                        traceM $ "Error parsing events in " ++ sourceFile
                                 ++ ": " ++ T.unpack err
                        return Nothing
                    Right mevt -> return mevt
                where mkEvtMap :: [EU4Event] -> HashMap Text EU4Event
                      mkEvtMap = HM.fromList . map (fromJust . eu4evt_id &&& id)
                        -- Events returned from parseEvent are guaranteed to have an id.

-- | Present the parsed events as wiki text and write them to the appropriate
-- files.
writeEU4Events :: (EU4Info g, MonadIO m) => PPT g m ()
writeEU4Events = do
    events <- getEvents
    let pathedEvents :: [Feature EU4Event]
        pathedEvents = map (\evt -> Feature {
                                    featurePath = Just (eu4evt_path evt)
                                ,   featureId = eu4evt_id evt
                                ,   theFeature = Right evt })
                            (HM.elems events)
    writeFeatures "events"
                  pathedEvents
                  (\e -> scope (eu4evt_scope e) $ pp_event e)

-- | Parse a statement in an events file. Some statements aren't events; for
-- those, and for any obvious errors, return Right Nothing.
parseEU4Event :: (EU4Info g, MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe EU4Event))
parseEU4Event (StatementBare lhs) = withCurrentFile $ \f ->
        throwError $ T.pack (f ++ ": bare statement at top level: " ++ (show lhs))
parseEU4Event stmt@[pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs etype _ ->
            let mescope = case etype of
                    "country_event" -> Just EU4Country
                    "province_event" -> Just EU4Province
                    _ -> Nothing
            in case mescope of
                Nothing -> throwError $ "unrecognized event type " <> etype
                Just escope -> withCurrentFile $ \file -> do
                    mevt <- hoistErrors (foldM eventAddSection (Just (newEU4Event escope file)) parts)
                    case mevt of
                        Left err -> return (Left err)
                        Right Nothing -> return (Right Nothing)
                        Right (Just evt) ->
                            if isJust (eu4evt_id evt)
                            then return (Right (Just evt))
                            else return (Left $ "error parsing events in " <> T.pack file
                                         <> ": missing event id")

    _ -> return (Right Nothing)
parseEU4Event _ = throwError "operator other than ="

-- | Intermediate structure for interpreting event description blocks.
data EvtDescI = EvtDescI {
        edi_text :: Maybe Text
    ,   edi_trigger :: Maybe GenericScript
    }
-- | Interpret the @desc@ section of an event. This can be either a
-- localization key or a conditional description block. (TODO: document the
-- format here)
evtDesc :: MonadError Text m => Maybe Text -> GenericScript -> m EU4EvtDesc
evtDesc meid scr = case foldl' evtDesc' (EvtDescI Nothing Nothing) scr of
        EvtDescI (Just t) Nothing -- desc = { text = foo }
            -> return $ EU4EvtDescSimple t
        EvtDescI Nothing (Just trig) -- desc = { trigger = { .. } } (invalid)
            -> return $ EU4EvtDescCompound scr
        EvtDescI (Just t) (Just trig) -- desc = { trigger = { .. } text = foo }
                                      -- e.g. pirate.1
            -> return $ EU4EvtDescConditional trig t
        EvtDescI Nothing Nothing -- desc = { switch { .. = { text = foo } } }
                                 -- e.g. action.39
            -> throwError $ "bad desc: no trigger nor text" <> case meid of
                Just eid -> " in event " <> eid
                Nothing -> ""
    where
        evtDesc' ed [pdx| trigger = @trig |] = ed { edi_trigger = Just trig }
        evtDesc' ed [pdx| text = ?txt |] = ed { edi_text = Just txt }
        evtDesc' ed [pdx| desc = ?txt |] = ed { edi_text = Just txt }
        evtDesc' ed [pdx| show_sound = %_ |] = ed
        evtDesc' ed [pdx| $label = %_ |]
            = error ("unrecognized desc section " ++ T.unpack label
                     ++ " in " ++ maybe "(unknown)" T.unpack meid)
        evtDesc' ed stmt
            = error ("unrecognized desc section in " ++ maybe "(unknown)" T.unpack meid
                    ++ ": " ++ show stmt)

-- | Interpret one section of an event. If understood, add it to the event
-- data. If not understood, throw an exception.
eventAddSection :: (EU4Info g, MonadError Text m) =>
    Maybe EU4Event -> GenericStatement -> PPT g m (Maybe EU4Event)
eventAddSection Nothing _ = return Nothing
eventAddSection mevt stmt = sequence (eventAddSection' <$> mevt <*> pure stmt) where
    eventAddSection' evt stmt@[pdx| id = %rhs |]
        = case (textRhs rhs, floatRhs rhs) of
            (Just tid, _) -> return evt { eu4evt_id = Just tid }
            (_, Just nid) -> return evt { eu4evt_id = Just (T.pack $ show (nid::Int)) }
            _ -> withCurrentFile $ \file ->
                throwError $ "bad id in " <> T.pack file <> ": " <> T.pack (show rhs)
    eventAddSection' evt stmt@[pdx| title = %rhs |] = case textRhs rhs of
        Just title -> return evt { eu4evt_title = Just title }
        _ -> withCurrentFile $ \file ->
            throwError $ "bad title in " <> T.pack file
    eventAddSection' evt stmt@[pdx| desc = %rhs |] =
        let olddescs = eu4evt_desc evt in case rhs of
            (textRhs -> Just desc) -> return evt { eu4evt_desc = olddescs ++ [EU4EvtDescSimple desc] }
            CompoundRhs scr -> do
                let meid = eu4evt_id evt
                desc <- evtDesc meid scr
                return evt { eu4evt_desc = olddescs ++ [desc] }
            _ -> throwError $ "bad desc" <> case eu4evt_id evt of
                    Just eid -> " in event " <> eid
                    Nothing -> ""
    eventAddSection' evt stmt@[pdx| picture = %_ |] = return evt
--  picture has conditions like desc. Ignore for now since we don't actually use it
--    eventAddSection' evt stmt@[pdx| picture = %rhs |] = case textRhs rhs of
--        Just pic -> return evt { eu4evt_picture = Just pic }
--        _ -> throwError "bad picture"
    eventAddSection' evt stmt@[pdx| goto = %rhs |] = return evt
    eventAddSection' evt stmt@[pdx| trigger = %rhs |] = case rhs of
        CompoundRhs trigger_script -> case trigger_script of
            [] -> return evt -- empty, treat as if it wasn't there
            _ -> return evt { eu4evt_trigger = Just trigger_script }
        _ -> throwError "bad event trigger"
    eventAddSection' evt stmt@[pdx| is_triggered_only = %rhs |] = case rhs of
        GenericRhs "yes" [] -> return evt { eu4evt_is_triggered_only = Just True }
        -- no is the default, so I don't think this is ever used
        GenericRhs "no" [] -> return evt { eu4evt_is_triggered_only = Just False }
        _ -> throwError "bad trigger"
    eventAddSection' evt stmt@[pdx| mean_time_to_happen = %rhs |] = case rhs of
        CompoundRhs mtth -> return evt { eu4evt_mean_time_to_happen = Just mtth }
        _ -> throwError "bad MTTH"
    eventAddSection' evt stmt@[pdx| immediate = %rhs |] = case rhs of
        CompoundRhs immediate -> return evt { eu4evt_immediate = Just immediate }
        _ -> throwError "bad immediate section"
    eventAddSection' evt stmt@[pdx| option = %rhs |] =  case rhs of
        CompoundRhs option -> do
            newEU4Options <- addEU4Option (eu4evt_options evt) option
            return evt { eu4evt_options = newEU4Options }
        _ -> throwError "bad option"
    eventAddSection' evt stmt@[pdx| fire_only_once = %rhs |]
        | GenericRhs "yes" [] <- rhs = return evt { eu4evt_fire_only_once = True }
        | GenericRhs "no"  [] <- rhs = return evt { eu4evt_fire_only_once = False }
    eventAddSection' evt stmt@[pdx| major = %_ |] = return evt -- do nothing
    eventAddSection' evt stmt@[pdx| major_trigger = %_ |] = return evt -- do nothing
    eventAddSection' evt stmt@[pdx| hidden = %rhs |]
        | GenericRhs "yes" [] <- rhs = return evt { eu4evt_hide_window = True }
        | GenericRhs "no"  [] <- rhs = return evt { eu4evt_hide_window = False }
    eventAddSection' evt stmt@[pdx| is_mtth_scaled_to_size = %_ |] = return evt -- do nothing (XXX)
    eventAddSection' evt stmt@[pdx| after = @scr |] = return evt { eu4evt_after = Just scr }
    eventAddSection' evt stmt@[pdx| $label = %_ |] =
        withCurrentFile $ \file ->
            throwError $ "unrecognized event section in " <> T.pack file <> ": " <> label
    eventAddSection' evt stmt =
        withCurrentFile $ \file ->
            throwError $ "unrecognized event section in " <> T.pack file <> ": " <> T.pack (show stmt)

-- | Interpret an option block and append it to the list of options.
addEU4Option :: (IsGame g, Monad m) => Maybe [EU4Option] -> GenericScript -> PPT g m (Maybe [EU4Option])
addEU4Option Nothing opt = addEU4Option (Just []) opt
addEU4Option (Just opts) opt = do
    optn <- foldM optionAddStatement newEU4Option opt
    return $ Just (opts ++ [optn])

-- | Interpret one section of an option block and add it to the option data.
optionAddStatement :: (IsGame g, Monad m) => EU4Option -> GenericStatement -> PPT g m EU4Option
optionAddStatement opt stmt@[pdx| name = ?name |]
    = return $ opt { eu4opt_name = Just name }
optionAddStatement opt stmt@[pdx| ai_chance = @ai_chance |]
    = return $ opt { eu4opt_ai_chance = Just ai_chance }
optionAddStatement opt stmt@[pdx| trigger = @trigger_script |]
    = return $ opt { eu4opt_trigger = Just trigger_script }
optionAddStatement opt stmt = do
    -- Not a GenericLhs - presumably an effect.
    effects_pp'd <- setIsInEffect True (optionAddEffect (eu4opt_effects opt) stmt)
    return $ opt { eu4opt_effects = effects_pp'd }

-- | Append an effect to the effects of an option.
optionAddEffect :: Monad m => Maybe GenericScript -> GenericStatement -> PPT g m (Maybe GenericScript)
optionAddEffect Nothing stmt = optionAddEffect (Just []) stmt
optionAddEffect (Just effs) stmt = return $ Just (effs ++ [stmt])

iquotes't = Doc.doc2text . iquotes

-- | Present an event's description block.
ppDescs :: (EU4Info g, Monad m) => Bool {- ^ Is this a hidden event? -}
                                -> [EU4EvtDesc] -> PPT g m Doc
ppDescs True _ = return "| cond_event_text = (This event is hidden and has no description.)"
ppDescs _ [] = return "| event_text = (No description)"
ppDescs _ [EU4EvtDescSimple key] = ("| event_text = " <>) . Doc.strictText . Doc.nl2br <$> getGameL10n key
ppDescs _ descs = (("| cond_event_text = yes" <> PP.line <> "| event_text = ") <>) . PP.vsep <$> mapM ppDesc descs where
    ppDesc (EU4EvtDescSimple key) = ("Otherwise:<br>:" <>) <$> fmtDesc key
    ppDesc (EU4EvtDescConditional scr key) = mconcat <$> sequenceA
        [pure "The following description is used if:", pure PP.line
        ,imsg2doc =<< ppMany scr, pure PP.line
        ,pure ":", fmtDesc key
        ]
    ppDesc (EU4EvtDescCompound scr) =
        imsg2doc =<< ppMany scr
    fmtDesc key = flip liftM (getGameL10nIfPresent key) $ \case
        Nothing -> Doc.strictText key
        Just txt -> "''" <> Doc.strictText (Doc.nl2br txt) <> "''"

ppEventLoc :: (EU4Info g, Monad m) => Text -> PPT g m Text
ppEventLoc id = do
    loc <- getEventTitle id -- Note: Hidden events often have empty titles, see e.g. fetishist_flavor.400
    case loc of
        (Just t) | T.length (T.strip t) /= 0 -> return $ "<!-- " <> id <> " -->" <> iquotes't t -- TODO: Add link if possible
        _ -> return $ "<tt>" <> id <> "</tt>"

formatWeight :: EU4EventWeight -> Text
formatWeight Nothing = ""
formatWeight (Just (n, d)) = T.pack (" (Base weight: " ++ show n ++ "/" ++ show d ++ ")")

ppEventSource :: (EU4Info g, Monad m) => EU4EventSource -> PPT g m Doc
ppEventSource (EU4EvtSrcOption eventId optionId) = do
    eventLoc <- ppEventLoc eventId
    optLoc <- getGameL10n optionId
    return $ Doc.strictText $ mconcat [ "The event "
        , eventLoc
        , " option "
        , iquotes't optLoc
        ]
ppEventSource (EU4EvtSrcAfter eventId) = do
    eventLoc <- ppEventLoc eventId
    return $ Doc.strictText $ mconcat [ "After choosing an option an option in the "
        , eventLoc
        , " event"
        ]
ppEventSource (EU4EvtSrcImmediate eventId) = do
    eventLoc <- ppEventLoc eventId
    return $ Doc.strictText $ mconcat [ "As an immediate effect of the "
        , eventLoc
        , " event"
        ]
ppEventSource (EU4EvtSrcDecision id loc) = do
    return $ Doc.strictText $ mconcat ["Taking the decision "
        , "<!-- "
        , id
        , " -->"
        , iquotes't loc
        ]
ppEventSource (EU4EvtSrcOnAction act weight) = do
    return $ Doc.strictText $ act <> formatWeight weight
ppEventSource (EU4EvtSrcDisaster id trig weight) = do
    idLoc <- getGameL10n id
    return $ Doc.strictText $ mconcat [trig
        , " of the <!-- "
        , id
        , " -->"
        , iquotes't idLoc
        , " disaster"
        , formatWeight weight
        ]
ppEventSource (EU4EvtSrcGeneric id trig) = do
    idLoc <- getGameL10n id
    locWithTitle <- getGameL10nIfPresent (id <> "_title")
    return $ Doc.strictText $ mconcat [trig
        , " <!-- "
        , id
        , " -->"
        , iquotes't (fromMaybe idLoc locWithTitle)
        ]
ppEventSource (EU4EvtSrcMission missionId) = do
    title <- getGameL10n (missionId <> "_title")
    return $ Doc.strictText $ mconcat ["Completing the <!-- "
        , missionId
        , " -->"
        , iquotes't title
        , " mission"
        ]
ppEventSource (EU4EvtSrcGovernmentMechanic id sectionId trig) = do
    idLoc <- getGameL10n ("ability_" <> id)
    sectionLoc <- getGameL10n sectionId
    return $ Doc.strictText $ mconcat [trig
        , " <!-- "
        , sectionId
        , " -->"
        , iquotes't sectionLoc
        , " in the government mechanic <!-- "
        , id
        , " -->"
        , iquotes't idLoc
        ]

ppTriggeredBy :: (EU4Info g, Monad m) => Text -> PPT g m Doc
ppTriggeredBy eventId = do
    eventTriggers <- getEventTriggers
    let mtriggers = HM.lookup eventId eventTriggers
    case mtriggers of
        Just triggers -> do
            ts <- mapM ppEventSource triggers
            -- FIXME: This is a bit ugly, but we only want a list if there's more than one trigger
            let ts' = if length ts < 2 then
                    ts
                else
                    -- to give consistent results, the triggers are sorted while ignoring HTML comments in the sort(because they often contain an event ID)
                    map (\d -> Doc.strictText $ "* " <> (Doc.doc2text d)) (sortOn removeComments ts)
            return $ mconcat $ [PP.line] ++ (intersperse PP.line ts')
        _ -> return $ Doc.strictText "(please describe trigger here)"
    where
        commentRE :: Regex
        commentRE = RE.makeRegex ("<!--[^>]*-->"::ByteString)
        removeComments :: Doc -> Text
        removeComments s = case RE.matchOnceText commentRE (Doc.doc2text s) of
            Just (pre, matcharr, post) -> mconcat
                [pre, post, fst (matcharr ! 0)]
            Nothing -> Doc.doc2text s

-- | Pretty-print an event. If some essential parts are missing from the data,
-- throw an exception.
pp_event :: forall g m. (EU4Info g, MonadError Text m) =>
    EU4Event -> PPT g m Doc
pp_event evt = case (eu4evt_id evt
                    ,eu4evt_title evt
                    ,eu4evt_options evt) of
    (Just eid, Just title, Just options) -> setCurrentFile (eu4evt_path evt) $ do
        -- Valid event
        version <- gets (gameVersion . getSettings)
        (conditional, options_pp'd) <- pp_options (eu4evt_hide_window evt) eid options
        titleLoc <- getGameL10n title
        descLoc <- ppDescs (eu4evt_hide_window evt) (eu4evt_desc evt)
        after_pp'd <- setIsInEffect True (sequence ((imsg2doc <=< ppMany) <$> eu4evt_after evt))
        let evtArg :: Text -> (EU4Event -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
            evtArg fieldname field fmt
                = maybe (return [])
                    (\field_content -> do
                        content_pp'd <- fmt field_content
                        return
                            ["| ", Doc.strictText fieldname, " = "
                            ,PP.line
                            ,content_pp'd
                            ,PP.line])
                    (field evt)
            isTriggeredOnly = fromMaybe False $ eu4evt_is_triggered_only evt
            isFireOnlyOnce = eu4evt_fire_only_once evt
            evtId = Doc.strictText eid
        trigger_pp'd <- evtArg "trigger" eu4evt_trigger ppScript
        mmtth_pp'd <- mapM (pp_mtth isTriggeredOnly) (eu4evt_mean_time_to_happen evt)
        immediate_pp'd <- setIsInEffect True (evtArg "immediate" eu4evt_immediate ppScript)
        triggered_pp <- ppTriggeredBy eid
        -- Keep track of incomplete events
        when (not isTriggeredOnly && isNothing mmtth_pp'd) $
            -- TODO: use logging instead of trace
            traceM ("warning: is_triggered_only and mean_time_to_happen missing for event id " ++ T.unpack eid)
        return . mconcat $
            ["<section begin=", evtId, "/>", PP.line
            ,"{{Event", PP.line
            ,"| version = ", Doc.strictText version, PP.line
            ,"| event_id = ", evtId, PP.line
            ,"| event_name = ", Doc.strictText titleLoc, PP.line
            ,descLoc, PP.line
            ] ++
            ( if isFireOnlyOnce then
                ["| fire_only_once = yes", PP.line]
            else []) ++
            -- For triggered only events, mean_time_to_happen is not
            -- really mtth but instead describes weight modifiers, for
            -- scripts that trigger them with a probability based on a
            -- weight (e.g. on_bi_yearly_pulse).
            (if isTriggeredOnly then
                ["| triggered only = ", triggered_pp, PP.line
                ]
                ++ maybe [] (:[PP.line]) mmtth_pp'd
            else []) ++
            trigger_pp'd ++
            -- mean_time_to_happen is only really mtth if it's *not*
            -- triggered only.
            (if isTriggeredOnly then [] else case mmtth_pp'd of
                Nothing ->
                    ["| triggered_only =", PP.line
                    ,"* Unknown (Missing MTTH and is_triggered_only)", PP.line]
                Just mtth_pp'd ->
                    ["| mtth = ", PP.line
                    ,mtth_pp'd, PP.line]) ++
            immediate_pp'd ++
            (if conditional then ["| option conditions = yes", PP.line] else []) ++
            -- option_conditions = no (not implemented yet)
            (maybe [] (\app -> ["| after =", PP.line, app, PP.line]) after_pp'd) ++
            ["| options = ", options_pp'd, PP.line
            -- ,"| collapse = yes", PP.line
            ,"}}", PP.line
            ,"<section end=", evtId, "/>", PP.line
            ]

    (Nothing, _, _) -> throwError "eu4evt_id missing"
    (Just eid, Nothing, _) ->
        throwError ("title missing for event id " <> eid)
    (Just eid, _, Nothing) ->
        throwError ("options missing for event id " <> eid)

-- | Present the options of an event.
pp_options :: (EU4Info g, MonadError Text m) =>
    Bool -> Text -> [EU4Option] -> PPT g m (Bool, Doc)
pp_options hidden evtid opts = do
    let triggered = any (isJust . eu4opt_trigger) opts
    options_pp'd <- mapM (pp_option evtid hidden triggered) opts
    return (triggered, mconcat . (PP.line:) . intersperse PP.line $ options_pp'd)

-- | Present a single event option.
pp_option :: (EU4Info g, MonadError Text m) =>
    Text -> Bool -> Bool -> EU4Option -> PPT g m Doc
pp_option evtid hidden triggered opt = do
    optNameLoc <- getGameL10n `mapM` eu4opt_name opt
    case optNameLoc of
        -- NB: some options have no effect, e.g. start of Peasants' War.
        Just name_loc -> ok name_loc
        Nothing -> if hidden
            then ok "(Dummy option for hidden event)"
            else throwError $ "some required option sections missing in " <> evtid <> " - dumping: " <> T.pack (show opt)
    where
        ok name_loc = let mtrigger = eu4opt_trigger opt in do
            effects_pp'd <- setIsInEffect True (ppScript (fromMaybe [] (eu4opt_effects opt)))
            mtrigger_pp'd <- sequence (ppScript <$> mtrigger)
            return . mconcat $
                ["{{Option", PP.line
                ,"| option_text = ", Doc.strictText name_loc, PP.line
                ,"| effect =", PP.line, effects_pp'd, PP.line]
                ++ (if triggered then
                        maybe
                            ["| trigger = always", PP.line] -- no trigger
                        (\trigger_pp'd ->
                            ["| trigger = ", PP.line -- trigger
                            ,trigger_pp'd, PP.line]
                        ) mtrigger_pp'd
                    else [])
                ++
                -- 1 = no
                ["}}"
                ]

findInStmt :: GenericStatement -> [(EU4EventWeight, Text)]
findInStmt stmt@[pdx| $lhs = @scr |] | lhs == "country_event" || lhs == "province_event" || lhs == "country_event_with_insight" = case getId scr of
    Just triggeredId -> [(Nothing, triggeredId)]
    _ -> (trace $ "Unrecognized event trigger: " ++ show stmt) $ []
    where
        getId :: [GenericStatement] -> Maybe Text
        getId [] = Nothing
        getId (stmt@[pdx| id = ?!id |] : _) = case id of
            Just (Left n) -> Just $ T.pack (show (n :: Int))
            Just (Right t) -> Just t
            _ -> (trace $ "Invalid event id statement: " ++ show stmt) $ Nothing
        getId (_ : ss) = getId ss
findInStmt [pdx| events = @scr |]  = catMaybes $ map extractEvent scr
    where
        extractEvent :: GenericStatement -> Maybe (EU4EventWeight, Text)
        extractEvent (StatementBare (GenericLhs e [])) = Just (Nothing, e)
        extractEvent (StatementBare (IntLhs e)) = Just (Nothing, T.pack (show e))
        extractEvent stmt = (trace $ "Unknown in events statement: " ++ show stmt) $ Nothing
findInStmt [pdx| random_events = @scr |] =
    let evts = catMaybes $ map extractRandomEvent scr
        total = sum $ map fst evts
    in map (\t -> (Just (fst t, total), snd t)) evts
    where
        extractRandomEvent :: GenericStatement -> Maybe (Integer, Text)
        extractRandomEvent stmt@[pdx| !weight = ?!id |] = case id of
            Just (Left n) -> Just (fromIntegral weight, T.pack (show (n :: Int)))
            Just (Right t) -> Just (fromIntegral weight, t)
            _ -> (trace $ "Invalid event id in random_events: " ++ show stmt) $ Nothing
        extractRandomEvent stmt = (trace $ "Unknown in random_events statement: " ++ show stmt) $ Nothing
findInStmt [pdx| %_ = @scr |] = findInStmts scr
findInStmt _ = []

findInStmts :: [GenericStatement] -> [(EU4EventWeight, Text)]
findInStmts stmts = concatMap findInStmt stmts

addEventSource :: (EU4EventWeight -> EU4EventSource) -> [(EU4EventWeight, Text)] -> [(Text, EU4EventSource)]
addEventSource es l = map (\t -> (snd t, es (fst t))) l

findInOptions :: Text -> [EU4Option] -> [(Text, EU4EventSource)]
findInOptions eventId opts = concatMap (\o -> case eu4opt_name o of
    Just optName -> addEventSource (const (EU4EvtSrcOption eventId optName)) (maybe [] (concatMap findInStmt) (eu4opt_effects o))
    _ -> []
    ) opts

addEventTriggers :: EU4EventTriggers -> [(Text, EU4EventSource)] -> EU4EventTriggers
addEventTriggers hm l = foldl' ins hm l
    where
        ins :: EU4EventTriggers -> (Text, EU4EventSource) -> EU4EventTriggers
        ins hm (k, v) = HM.alter (\orig -> case orig of
            Just l -> Just $ l ++ [v]
            Nothing -> Just [v]) k hm

findTriggeredEventsInEvents :: EU4EventTriggers -> [EU4Event] -> EU4EventTriggers
findTriggeredEventsInEvents hm evts = addEventTriggers hm (concatMap findInEvent evts)
    where
        findInEvent :: EU4Event -> [(Text, EU4EventSource)]
        findInEvent evt@EU4Event{eu4evt_id = Just eventId} =
            (case eu4evt_options evt of
                Just opts -> findInOptions eventId opts
                _ -> []) ++
            (addEventSource (const (EU4EvtSrcImmediate eventId)) (maybe [] findInStmts (eu4evt_immediate evt))) ++
            (addEventSource (const (EU4EvtSrcAfter eventId)) (maybe [] findInStmts (eu4evt_after evt)))
        findInEvent _ = []

findTriggeredEventsInDecisions :: EU4EventTriggers -> [EU4Decision] -> EU4EventTriggers
findTriggeredEventsInDecisions hm ds = addEventTriggers hm (concatMap findInDecision ds)
    where
        findInDecision :: EU4Decision -> [(Text, EU4EventSource)]
        findInDecision d = addEventSource (const (EU4EvtSrcDecision (dec_name d) (dec_name_loc d))) (findInStmts (dec_effect d))

findTriggeredEventsInOnActions :: EU4EventTriggers -> [GenericStatement] -> EU4EventTriggers
findTriggeredEventsInOnActions hm scr = foldl' findInAction hm scr
    where
        findInAction :: EU4EventTriggers -> GenericStatement -> EU4EventTriggers
        findInAction hm stmt@[pdx| $lhs = @scr |] = addEventTriggers hm (addEventSource (EU4EvtSrcOnAction (actionName lhs)) (findInStmts scr))
        findInAction hm stmt = (trace $ "Unknown on_actions statement: " ++ show stmt) $ hm

        actionName :: Text -> Text
        actionName n = HM.lookupDefault ("<pre>" <> n <> "</pre>") n actionNameTable


        -- TODO: This should in principle be localizable at some point
        actionNameTable :: HashMap Text Text
        actionNameTable = HM.fromList
            [("on_annexed", "When a nation is annexed")
            --,("on_battle_lost_country", "")
            ,("on_battle_lost_province", "<!-- on_battle_lost_province -->Losing a battle to ''From'' in the province") -- # root = location, from = winner country
            --,("on_battle_lost_unit", "")
            --,("on_battle_won_province", "")
            --,("on_become_free_city", "")
            ,("on_bi_yearly_pulse", "The [[List_of_event_lists#2_year_pulse|bi-yearly pulse I]]")
            ,("on_bi_yearly_pulse_2", "The [[List_of_event_lists#2_year_pulse|bi-yearly pulse II]]")
            ,("on_bi_yearly_pulse_3", "The [[List_of_event_lists#2_year_pulse|bi-yearly pulse III]]")
            ,("on_bi_yearly_pulse_4", "The [[List_of_event_lists#2_year_pulse|bi-yearly pulse IV]]")
            ,("on_bi_yearly_pulse_5", "The [[List_of_event_lists#2_year_pulse|bi-yearly pulse V]]")
            --,("on_buy_religious_reform", "")
            --,("on_change_hre_religion", "")
            --,("on_circumnavigation", "")
            --,("on_colonial_liberation", "")
            --,("on_colonial_pulse", "")
            --,("on_colonial_reintegration", "")
            ,("on_conquistador_empty", "<!-- on_conquistador_empty -->{{icon|conquistador}} Conquistador is entering a uncolonized province with ''\"Hunt for the Seven Cities of Gold\"'' mission")
            ,("on_conquistador_native", "<!-- on_conquistador_native -->{{icon|conquistador}} Conquistador is entering a province owned by natives with ''\"Hunt for the Seven Cities of Gold\"'' mission")
            --,("on_death_election", "")
            --,("on_death_foreign_slave_ruler", "")
            --,("on_death_has_harem", "")
            --,("on_dependency_gained", "")
            ,("on_diplomatic_annex", "<!-- on_diplomatic_annex -->Diplomatically annexing a country")
            --,("on_dismantle_revolution", "")

            -- Note: Should probably be "An estate *becoming* more influential", but that doesn't seem to be the behavior in 1.31.3
            ,("on_estate_led_regency_surpassed", "<!-- on_estate_led_regency_surpassed -->An estate being more influential than the one leading the regency")
            --,("on_explore_coast", "")
            ,("on_extended_regency", "<!-- on_extended_regency -->Extending a regency")
            --,("on_fetishist_cult_change", "")
            ,("on_five_year_pulse", "The [[list_of_event_lists#5_year_pulse|five year pulse I]]")
            ,("on_five_year_pulse_2", "The [[list_of_event_lists#5_year_pulse|five year pulse II]]")
            ,("on_five_year_pulse_3", "The [[list_of_event_lists#5_year_pulse|five year pulse III]]")
            ,("on_five_year_pulse_4", "The [[list_of_event_lists#5_year_pulse|five year pulse IV]]")
            --,("on_flagship_captured", "")
            --,("on_flagship_destroyed", "")
            ,("on_four_year_pulse", "The [[List_of_event_lists#4_year_pulse|4 year pulse]]")
            ,("on_four_year_pulse_2", "The [[List_of_event_lists#4_year_pulse|4 year pulse II]]")
            ,("on_four_year_pulse_3", "The [[List_of_event_lists#4_year_pulse|4 year pulse III]]")
            ,("on_four_year_pulse_4", "The [[List_of_event_lists#4_year_pulse|4 year pulse IV]]")
            --,("on_harmonized_buddhism", "")
            --,("on_harmonized_christian", "")
            --,("on_harmonized_dharmic", "")
            --,("on_harmonized_jewish_group", "")
            --,("on_harmonized_mahayana", "")
            --,("on_harmonized_muslim", "")
            --,("on_harmonized_pagan", "")
            --,("on_harmonized_shinto", "")
            --,("on_harmonized_vajrayana", "")
            --,("on_harmonized_zoroastrian_group", "")
            ,("on_heir_death", "<!-- on_heir_death -->Heir dying")
            ,("on_heir_disinherited", "<!-- on_heir_disinherited -->Heir disinherited")
            ,("on_heir_needed_theocracy", "<!-- on_heir_needed_theocracy -->A theocracy needing an heir")
            ,("on_hre_dismantled", "<!-- on_hre_dismantled -->When dismantling the HRE")
            --,("on_hre_non_defense", "")
            --,("on_hre_religion_white_peace", "")
            ,("on_integrate", "Diplomatically integrating a junior partner")
            --,("on_lock_hre_religion", "")
            ,("on_main_war_won", "<!-- on_main_war_won -->Winning a war against ''From''") -- root = winning country, from = loser country
            ,("on_main_war_lost", "<!-- on_main_war_lost -->Losing a war against ''From''") -- root = winning country, from = loser country
            ,("on_mandate_of_heaven_gained", "<!-- on_mandate_of_heaven_gained -->Our country becoming the [[Emperor of China]] instead of ''From''")
            ,("on_monarch_death", "<!-- on_monarch_death-->Curent ruler dying")
            ,("on_new_age", "<!-- on_new_age -->When a new age starts")
            ,("on_new_consort", "<!-- on_new_consort -->Getting a new consort")
            ,("on_new_monarch", "<!-- on_new_monarch -->Getting a new ruler")
            --,("on_new_term_election", "")
            ,("on_overextension_pulse", "The overextension pulse")
            ,("on_peace_actor", "<!-- on_peace_actor -->Sending a peace offer")
            ,("on_peace_recipient", "<!-- on_peace_recipient -->Receiving a peace offer")
            ,("on_province_owner_change", "<!-- on_province_owner_change -->The owner of a province changes")
            --,("on_regent", "")
            ,("on_religion_change", "<!-- on_religion_change -->Changing religion")
            --,("on_remove_free_city", "")
            --,("on_replace_governor", "")
            --,("on_revoke_estate_land", "")
            ,("on_siege_lost_country", "<!-- on_siege_lost_country -->Our country lost a siege in ''From''") -- root = losing country, from = location
            --,("on_siege_lost_province", "")
            ,("on_siege_won_country", "<!-- on_siege_won_country -->Our country winning a siege in ''From''") -- root = winning country, from = location
            --,("on_siege_won_province", "")
            ,("on_startup", "<!-- on_startup -->Starting the game")
            --,("on_successive_emperor", "")
            ,("on_thri_yearly_pulse", "The [[list_of_event_lists#3_year_pulse|three year pulse I]]")
            ,("on_thri_yearly_pulse_2", "The [[list_of_event_lists#3_year_pulse|three year pulse II]]")
            ,("on_thri_yearly_pulse_3", "The [[list_of_event_lists#3_year_pulse|three year pulse III]]")
            ,("on_thri_yearly_pulse_4", "The [[list_of_event_lists#3_year_pulse|three year pulse IV]]")
            ,("on_war_lost", "<!-- on_war_lost -->Losing a war against ''From''") -- # root = loser country, from = winner country
            ,("on_war_won", "<!-- on_war_won -->Winning a war against ''From''") -- root = winning country, from = loser country
            ,("on_yearly_pulse", "The [[list_of_event_lists#Yearly_pulse|yearly pulse I]]")
            ,("on_yearly_pulse_2", "The [[list_of_event_lists#Yearly_pulse|yearly pulse II]]")
            ,("on_yearly_pulse_3", "The [[list_of_event_lists#Yearly_pulse|yearly pulse III]]")
            ,("on_yearly_pulse_4", "The [[list_of_event_lists#Yearly_pulse|yearly pulse IV]]")
            ,("on_yearly_pulse_5", "The [[list_of_event_lists#Yearly_pulse|yearly pulse V]]")
            ,("on_weak_heir_claim", "The rise to the throne of an heir with a weak claim")
            ]

findTriggeredEventsInDisasters :: EU4EventTriggers -> [GenericStatement] -> EU4EventTriggers
findTriggeredEventsInDisasters hm scr = foldl' findInDisaster hm scr
    where
        findInDisaster :: EU4EventTriggers -> GenericStatement -> EU4EventTriggers
        findInDisaster hm stmt@[pdx| $id = @scr |] = foldl' (findInDisaster' id) hm scr
        findInDisaster hm stmt = (trace $ "Unknown top-level disaster statement: " ++ show stmt) $ hm

        findInDisaster' :: Text -> EU4EventTriggers -> GenericStatement -> EU4EventTriggers
        findInDisaster' id hm [pdx| on_start = $event |] = addEventTriggers hm [(event, EU4EvtSrcDisaster id "Start" Nothing)]
        findInDisaster' id hm [pdx| on_end = $event |] = addEventTriggers hm [(event, EU4EvtSrcDisaster id "End" Nothing)]
        findInDisaster' id hm [pdx| on_monthly = @scr |] = addEventTriggers hm ((addEventSource (EU4EvtSrcDisaster id "Monthly pulse")) (findInStmts scr))
        findInDisaster' _ hm _ = hm

findTriggeredEventsInMissions :: EU4EventTriggers -> [EU4MissionTreeBranch] -> EU4EventTriggers
findTriggeredEventsInMissions hm mtbs = foldl' (\h -> \m -> foldl' findInMission h (eu4mtb_missions m)) hm mtbs
    where
        findInMission :: EU4EventTriggers -> EU4Mission -> EU4EventTriggers
        findInMission hm m = addEventTriggers hm $ addEventSource (const (EU4EvtSrcMission (eu4m_id m))) (findInStmts (eu4m_effect m))

findTriggeredEventsInGenericScript :: EU4EventTriggers -> HashMap Text Text -> [GenericStatement] -> EU4EventTriggers
findTriggeredEventsInGenericScript hm sectionMap scr = foldl' findInGenericScript hm scr
    where
        findInGenericScript :: EU4EventTriggers -> GenericStatement -> EU4EventTriggers
        findInGenericScript hm stmt@[pdx| $id = @scr |] = foldl' (findInGenericScript' id) hm scr
        findInGenericScript hm stmt = trace ("Unknown top-level statement: " ++ show stmt) hm

        findInGenericScript' :: Text -> EU4EventTriggers -> GenericStatement -> EU4EventTriggers
        findInGenericScript' id hm [pdx| $section = @scr |] = addEventTriggers hm $ addEventSource (const (EU4EvtSrcGeneric id (HM.lookupDefault ("<pre>" <> section <> "</pre>") section sectionMap))) (findInStmts scr)
        findInGenericScript' _ hm _ = hm

findTriggeredEventsInProvinceTriggeredModifiers :: EU4EventTriggers -> [EU4ProvinceTriggeredModifier] -> EU4EventTriggers
findTriggeredEventsInProvinceTriggeredModifiers hm modifiers = addEventTriggers hm (concatMap findInProvinceTriggeredModifier modifiers)
    where
        findInProvinceTriggeredModifier :: EU4ProvinceTriggeredModifier -> [(Text, EU4EventSource)]
        findInProvinceTriggeredModifier modifier@EU4ProvinceTriggeredModifier{ptmodName = modName} =
            addEventSource (const (EU4EvtSrcGeneric modName "Activation of the province triggered modifier")) (findInStmts (ptmodOnActivation modifier)) ++
            addEventSource (const (EU4EvtSrcGeneric modName "Deactivation of the province triggered modifier")) (findInStmts (ptmodOnDeactivation modifier))

findTriggeredEventsInGovernmentMechanics :: EU4EventTriggers -> [GenericStatement] -> EU4EventTriggers
findTriggeredEventsInGovernmentMechanics hm scr = foldl' findInGovernmentMechanic hm scr
    where
        findInGovernmentMechanic :: EU4EventTriggers -> GenericStatement -> EU4EventTriggers
        findInGovernmentMechanic hm stmt@[pdx| $id = @scr |] = foldl' (findInGovernmentMechanic' id) hm scr
        findInGovernmentMechanic hm stmt = trace ("Unknown top-level statement in government mechanic: " ++ show stmt) hm

        findInGovernmentMechanic' :: Text -> EU4EventTriggers -> GenericStatement -> EU4EventTriggers
        findInGovernmentMechanic' id hm [pdx| interactions = @scr |] = foldl' (findInSection id "interaction") hm scr
        findInGovernmentMechanic' id hm [pdx| powers = @scr |] = foldl' (findInSection id "power") hm scr
        findInGovernmentMechanic' _ hm _ = hm

        findInSection :: Text -> Text -> EU4EventTriggers -> GenericStatement -> EU4EventTriggers
        findInSection id section hm [pdx| $sectionId = @scr |] = foldl' (findInSection' id section sectionId) hm scr
        findInSection _ _ hm _ = hm

        findInSection' :: Text -> Text -> Text -> EU4EventTriggers -> GenericStatement -> EU4EventTriggers
        findInSection' id "power" sectionId hm [pdx| on_min_reached = @scr |] = addEventTriggers hm $ addEventSource (const (EU4EvtSrcGovernmentMechanic id sectionId "Reaching the minimum")) (findInStmts scr)
        findInSection' id "power" sectionId hm [pdx| on_max_reached = @scr |] = addEventTriggers hm $ addEventSource (const (EU4EvtSrcGovernmentMechanic id sectionId "Reaching the maximum")) (findInStmts scr)
        findInSection' id "interaction" sectionId hm [pdx| effect = @scr |] = addEventTriggers hm $ addEventSource (const (EU4EvtSrcGovernmentMechanic id sectionId "Using the interaction")) (findInStmts scr)
        findInSection' _ _ _ hm _ = hm

findTriggeredEventsInImperialIncidents :: EU4EventTriggers -> [GenericStatement] -> EU4EventTriggers
findTriggeredEventsInImperialIncidents hm scr = foldl' findInImperialIncident hm scr
    where
        findInImperialIncident :: EU4EventTriggers -> GenericStatement -> EU4EventTriggers
        findInImperialIncident hm stmt@[pdx| $id = @scr |] = foldl' (findInImperialIncident' id) hm scr
        findInImperialIncident hm stmt = trace ("Unknown top-level statement in imperial incident: " ++ show stmt) hm

        findInImperialIncident' :: Text -> EU4EventTriggers -> GenericStatement -> EU4EventTriggers
        findInImperialIncident' id hm [pdx| event = $event |] = addEventTriggers hm [(event, EU4EvtSrcGeneric id "Used as a template for the imperial incident")]
        findInImperialIncident' _ hm _ = hm
