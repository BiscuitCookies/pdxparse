{-|
Module      : HOI4.Events
Description : Feature handler for Hearts of Iron IV events
-}
module HOI4.Events (
        parseHOI4Events
    ,   writeHOI4Events
    ,   findTriggeredEventsInEvents
    ,   findTriggeredEventsInDecisions
    ,   findTriggeredEventsInOnActions
    ,   findTriggeredEventsInNationalFocus
    ,   findTriggeredEventsInIdeas
    ,   findTriggeredEventsInCharacters
    ,   findTriggeredEventsInScriptedEffects
    ,   findTriggeredEventsInBops
    ) where

import Debug.Trace (trace, traceM)

import Control.Arrow ((&&&))
import Control.Monad (liftM, forM, foldM, when, (<=<))
import Control.Monad.Except (MonadError (..))
import Control.Monad.State (MonadState (..), gets)
import Control.Monad.Trans (MonadIO (..))

import Data.List (intersperse, foldl')
import Data.Maybe (isJust, isNothing, fromMaybe, fromJust, catMaybes, mapMaybe)
import Data.Monoid ((<>))

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL

import Text.PrettyPrint.Leijen.Text (Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP

import Abstract -- everything
import qualified Doc
import HOI4.Common -- everything
import FileIO (Feature (..), writeFeatures)
import HOI4.Messages (imsg2doc)
import MessageTools (iquotes)
import QQ (pdx)
import SettingsTypes ( PPT, Settings (..), Game (..)
                     , IsGame (..), IsGameData (..), IsGameState (..)
                     , getGameL10n, getGameL10nIfPresent
                     , setCurrentFile, withCurrentFile
                     , hoistErrors, hoistExceptions)
import HOI4.Handlers (flagText)

-- | Empty event value. Starts off Nothing/empty everywhere.
newHOI4Event :: HOI4Scope -> FilePath -> HOI4Event
newHOI4Event escope = HOI4Event Nothing [] [] escope Nothing Nothing Nothing Nothing False False False Nothing Nothing Nothing
-- | Empty event option vaule. Starts off Nothing everywhere.
newHOI4Option :: HOI4Option
newHOI4Option = HOI4Option Nothing Nothing Nothing Nothing

-- | Take the event scripts from game data and parse them into event data
-- structures.
parseHOI4Events :: (HOI4Info g, Monad m) =>
    HashMap String GenericScript -> PPT g m (HashMap Text HOI4Event)
parseHOI4Events scripts = HM.unions . HM.elems <$> do
    tryParse <- hoistExceptions $
        HM.traverseWithKey
            (\sourceFile scr ->
                setCurrentFile sourceFile $ mapM parseHOI4Event scr)
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
                where mkEvtMap :: [HOI4Event] -> HashMap Text HOI4Event
                      mkEvtMap = HM.fromList . map (fromJust . hoi4evt_id &&& id)
                        -- Events returned from parseEvent are guaranteed to have an id.

-- | Present the parsed events as wiki text and write them to the appropriate
-- files.
writeHOI4Events :: (HOI4Info g, MonadIO m) => PPT g m ()
writeHOI4Events = do
    events <- getEvents
    let pathedEvents :: [Feature HOI4Event]
        pathedEvents = map (\evt -> Feature {
                                    featurePath = Just (hoi4evt_path evt)
                                ,   featureId = hoi4evt_id evt <> Just ".txt"
                                ,   theFeature = Right evt })
                            (HM.elems events)
    writeFeatures "events"
                  pathedEvents
                  (\e -> scope (hoi4evt_scope e) $ ppEvent e)

-- | Parse a statement in an events file. Some statements aren't events; for
-- those, and for any obvious errors, return Right Nothing.
parseHOI4Event :: (HOI4Info g, MonadError Text m) =>
    GenericStatement -> PPT g m (Either Text (Maybe HOI4Event))
parseHOI4Event (StatementBare lhs) = withCurrentFile $ \f ->
        throwError $ T.pack (f ++ ": bare statement at top level: " ++ show lhs)
parseHOI4Event stmt@[pdx| %left = %right |] = case right of
    CompoundRhs parts -> case left of
        CustomLhs _ -> throwError "internal error: custom lhs"
        IntLhs _ -> throwError "int lhs at top level"
        AtLhs _ -> return (Right Nothing)
        GenericLhs etype _ ->
            let mescope = case T.toLower etype of
                    "country_event" -> Just HOI4Country
                    "unit_leader_event" -> Just HOI4Country
                    "operative_leader_event" -> Just HOI4Operative
                    "state_event" -> Just HOI4ScopeState
                    "news_event" -> Just HOI4Country -- ?
                    "event" -> Just HOI4Country -- ?
                    _ -> Nothing
            in case mescope of
                Nothing -> throwError $ "unrecognized event type " <> etype
                Just escope -> withCurrentFile $ \file -> do
                    mevt <- hoistErrors (foldM eventAddSection (Just (newHOI4Event escope file)) parts)
                    case mevt of
                        Left err -> return (Left err)
                        Right Nothing -> return (Right Nothing)
                        Right (Just evt) ->
                            if isJust (hoi4evt_id evt)
                            then return (Right (Just evt))
                            else return (Left $ "error parsing events in " <> T.pack file
                                         <> ": missing event id")

    _ -> return (Right Nothing)
parseHOI4Event _ = throwError "operator other than ="

-- | Intermediate structure for interpreting event title blocks.
data EvtTitleI = EvtTitleI {
        eti_text :: Maybe Text
    ,   eti_trigger :: Maybe GenericScript
    }
-- | Interpret the @title@ section of an event. This can be either a
-- localization key or a conditional title block. (TODO: document the
-- format here)
evtTitle :: MonadError Text m => Maybe Text -> GenericScript -> m HOI4EvtTitle
evtTitle meid scr = case foldl' evtTitle' (EvtTitleI Nothing Nothing) scr of
        EvtTitleI (Just t) Nothing -- title = { text = foo }
            -> return $ HOI4EvtTitleSimple t
        EvtTitleI Nothing (Just trig) -- title = { trigger = { .. } } (invalid)
            -> return $ HOI4EvtTitleCompound scr
        EvtTitleI (Just t) (Just trig) -- title = { trigger = { .. } text = foo }
                                      -- e.g. pirate.1
            -> return $ HOI4EvtTitleConditional trig t
        EvtTitleI Nothing Nothing -- title = { switch { .. = { text = foo } } }
                                 -- e.g. action.39
            -> throwError $ "bad title: no trigger nor text" <> case meid of
                Just eid -> " in event " <> eid
                Nothing -> ""
    where
        evtTitle' ed [pdx| trigger = @trig |] = ed { eti_trigger = Just trig }
        evtTitle' ed [pdx| text = ?txt |] = ed { eti_text = Just txt }
        evtTitle' ed [pdx| title = ?txt |] = ed { eti_text = Just txt }
        evtTitle' ed [pdx| show_sound = %_ |] = ed
        evtTitle' ed [pdx| $label = %_ |]
            = error ("unrecognized title section " ++ T.unpack label
                     ++ " in " ++ maybe "(unknown)" T.unpack meid)
        evtTitle' ed stmt
            = error ("unrecognized title section in " ++ maybe "(unknown)" T.unpack meid
                    ++ ": " ++ show stmt)


-- | Intermediate structure for interpreting event description blocks.
data EvtDescI = EvtDescI {
        edi_text :: Maybe Text
    ,   edi_trigger :: Maybe GenericScript
    }
-- | Interpret the @desc@ section of an event. This can be either a
-- localization key or a conditional description block. (TODO: document the
-- format here)
evtDesc :: MonadError Text m => Maybe Text -> GenericScript -> m HOI4EvtDesc
evtDesc meid scr = case foldl' evtDesc' (EvtDescI Nothing Nothing) scr of
        EvtDescI (Just t) Nothing -- desc = { text = foo }
            -> return $ HOI4EvtDescSimple t
        EvtDescI Nothing (Just trig) -- desc = { trigger = { .. } } (invalid)
            -> return $ HOI4EvtDescCompound scr
        EvtDescI (Just t) (Just trig) -- desc = { trigger = { .. } text = foo }
                                      -- e.g. pirate.1
            -> return $ HOI4EvtDescConditional trig t
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
eventAddSection :: (HOI4Info g, MonadError Text m) =>
    Maybe HOI4Event -> GenericStatement -> PPT g m (Maybe HOI4Event)
eventAddSection Nothing _ = return Nothing
eventAddSection mevt stmt = sequence (eventAddSection' <$> mevt <*> pure stmt) where
    eventAddSection' evt stmt@[pdx| id = %rhs |]
        = case (textRhs rhs, floatRhs rhs) of
            (Just tid, _) -> return evt { hoi4evt_id = Just tid }
            (_, Just nid) -> return evt { hoi4evt_id = Just (T.pack $ show (nid::Int)) }
            _ -> withCurrentFile $ \file ->
                throwError $ "bad id in " <> T.pack file <> ": " <> T.pack (show rhs)
    eventAddSection' evt stmt@[pdx| title = %rhs |] =
        let oldtitles = hoi4evt_title evt in case rhs of
            (textRhs -> Just title) -> return evt { hoi4evt_title = oldtitles ++ [HOI4EvtTitleSimple title] }
            CompoundRhs scr -> do
                let meid = hoi4evt_id evt
                title <- evtTitle meid scr
                return evt { hoi4evt_title = oldtitles ++ [title] }
            _ -> throwError $ "bad title" <> maybe "" (" in event " <>) (hoi4evt_id evt)
    eventAddSection' evt stmt@[pdx| desc = %rhs |] =
        let olddescs = hoi4evt_desc evt in case rhs of
            (textRhs -> Just desc) -> return evt { hoi4evt_desc = olddescs ++ [HOI4EvtDescSimple desc] }
            CompoundRhs scr -> do
                let meid = hoi4evt_id evt
                desc <- evtDesc meid scr
                return evt { hoi4evt_desc = olddescs ++ [desc] }
            _ -> throwError $ "bad desc" <>  maybe "" (" in event " <>) (hoi4evt_id evt)
    eventAddSection' evt stmt@[pdx| $picture = %_ |] | T.toLower picture == "picture" = return evt
--  picture has conditions like desc. Ignore for now since we don't actually use it
--    eventAddSection' evt stmt@[pdx| picture = %rhs |] = case textRhs rhs of
--        Just pic -> return evt { hoi4evt_picture = Just pic }
--        _ -> throwError "bad picture"
    eventAddSection' evt stmt@[pdx| goto = %rhs |] = return evt
    eventAddSection' evt stmt@[pdx| trigger = %rhs |] = case rhs of
        CompoundRhs [] -> return evt
        CompoundRhs trigger_script -> case trigger_script of
            [] -> return evt -- empty, treat as if it wasn't there
            _ -> return evt { hoi4evt_trigger = Just trigger_script }
        _ -> throwError "bad event trigger"
    eventAddSection' evt stmt@[pdx| is_triggered_only = %rhs |] = case rhs of
        GenericRhs "yes" [] -> return evt { hoi4evt_is_triggered_only = Just True }
        -- no is the default, so I don't think this is ever used
        GenericRhs "no" [] -> return evt { hoi4evt_is_triggered_only = Just False }
        _ -> throwError "bad trigger"
    eventAddSection' evt stmt@[pdx| mean_time_to_happen = %rhs |] = case rhs of
        CompoundRhs [] -> return evt
        CompoundRhs mtth -> return evt { hoi4evt_mean_time_to_happen = Just mtth }
        _ -> throwError "bad MTTH"
    eventAddSection' evt stmt@[pdx| immediate = %rhs |] = case rhs of
        CompoundRhs [] -> return evt
        CompoundRhs immediate -> return evt { hoi4evt_immediate = Just immediate }
        _ -> throwError "bad immediate section"
    eventAddSection' evt stmt@[pdx| option = %rhs |] =  case rhs of
        CompoundRhs option -> do
            newHOI4Options <- addHOI4Option (hoi4evt_options evt) option
            return evt { hoi4evt_options = newHOI4Options }
        _ -> throwError "bad option"
    eventAddSection' evt stmt@[pdx| fire_only_once = %rhs |]
        | GenericRhs "yes" [] <- rhs = return evt { hoi4evt_fire_only_once = True }
        | GenericRhs "no"  [] <- rhs = return evt { hoi4evt_fire_only_once = False }
    eventAddSection' evt stmt@[pdx| major = %rhs |] = case rhs of
        GenericRhs "yes" [] -> return evt { hoi4evt_major = True }
        -- No is the default
        GenericRhs "no"  [] -> return evt { hoi4evt_major = False }
        _ -> throwError "bad major"
    eventAddSection' evt stmt@[pdx| show_major = %rhs |] = case rhs of
        CompoundRhs show_major_script -> case show_major_script of
            [] -> return evt -- empty, treat as if it wasn't there
            _ -> return evt { hoi4evt_show_major = Just show_major_script }
        _ -> throwError "bad event show_major"
    eventAddSection' evt stmt@[pdx| $hidden = %rhs |] | T.toLower hidden == "hidden" = case rhs of
        GenericRhs "yes" [] -> return evt { hoi4evt_hide_window = True }
        -- No is the default
        GenericRhs "no"  [] -> return evt { hoi4evt_hide_window = False }
        _ -> throwError "bad hidden"
    eventAddSection' evt stmt@[pdx| fire_for_sender = %rhs |] = case rhs of
        -- Yes is the default, so I don't think this is ever used
        GenericRhs "yes" [] -> return evt { hoi4evt_fire_for_sender = Just False }
        GenericRhs "no" [] -> return evt { hoi4evt_fire_for_sender = Just True }
        _ -> throwError "bad fire_for_sender"
    eventAddSection' evt stmt@[pdx| timeout_days = %_ |] = return evt
    eventAddSection' evt stmt@[pdx| minor_flavor = %_ |] = return evt -- unknown effect
    eventAddSection' evt stmt@[pdx| $label = %_ |] =
        withCurrentFile $ \file ->
            throwError $ "unrecognized event section in " <> T.pack file <> ": " <> label
    eventAddSection' evt stmt =
        withCurrentFile $ \file ->
            throwError $ "unrecognized event section in " <> T.pack file <> ": " <> T.pack (show stmt)

-- | Interpret an option block and append it to the list of options.
addHOI4Option :: (IsGame g, Monad m) => Maybe [HOI4Option] -> GenericScript -> PPT g m (Maybe [HOI4Option])
addHOI4Option Nothing opt = addHOI4Option (Just []) opt
addHOI4Option (Just opts) opt = do
    optn <- foldM optionAddStatement newHOI4Option opt
    return $ Just (opts ++ [optn])

-- | Interpret one section of an option block and add it to the option data.
optionAddStatement :: (IsGame g, Monad m) => HOI4Option -> GenericStatement -> PPT g m HOI4Option
optionAddStatement opt stmt@[pdx| name = ?name |]
    = return $ opt { hoi4opt_name = Just name }
optionAddStatement opt stmt@[pdx| ai_chance = @ai_chance |]
    = return $ opt { hoi4opt_ai_chance = Just (aiWillDo ai_chance) } -- hope can re-use the aiWilldo script
optionAddStatement opt stmt@[pdx| trigger = %rhs |] = case rhs of
    CompoundRhs [] -> return opt
    CompoundRhs trigger_script -> return $ opt { hoi4opt_trigger = Just trigger_script }
    _ -> return opt
optionAddStatement opt stmt = do
    -- Not a GenericLhs - presumably an effect.
    effects_pp'd <- setIsInEffect True (optionAddEffect (hoi4opt_effects opt) stmt)
    return $ opt { hoi4opt_effects = effects_pp'd }

-- | Append an effect to the effects of an option.
optionAddEffect :: Monad m => Maybe GenericScript -> GenericStatement -> PPT g m (Maybe GenericScript)
optionAddEffect Nothing stmt = optionAddEffect (Just []) stmt
optionAddEffect (Just effs) stmt = return $ Just (effs ++ [stmt])

iquotes't = Doc.doc2text . iquotes

-- | Present an event's title block.
ppTitles :: (HOI4Info g, Monad m) => Bool {- ^ Is this a hidden event? -}
                                -> [HOI4EvtTitle] -> Text -> PPT g m Doc
ppTitles _ [] eid = return $ "| event_name = " <> Doc.strictText eid
ppTitles False [HOI4EvtTitleSimple key] eid = ("| event_name = " <>) . Doc.strictText . Doc.nl2br <$> getGameL10n key
ppTitles True [HOI4EvtTitleSimple key]eid  = ("| event_name = (Hidden) " <>) . Doc.strictText . Doc.nl2br <$> getGameL10n key
ppTitles True _ eid = return "| event_name = (This event is hidden and has no title.)"
ppTitles _ titles eid = (("| event_name = " <> Doc.strictText eid <> PP.line <>"| cond_event_name = yes" <> PP.line <> "| cond_name = ") <>) . PP.vsep <$> mapM ppTitle titles where
    ppTitle (HOI4EvtTitleSimple key) = ("Otherwise:<br>:" <>) <$> fmtTitle key
    ppTitle (HOI4EvtTitleConditional scr key) = mconcat <$> sequenceA
        [pure "The following title is used if:", pure PP.line
        ,imsg2doc =<< ppMany scr, pure PP.line
        ,pure ":", fmtTitle key
        ]
    ppTitle (HOI4EvtTitleCompound scr) =
        imsg2doc =<< ppMany scr
    fmtTitle key = flip fmap (getGameL10nIfPresent key) $ \case
        Nothing -> Doc.strictText key
        Just txt -> "''" <> Doc.strictText (Doc.nl2br txt) <> "''"

-- | Present an event's description block.
ppDescs :: (HOI4Info g, Monad m) => Bool {- ^ Is this a hidden event? -}
                                -> [HOI4EvtDesc] -> PPT g m Doc
ppDescs True _ = return "| cond_event_text = (This event is hidden and has no description.)"
ppDescs _ [] = return "| event_text = (No description)"
ppDescs _ [HOI4EvtDescSimple key] = ("| event_text = " <>) . Doc.strictText . Doc.nl2br <$> getGameL10n key
ppDescs _ descs = (("| cond_event_text = yes" <> PP.line <> "| event_text = ") <>) . PP.vsep <$> mapM ppDesc descs where
    ppDesc (HOI4EvtDescSimple key) = ("Otherwise:<br>:" <>) <$> fmtDesc key
    ppDesc (HOI4EvtDescConditional scr key) = mconcat <$> sequenceA
        [pure "The following description is used if:", pure PP.line
        ,imsg2doc =<< ppMany scr, pure PP.line
        ,pure ":", fmtDesc key
        ]
    ppDesc (HOI4EvtDescCompound scr) =
        imsg2doc =<< ppMany scr
    fmtDesc key = flip fmap (getGameL10nIfPresent key) $ \case
        Nothing -> Doc.strictText key
        Just txt -> "''" <> Doc.strictText (Doc.nl2br txt) <> "''"

ppEventLoc :: (HOI4Info g, Monad m) => Text -> PPT g m Text
ppEventLoc id = do
    loc <- getEventTitle id -- Note: Hidden events often have empty titles, see e.g. fetishist_flavor.400
    case loc of
        (Just t) | T.length (T.strip t) /= 0 -> return $ "<!-- " <> id <> " -->" <> iquotes't t -- TODO: Add link if possible
        _ -> return $ "<tt>" <> id <> "</tt>"


ppTriggeredBy :: (HOI4Info g, Monad m) => Text -> [Doc] -> PPT g m Doc
ppTriggeredBy eventId trig = do
    eventTriggers <- getEventTriggers
    let mtriggers = HM.lookup eventId eventTriggers
    case mtriggers of
        Just triggers -> do
            ts <- mapM ppEventSource triggers
            -- FIXME: This is a bit ugly, but we only want a list if there's more than one trigger
            let ts' = if length ts < 2 then
                    ts
                else
                    map (\d -> Doc.strictText $ "* " <> Doc.doc2text d) ts
            return $ mconcat $ PP.line : intersperse PP.line ts'
        _ -> if null trig then return $ Doc.strictText "(No triggers)" else return $ Doc.strictText "(Triggers in event)"

-- | Pretty-print an event. If some essential parts are missing from the data,
-- throw an exception.
ppEvent :: forall g m. (HOI4Info g, MonadError Text m) =>
    HOI4Event -> PPT g m Doc
ppEvent evt = maybe
    (throwError "hoi4evt_id missing")
    (\eid -> setCurrentFile (hoi4evt_path evt) $ do
        -- Valid event
        version <- gets (gameVersion . getSettings)
        (conditional, options_pp'd) <- case hoi4evt_options evt of
            Just opts -> ppoptions (hoi4evt_hide_window evt) eid opts
            _ -> fixForNoOptions eid  --BC: less ugly fix for having no options for an event
        titleLoc <- ppTitles (hoi4evt_hide_window evt) (hoi4evt_title evt) eid -- get localisation of title
        descLoc <- ppDescs (hoi4evt_hide_window evt) (hoi4evt_desc evt)
        let evtArg :: Text -> (HOI4Event -> Maybe a) -> (a -> PPT g m Doc) -> PPT g m [Doc]
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
            isTriggeredOnly = fromMaybe False $ hoi4evt_is_triggered_only evt
            isFireOnlyOnce = hoi4evt_fire_only_once evt
            isMajor = hoi4evt_major evt
            isFireForSender = fromMaybe False $ hoi4evt_fire_for_sender evt
            evtId = Doc.strictText eid
        trigger_pp'd <- evtArg "trigger" hoi4evt_trigger ppScript
        showmajor_pp'd <- evtArg "trigger" hoi4evt_show_major ppScript
        mmtth_pp'd <- mapM (ppMtth isTriggeredOnly) (hoi4evt_mean_time_to_happen evt)
        immediate_pp'd <- setIsInEffect True (evtArg "immediate" hoi4evt_immediate ppScript)
        triggered_pp <- ppTriggeredBy eid trigger_pp'd
        -- Keep track of incomplete events
        when (not isTriggeredOnly && isNothing mmtth_pp'd && null trigger_pp'd) $
            -- TODO: use logging instead of trace
            traceM ("warning: is_triggered_only, trigger, and mean_time_to_happen missing for event id " ++ T.unpack eid)
        when (isTriggeredOnly && Doc.doc2text triggered_pp == "(No triggers)" && isNothing mmtth_pp'd && null trigger_pp'd) $
            -- TODO: use logging instead of trace
            traceM ("warning: Event is is_triggered_only but no triggers or mean_time_to_hapen found for event id " ++ T.unpack eid)
        when (isFireOnlyOnce && isMajor) $
            -- TODO: use logging instead of trace
            traceM ("warning: Event is fire_only_once and major " ++ T.unpack eid)
        return . mconcat $
            ["<section begin=", evtId, "/>", PP.line
            ,"{{Event", PP.line
            ,"| version = ", Doc.strictText version, PP.line
            ,"| event_id = ", evtId, PP.line
            ,titleLoc, PP.line
            ,descLoc, PP.line
            ] ++
            ( if isFireOnlyOnce then
                ["| fire_only_once = yes", PP.line]
            else []) ++
            ( if isMajor then
                ["| major = yes", PP.line]
            else []) ++
            ( if isFireForSender then
                ["| fire_for_sender = no", PP.line]
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
                Nothing -> if not $ null trigger_pp'd then [] else ["| triggered_only =", PP.line
                        ,"* Unknown (Missing MTTH and is_triggered_only)", PP.line]
                Just mtth_pp'd ->
                    ["| mtth = ", PP.line
                    ,mtth_pp'd, PP.line]) ++
            immediate_pp'd ++
            (if conditional then ["| option conditions = yes", PP.line] else []) ++
            -- option_conditions = no (not implemented yet)
            ["| options = ", options_pp'd, PP.line] ++
            ["| collapse = no", PP.line
            ,"}}", PP.line
            ,"<section end=", evtId, "/>", PP.line
            ])
    (hoi4evt_id evt)

fixForNoOptions :: Monad m => Text -> m (Bool, Doc)
fixForNoOptions eid = do --BC: less ugly fix for having no options for an event
    let evtId = Doc.strictText eid
        message = mconcat ["(no options for event ", evtId, ")"]
    return (False, message)
-- | Present the options of an event.
ppoptions :: (HOI4Info g, MonadError Text m) =>
    Bool -> Text -> [HOI4Option] -> PPT g m (Bool, Doc)
ppoptions hidden evtid opts = do
    let triggered = any (isJust . hoi4opt_trigger) opts
    options_pp'd <- mapM (ppoption evtid hidden triggered) opts
    return (triggered, mconcat . (PP.line:) . intersperse PP.line $ options_pp'd)

-- | Present a single event option.
ppoption :: (HOI4Info g, MonadError Text m) =>
    Text -> Bool -> Bool -> HOI4Option -> PPT g m Doc
ppoption evtid hidden triggered opt = do
    optNameLoc <- getGameL10n `mapM` hoi4opt_name opt
    case optNameLoc of
        -- NB: some options have no effect, e.g. start of Peasants' War.
        Just name_loc -> ok name_loc
        Nothing -> if hidden
            then ok "(Dummy option for hidden event)"
            else ok "(Dummy option for possibly AI or invisible actions)"
                --old thing-throwError $ "some required option sections missing in " <> evtid <> " - dumping: " <> T.pack (show opt)
    where
        ok name_loc = let mtrigger = hoi4opt_trigger opt in do
            mawd_pp'd   <- mapM (imsg2doc <=< ppAiWillDo) (hoi4opt_ai_chance opt)
            effects_pp'd <- setIsInEffect True (ppScript (fromMaybe [] (hoi4opt_effects opt)))
            mtrigger_pp'd <- sequence (ppScript <$> mtrigger)
            return . mconcat $
                ["{{Option",PP.line
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
                maybe [] (\awd_pp'd ->
                    ["| aichance = ", PP.line
                    ,awd_pp'd, PP.line]) mawd_pp'd ++
                -- 1 = no
                ["}}"
                ]

formatWeight :: HOI4EventWeight -> Text
formatWeight Nothing = ""
formatWeight (Just (n, d)) = T.pack (" (Base weight: " ++ show n ++ "/" ++ show d ++ ")")

ppEventSource :: (HOI4Info g, Monad m) => HOI4EventSource -> PPT g m Doc
ppEventSource (HOI4EvtSrcOption eventId optionId) = do
    eventLoc <- ppEventLoc eventId
    optLoc <- getGameL10n optionId
    return $ Doc.strictText $ mconcat [ "The event "
        , eventLoc
        , " option "
        , iquotes't optLoc
        ]
ppEventSource (HOI4EvtSrcImmediate eventId) = do
    eventLoc <- ppEventLoc eventId
    return $ Doc.strictText $ mconcat [ "As an immediate effect of the "
        , eventLoc
        , " event"
        ]
ppEventSource (HOI4EvtSrcDecComplete id loc) = do
    return $ Doc.strictText $ mconcat ["Taking the decision "
        , "<!-- "
        , id
        , " -->"
        , iquotes't loc
        ]
ppEventSource (HOI4EvtSrcDecRemove id loc) = do
    return $ Doc.strictText $ mconcat ["Finishing the decision "
        , "<!-- "
        , id
        , " -->"
        , iquotes't loc
        ]
ppEventSource (HOI4EvtSrcDecCancel id loc) = do
    return $ Doc.strictText $ mconcat ["Triggering the cancel trigger on the decision "
        , "<!-- "
        , id
        , " -->"
        , iquotes't loc
        ]
ppEventSource (HOI4EvtSrcDecTimeout id loc) = do
    return $ Doc.strictText $ mconcat ["Running out the timer on the decision "
        , "<!-- "
        , id
        , " -->"
        , iquotes't loc
        ]
ppEventSource (HOI4EvtSrcOnAction act weight) = do
    actn <- actionName act
    return $ Doc.strictText $ actn <> formatWeight weight
    where
        actionName :: (HOI4Info g, Monad m) =>
            Text -> PPT g m Text
        actionName n
            | "on_monthly_" `T.isPrefixOf` n = do
                let tag = case T.stripPrefix "on_monthly_" n of
                        Just nc -> nc
                        _ -> "<!-- Check game Script -->"
                let actmsg = "<!-- " <> n <>  " -->On every month for "
                tagloc <- flagText (Just HOI4Country) tag
                return $ actmsg <> tagloc
            | "on_weekly_" `T.isPrefixOf` n = do
                let tag = case T.stripPrefix "on_weekly_" n of
                        Just nc -> nc
                        _ -> "<!-- Check game Script -->"
                let actmsg = "<!-- " <> n <>  " -->On every week for "
                tagloc <- flagText (Just HOI4Country) tag
                return $ actmsg <> tagloc
            | "on_daily_" `T.isPrefixOf` n = do
                let tag = case T.stripPrefix "on_daily_" n of
                        Just nc -> nc
                        _ -> "<!-- Check game Script -->"
                let actmsg = "<!-- " <> n <>  " -->On every day for "
                tagloc <- flagText (Just HOI4Country) tag
                return $ actmsg <> tagloc
            | otherwise =
                return $ HM.findWithDefault ("<pre>" <> n <> "</pre>") n actionNameTable

        actionNameTable :: HashMap Text Text
        actionNameTable = HM.fromList
            [("on_ace_killed","<!-- on_ace_killed -->On ace killed")
            ,("on_ace_killed_by_ace","<!-- on_ace_killed_by_ace -->On ace killed by enemy ace")
            ,("on_ace_killed_other_ace","<!-- on_ace_killed_other_ace -->On ace kills enemy ace")
            ,("on_aces_killed_each_other","<!-- on_aces_killed_each_other -->On aces killed each other")
            ,("on_ace_promoted","<!-- on_ace_promoted -->On ace promoted")
            ,("on_annex", "<!-- on_annex -->On nation annexed")
            ,("on_army_leader_daily","<!-- on_army_leader_daily -->On every day for army leader")
            ,("on_army_leader_lost_combat","<!-- on_army_leader_lost_combat -->On army leader loses combat")
            ,("on_army_leader_won_combat","<!-- on_army_leader_won_combat -->On army leader wins combat")
            ,("on_border_war_lost","<!-- on_border_war_lost -->On lost border conflict war")
            ,("on_capitulation","<!-- on_capitulation -->On nation capitulation")
            ,("on_civil_war_end","<!-- on_civil_war_end -->On civil war end")
            ,("on_civil_war_end_before_annexation","<!-- on_civil_war_end_before_annexation -->On civil war end before annexation")
            ,("on_daily","<!-- on_daily -->On every day")
            ,("on_declare_war","<!-- on_declare_war -->On declared war")
            ,("on_faction_formed","<!-- on_faction_formed -->On faction formed")
            ,("on_government_change","<!-- on_government_change -->On government changed")
            ,("on_government_exiled","<!-- on_government_exiled -->On government exiled")
            ,("on_join_faction","<!-- on_join_faction -->On faction joined")
            ,("on_justifying_wargoal_pulse","<!-- on_justifying_wargoal_pulse -->On justifying wargoal")
            ,("on_liberate","<!-- on_liberate -->On nation liberated")
            ,("on_new_term_election","<!-- on_new_term_election -->On new term election")
            ,("on_nuke_drop","<!-- on_nuke_drop -->On nuke dropped")
            ,("on_monthly","<!-- on_monthly -->On every month")
            ,("on_offer_join_faction","<!-- on_offer_join_faction -->On nation invited to faction")
            ,("on_operative_captured","<!-- on_operative_captured -->On operative captured")
            ,("on_operative_death","<!-- on_operative_death -->On operative death")
            ,("on_operative_detected_during_operation","<!-- on_operative_detected_during_operation -->On operative detected during operation")
            ,("on_peaceconference_ended","<!-- on_peaceconference_ended -->On peace conference ended")
            ,("on_puppet","<!-- on_puppet -->On nation puppeted")
            ,("on_release_as_free","<!-- on_release_as_free -->On nation released as free nation")
            ,("on_release_as_puppet","<!-- on_release_as_puppet -->On nation released as puppet")
            ,("on_ruling_party_change","<!-- on_ruling_party_change -->On ruling party change")
            ,("on_state_control_changed","<!-- on_state_control_changed -->On state control changed")
            ,("on_startup", "<!-- on_startup -->On startup")
            ,("on_subject_annexed","<!-- on_subject_annexed -->On subject nation annexed")
            ,("on_subject_free","<!-- on_subject_free -->On subject nation freed")
            ,("on_unit_leader_created","<!-- on_unit_leader_created -->On army leader created")
            ,("on_war_relation_added","<!-- on_war_relation_added -->On nation joined war")
            ,("on_wargoal_expire","<!-- on_wargoal_expire -->On wargoal expired")
            ,("on_weekly","<!-- on_weekly -->On every week")
            ]
ppEventSource (HOI4EvtSrcNFComplete id loc icon) = do
    gfx <- getInterfaceGFX
    iconnf <-
        let iconname = HM.findWithDefault icon icon gfx in
        return $ "[[File:" <> iconname <> ".png|28px]]"
    return $ Doc.strictText $ mconcat ["Completing the national focus "
        , iconnf
        , " <!-- "
        , id
        , " -->"
        , iquotes't loc
        ]
ppEventSource (HOI4EvtSrcNFSelect id loc icon) = do
    gfx <- getInterfaceGFX
    iconnf <-
        let iconname = HM.findWithDefault icon icon gfx in
        return $ "[[File:" <> iconname <> ".png|28px]]"
    return $ Doc.strictText $ mconcat ["Selecting the national focus "
        , iconnf
        , " <!-- "
        , id
        , " -->"
        , iquotes't loc
        ]
ppEventSource (HOI4EvtSrcIdeaOnAdd id loc icon categ) = do
    gfx <- getInterfaceGFX
    iconnf <-
        let iconname = HM.findWithDefault icon icon gfx in
        return $ "[[File:" <> iconname <> ".png|28px]]"
    catloc <- getGameL10n categ
    return $ Doc.strictText $ mconcat ["When the "
        , catloc
        , " "
        , iconnf
        , " <!-- "
        , id
        , " -->"
        , iquotes't loc
        , " is added"
        ]
ppEventSource (HOI4EvtSrcIdeaOnRemove id loc icon categ) = do
    gfx <- getInterfaceGFX
    iconnf <-
        let iconname = HM.findWithDefault icon icon gfx in
        return $ "[[File:" <> iconname <> ".png|28px]]"
    catloc <- getGameL10n categ
    return $ Doc.strictText $ mconcat ["When the "
        , catloc
        , " "
        , iconnf
        , " <!-- "
        , id
        , " -->"
        , iquotes't loc
        , " is removed"
        ]
ppEventSource (HOI4EvtSrcCharacterOnAdd id loc) =
    return $ Doc.strictText $ mconcat ["When the advisor "
        , " <!-- "
        , id
        , " -->"
        , iquotes't loc
        , " is added"
        ]
ppEventSource (HOI4EvtSrcCharacterOnRemove id loc) =
    return $ Doc.strictText $ mconcat ["When the advisor "
        , " <!-- "
        , id
        , " -->"
        , iquotes't loc
        , " is removed"
        ]
ppEventSource (HOI4EvtSrcScriptedEffect id weight) =
    return $ Doc.strictText $ mconcat ["When scripted effect "
        , iquotes't id
        , " is activated"
        ]
ppEventSource (HOI4EvtSrcBopOnActivate id) = do
    loc <- getGameL10n id
    return $ Doc.strictText $ mconcat ["When reaching the "
        , "<!-- "
        , id
        , " -->"
        , iquotes't loc
        , " balance of power range"
        ]
ppEventSource (HOI4EvtSrcBopOnDeactivate id) = do
    loc <- getGameL10n id
    return $ Doc.strictText $ mconcat ["When leaving the "
        , "<!-- "
        , id
        , " -->"
        , iquotes't loc
        , " balance of power range"
        ]

findInStmt :: GenericStatement -> [(HOI4EventWeight, Text)]
findInStmt stmt@[pdx| $lhs = @scr |] | lhs == "country_event" || lhs == "news_event" || lhs == "unit_leader_event" || lhs == "state_event" || lhs == "operative_leader_event" =
    maybe (trace ("Unrecognized event trigger: " ++ show stmt) [])
        (\triggeredId -> [(Nothing, triggeredId)])
        (getId scr)
    where
        getId :: [GenericStatement] -> Maybe Text
        getId [] = Nothing
        getId (stmt@[pdx| id = ?!id |] : _) = case id of
            Just (Left n) -> Just $ T.pack (show (n :: Int))
            Just (Right t) -> Just t
            _ -> trace ("Invalid event id statement: " ++ show stmt) Nothing
        getId (_ : ss) = getId ss
findInStmt stmt@[pdx| $lhs = $id |]
    | lhs == "country_event" || lhs == "news_event" || lhs == "unit_leader_event" || lhs == "state_event" || lhs == "operative_leader_event" || lhs == "on_win" || lhs == "on_lose" || lhs == "on_cancel"=
        [(Nothing, id)]
findInStmt [pdx| events = @scr |]  = mapMaybe extractEvent scr
    where
        extractEvent :: GenericStatement -> Maybe (HOI4EventWeight, Text)
        extractEvent (StatementBare (GenericLhs e [])) = Just (Nothing, e)
        extractEvent (StatementBare (IntLhs e)) = Just (Nothing, T.pack (show e))
        extractEvent stmt = trace ("Unknown in events statement: " ++ show stmt) Nothing
findInStmt [pdx| random_events = @scr |] =
    let evts = mapMaybe extractRandomEvent scr
        total = sum $ map fst evts
    in map (\t -> (Just (fst t, total), snd t)) evts
    where
        extractRandomEvent :: GenericStatement -> Maybe (Integer, Text)
        extractRandomEvent stmt@[pdx| !weight = ?!id |] = case id of
            Just (Left n) -> Just (fromIntegral weight, T.pack (show (n :: Int)))
            Just (Right t) -> Just (fromIntegral weight, t)
            _ -> trace ("Invalid event id in random_events: " ++ show stmt) Nothing
        extractRandomEvent stmt = trace ("Unknown in random_events statement: " ++ show stmt) Nothing
findInStmt [pdx| %lhs = @scr |] = findInStmts scr
findInStmt _ = []

findInStmts :: [GenericStatement] -> [(HOI4EventWeight, Text)]
findInStmts = concatMap findInStmt

addEventSource :: (HOI4EventWeight -> HOI4EventSource) -> [(HOI4EventWeight, Text)] -> [(Text, HOI4EventSource)]
addEventSource es = map (\t -> (snd t, es (fst t)))

findInOptions :: Text -> [HOI4Option] -> [(Text, HOI4EventSource)]
findInOptions eventId = concatMap (\o ->
    (\optName -> addEventSource (const (HOI4EvtSrcOption eventId optName)) (maybe [] (concatMap findInStmt) (hoi4opt_effects o)))
    (fromMaybe "(Un-named option)" (hoi4opt_name o))
    )

addEventTriggers :: HOI4EventTriggers -> [(Text, HOI4EventSource)] -> HOI4EventTriggers
addEventTriggers hm l = foldl' ins hm l
    where
        ins :: HOI4EventTriggers -> (Text, HOI4EventSource) -> HOI4EventTriggers
        ins hm (k, v) = HM.alter (\case
            Just l -> Just $ l ++ [v]
            Nothing -> Just [v]) k hm

findTriggeredEventsInEvents :: HOI4EventTriggers -> [HOI4Event] -> HOI4EventTriggers
findTriggeredEventsInEvents hm evts = addEventTriggers hm (concatMap findInEvent evts)
    where
        findInEvent :: HOI4Event -> [(Text, HOI4EventSource)]
        findInEvent evt@HOI4Event{hoi4evt_id = Just eventId} =
            (case hoi4evt_options evt of
                Just opts -> findInOptions eventId opts
                _ -> []) ++
            addEventSource (const (HOI4EvtSrcImmediate eventId)) (maybe [] findInStmts (hoi4evt_immediate evt))
        findInEvent _ = []

findTriggeredEventsInDecisions :: HOI4EventTriggers -> [HOI4Decision] -> HOI4EventTriggers
findTriggeredEventsInDecisions hm ds = addEventTriggers hm (concatMap findInDecision ds)
    where
        findInDecision :: HOI4Decision -> [(Text, HOI4EventSource)]
        findInDecision d =
            addEventSource (const (HOI4EvtSrcDecComplete (dec_name d) (dec_name_loc d))) (maybe [] findInStmts (dec_complete_effect d)) ++
            addEventSource (const (HOI4EvtSrcDecRemove (dec_name d) (dec_name_loc d))) (maybe [] findInStmts (dec_remove_effect d)) ++
            addEventSource (const (HOI4EvtSrcDecCancel (dec_name d) (dec_name_loc d))) (maybe [] findInStmts (dec_cancel_effect d)) ++
            addEventSource (const (HOI4EvtSrcDecTimeout (dec_name d) (dec_name_loc d))) (maybe [] findInStmts (dec_timeout_effect d))

findTriggeredEventsInOnActions :: HOI4EventTriggers -> [GenericStatement] -> HOI4EventTriggers
findTriggeredEventsInOnActions hm scr = foldl' findInAction hm scr -- needs editing
    where
        findInAction :: HOI4EventTriggers -> GenericStatement -> HOI4EventTriggers
        findInAction hm [pdx|on_actions = @stmts |] = foldl' findInAction hm stmts
        findInAction hm stmt@[pdx| $lhs = @scr |] = addEventTriggers hm (addEventSource (HOI4EvtSrcOnAction lhs) (findInStmts scr))
        findInAction hm stmt = trace ("Unknown on_actions statement: " ++ show stmt) hm


findTriggeredEventsInNationalFocus :: HOI4EventTriggers -> [HOI4NationalFocus] -> HOI4EventTriggers
findTriggeredEventsInNationalFocus hm nf = addEventTriggers hm (concatMap findInFocus nf)
    where
        findInFocus :: HOI4NationalFocus -> [(Text, HOI4EventSource)]
        findInFocus f =
            addEventSource (const (HOI4EvtSrcNFComplete (nf_id f) (nf_name_loc f) (nf_icon f))) (maybe [] findInStmts (nf_completion_reward f)) ++
            addEventSource (const (HOI4EvtSrcNFSelect (nf_id f) (nf_name_loc f) (nf_icon f))) (maybe [] findInStmts (nf_select_effect f))

findTriggeredEventsInIdeas :: HOI4EventTriggers -> [HOI4Idea] -> HOI4EventTriggers
findTriggeredEventsInIdeas hm idea = addEventTriggers hm (concatMap findInIdea idea)
    where
        findInIdea :: HOI4Idea -> [(Text, HOI4EventSource)]
        findInIdea idea =
            addEventSource (const (HOI4EvtSrcIdeaOnAdd (id_id idea) (id_name_loc idea) (id_picture idea) (id_category idea))) (maybe [] findInStmts (id_on_add idea)) ++
            addEventSource (const (HOI4EvtSrcIdeaOnRemove (id_id idea) (id_name_loc idea) (id_picture idea) (id_category idea))) (maybe [] findInStmts (id_on_remove idea))

findTriggeredEventsInCharacters :: HOI4EventTriggers -> [HOI4Character] -> HOI4EventTriggers
findTriggeredEventsInCharacters hm hChar = addEventTriggers hm (concatMap findInCharacter hChar)
    where
        findInCharacter :: HOI4Character -> [(Text, HOI4EventSource)]
        findInCharacter hChar =
            addEventSource (const (HOI4EvtSrcCharacterOnAdd (chaTag hChar) (chaName hChar))) (maybe [] findInStmts (chaOn_add hChar)) ++
            addEventSource (const (HOI4EvtSrcCharacterOnRemove (chaTag hChar) (chaName hChar))) (maybe [] findInStmts (chaOn_remove hChar))

findTriggeredEventsInScriptedEffects :: HOI4EventTriggers -> [GenericStatement] -> HOI4EventTriggers
findTriggeredEventsInScriptedEffects hm scr = foldl' findInScriptEffect hm scr -- needs editing
    where
        findInScriptEffect :: HOI4EventTriggers -> GenericStatement -> HOI4EventTriggers
        findInScriptEffect hm stmt@[pdx| $lhs = @scr |] = addEventTriggers hm (addEventSource (HOI4EvtSrcScriptedEffect lhs) (findInStmts scr))
        findInScriptEffect hm stmt = trace ("Unknown on_actions statement: " ++ show stmt) hm

findTriggeredEventsInBops :: HOI4EventTriggers -> [HOI4BopRange] -> HOI4EventTriggers
findTriggeredEventsInBops hm hBop = addEventTriggers hm (concatMap findInCharacter hBop)
    where
        findInCharacter :: HOI4BopRange -> [(Text, HOI4EventSource)]
        findInCharacter hBop =
            addEventSource (const (HOI4EvtSrcBopOnActivate (bop_id hBop))) (maybe [] findInStmts (bop_on_activate hBop)) ++
            addEventSource (const (HOI4EvtSrcBopOnDeactivate (bop_id hBop))) (maybe [] findInStmts (bop_on_deactivate hBop))