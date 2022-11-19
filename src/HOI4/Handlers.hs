{-# LANGUAGE LambdaCase #-}
module HOI4.Handlers (
        preStatement
    ,   plainStatement
    ,   plainMsg
    ,   plainMsg'
    ,   msgToPP
    ,   msgToPP'
    ,   flagText
    ,   isTag
    ,   getStateLoc
    ,   ppMtth
    ,   compound
    ,   compoundMessage
    ,   compoundMessageExtractTag
    ,   compoundMessageExtract
    ,   compoundMessageExtractNum
    ,   compoundMessagePronoun
    ,   compoundMessageTagged
    ,   withLocAtom
    ,   withLocAtom'
    ,   withLocAtomCompound
    ,   withLocAtomKey
    ,   withLocAtom2
    ,   withLocAtomIcon
    ,   withLocAtomIconHOI4Scope
    ,   locAtomTagOrState
    ,   withState
    ,   withNonlocAtom
    ,   withNonlocAtom2
    ,   withNonlocTextValue
    ,   iconOrFlag
    ,   tagOrState
    ,   tagOrStateIcon
    ,   numeric
    ,   numericCompare
    ,   numericCompareCompound
    ,   numericCompareCompoundLoc
    ,   numericOrTag
    ,   numericOrTagIcon
    ,   numericIconChange
    ,   withFlag
    ,   withFlagAndTag
    ,   withBool
    ,   withBoolHOI4Scope
    ,   withFlagOrBool
    ,   withTagOrNumber
    ,   numericIcon
    ,   numericIconLoc
    ,   numericLoc
    ,   boolIconLoc
    ,   tryLoc
    ,   tryLocAndIcon
    ,   tryLocMaybe
    ,   textValue
    ,   textValueKey
    ,   textValueCompare
    ,   valueValue
    ,   textAtom
    ,   textAtomKey
    ,   taDescAtomIcon
    ,   taTypeFlag
    ,   simpleEffectNum
    ,   simpleEffectAtom
    ,   ppAiWillDo
    ,   ppAiMod
    ,   opinion
    ,   hasOpinion
    ,   triggerEvent
    ,   random
    ,   randomList
    ,   hasDlc
    ,   withFlagOrState
    ,   customTriggerTooltip
    ,   handleFocus
    ,   focusUncomplete
    ,   focusProgress
    ,   setVariable
    ,   clampVariable
    ,   checkVariable
    ,   rhsAlways
    ,   rhsAlwaysYes
    ,   rhsIgnored
    ,   rhsAlwaysEmptyCompound
    ,   exportVariable
--    ,   aiAttitude
    ,   addBuildingConstruction
    ,   setBuildingLevel
    ,   addNamedThreat
    ,   createWargoal
    ,   declareWarOn
    ,   annexCountry
    ,   addTechBonus
    ,   setFlag
    ,   hasFlag
    ,   addToWar
    ,   setAutonomy
    ,   setPolitics
    ,   hasCountryLeader
    ,   setPartyName
    ,   loadFocusTree
    ,   setNationality
    ,   prioritize
    ,   hasWarGoalAgainst
    ,   diplomaticRelation
    ,   hasArmySize
    ,   startCivilWar
    ,   createEquipmentVariant
    ,   setRule
    ,   addDoctrineCostReduction
    ,   freeBuildingSlots
    ,   addAutonomyRatio
    ,   sendEquipment
    ,   buildRailway
    ,   canBuildRailway
    ,   addResource
    ,   modifyBuildingResources
    ,   handleDate
    ,   setTechnology
    ,   setCapital
    ,   setPopularities
    ,   addEquipment
    ,   giveResourceRights
    ,   addAce
    ,   divisionTemplate
    ,   hasNavySize
    ,   locandid
    ,   createUnit
    ,   damageBuilding
    ,   withRegion
    ,   divisionsInState
    ,   deleteUnits
    ,   startBorderWar
    ,   addProvinceModifier
    ,   powerBalanceRange
    ,   navalStrengthComparison
    ,   unlockDecisionTooltip
    -- testing
    ,   isPronoun
    ,   flag
    ,   eGetState
    --specialhandler exports
    ,   TextAtom(..)
    ,   TextValue(..)
    ,   parseTA
    ,   parseTV
    ,   eflag
    ) where

import Data.Char (toUpper, toLower, isUpper, isDigit)
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Encoding as TE

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
--import Data.Set (Set)
import qualified Data.Set as S
import Data.Trie (Trie)
import qualified Data.Trie as Tr

import qualified Text.PrettyPrint.Leijen.Text as PP

import Data.List (foldl', intersperse, intercalate, findIndex)
import Data.Maybe

import Control.Applicative (liftA2)
import Control.Arrow (first)
import Control.Monad (foldM, mplus, forM, join, when)
import Data.Foldable (fold)
import Data.Monoid ((<>))

import Abstract -- everything
import Doc (Doc)
import qualified Doc -- everything
import HOI4.Messages -- everything
import MessageTools (plural, iquotes, italicText, boldText, typewriterText
                    , plainNum, colourNumSign, plainNumSign, plainPc, colourPc, reducedNum
                    , formatDays, formatHours)
import QQ -- everything
import SettingsTypes ( PPT, IsGameData (..), GameData (..), IsGameState (..), GameState (..)
                     , indentUp, indentDown, getCurrentIndent, withCurrentIndent, withCurrentIndentZero, withCurrentIndentCustom, alsoIndent, alsoIndent'
                     , getGameL10n, getGameL10nIfPresent, getGameL10nDefault, withCurrentFile
                     , unfoldM, unsnoc )
import HOI4.Templates
import {-# SOURCE #-} HOI4.Common (ppScript, ppMany, ppOne, extractStmt, matchLhsText)
import HOI4.Types -- everything

import Debug.Trace
import System.Win32.SimpleMAPI (defMessage)

-- | Pretty-print a script statement, wrap it in a @<pre>@ element, and emit a
-- generic message for it at the current indentation level. This is the
-- fallback in case we haven't implemented that particular statement or we
-- failed to understand it.
--
-- Will now try to recurse into nested clauses as they break the wiki layout, and
-- it might be possible to "recover".
preStatement :: (HOI4Info g, Monad m) =>
    GenericStatement -> PPT g m IndentedMessages
preStatement [pdx| %lhs = @scr |] = do
    headerMsg <- plainMsg' $ "<pre>" <> Doc.doc2text (lhs2doc (const "") lhs) <> "</pre>"
    msgs <- ppMany scr
    return (headerMsg : msgs)
preStatement stmt = (:[]) <$> alsoIndent' (preMessage stmt)

-- | For pretty printing a simple statement without <pre>
plainStatement :: (HOI4Info g, Monad m) =>
    Text -> GenericStatement -> PPT g m IndentedMessages
plainStatement xtxt stmt =
    plainMsg $ xtxt <> "<tt>" <> Doc.doc2text (genericStatement2doc stmt) <> "</tt>"

-- | Pretty-print a statement and wrap it in a @<pre>@ element.
preStatementText :: GenericStatement -> Doc
preStatementText stmt = "<pre>" <> genericStatement2doc stmt <> "</pre>"

-- | 'Text' version of 'preStatementText'.
preStatementText' :: GenericStatement -> Text
preStatementText' = Doc.doc2text . preStatementText

-- | Pretty-print a script statement, wrap it in a @<pre>@ element, and emit a
-- generic message for it.
preMessage :: GenericStatement -> ScriptMessage
preMessage = MsgUnprocessed
            . TL.toStrict
            . PP.displayT
            . PP.renderPretty 0.8 80 -- Don't use 'Doc.doc2text', because it uses
                                     -- 'Doc.renderCompact' which is not what
                                     -- we want here.
            . preStatementText

-- | Create a generic message from a piece of text. The rendering function will
-- pass this through unaltered.
plainMsg :: (IsGameState (GameState g), Monad m) => Text -> PPT g m IndentedMessages
plainMsg msg = (:[]) <$> plainMsg' msg

plainMsg' :: (IsGameState (GameState g), Monad m) => Text -> PPT g m IndentedMessage
plainMsg' = alsoIndent' . MsgUnprocessed

msgToPP :: (IsGameState (GameState g), Monad m) => ScriptMessage -> PPT g m IndentedMessages
msgToPP msg = (:[]) <$> msgToPP' msg

msgToPP' :: (IsGameState (GameState g), Monad m) => ScriptMessage -> PPT g m IndentedMessage
msgToPP' = alsoIndent'

-- Emit icon template.
icon :: Text -> Doc
icon what = case HM.lookup what scriptIconFileTable of
    Just "" -> Doc.strictText $ "[[File:" <> what <> ".png|28px]]" -- shorthand notation
    Just file -> Doc.strictText $ "[[File:" <> file <> ".png|28px]]"
    _ ->  if isPronoun what then
            ""
        else
            template "icon" [HM.findWithDefault what what scriptIconTable]
iconText :: Text -> Text
iconText = Doc.doc2text . icon

-- Argument may be a tag or a tagged variable. Emit a flag in the former case,
-- and localize in the latter case.
eflag :: (HOI4Info g, Monad m) =>
            Maybe HOI4Scope -> Either Text (Text, Text) -> PPT g m (Maybe Text)
eflag expectScope = \case
    Left name -> Just <$> flagText expectScope name
    Right (vartag, var) -> tagged vartag var

-- | Look up the message corresponding to a tagged atom.
--
-- For example, to localize @event_target:some_name@, call
-- @tagged "event_target" "some_name"@.
tagged :: (HOI4Info g, Monad m) =>
    Text -> Text -> PPT g m (Maybe Text)
tagged vartag var = case flip Tr.lookup varTags . TE.encodeUtf8 $ vartag of
    Just msg -> Just <$> messageText (msg var)
    Nothing -> return $ Just $ "<tt>" <> vartag <> ":" <> var <> "</tt>" -- just let it pass

flagText :: (HOI4Info g, Monad m) =>
    Maybe HOI4Scope -> Text -> PPT g m Text
flagText expectScope = fmap Doc.doc2text . flag expectScope

-- Emit an appropriate phrase if the given text is a pronoun, otherwise use the
-- provided localization function.
allowPronoun :: (HOI4Info g, Monad m) =>
    Maybe HOI4Scope -> (Text -> PPT g m Doc) -> Text -> PPT g m Doc
allowPronoun expectedScope getLoc name =
    if isPronoun name
        then pronoun expectedScope name
        else getLoc name

-- | Emit flag template if the argument is a tag, or an appropriate phrase if
-- it's a pronoun.
flag :: (HOI4Info g, Monad m) =>
    Maybe HOI4Scope -> Text -> PPT g m Doc
flag expectscope = allowPronoun expectscope $ \name -> do
                    nameIdeo <- getCoHi name
                    template "flag" . (:[]) <$> getGameL10n nameIdeo

getCoHi :: (Monad m, HOI4Info g) =>
    Text -> PPT g m Text
getCoHi name = do
    chistories <- getCountryHistory
    let mchistories = HM.lookup name chistories
    case mchistories of
        Nothing -> return name
        Just chistory -> do
            rulLoc <- getGameL10nIfPresent (chRulingTag chistory)
            case rulLoc of
                Just rulingTag -> return $ chRulingTag chistory
                Nothing -> return name

-- | Emit an appropriate phrase for a pronoun.
-- If a scope is passed, that is the type the current command expects. If they
-- don't match, it's a synecdoche; adjust the wording appropriately.
--
-- All handlers in this module that take an argument of type 'Maybe HOI4Scope'
-- call this function. Use whichever scope corresponds to what you expect to
-- appear on the RHS. If it can be one of several (e.g. either a country or a
-- province), use HOI4From. If it doesn't correspond to any scope, use Nothing.
pronoun :: (HOI4Info g, Monad m) =>
    Maybe HOI4Scope -> Text -> PPT g m Doc
pronoun expectedScope name = withCurrentFile $ \f -> case T.toLower name of
    "root" -> message MsgROOTCountry--getRootScope >>= \case -- will need editing
        --Just HOI4Country
            -- \| expectedScope `matchScope` HOI4Country -> message MsgROOTCountry
            -- \| otherwise                             -> return "ROOT"
        --Just HOI4ScopeState
            -- \| expectedScope `matchScope` HOI4ScopeState -> message MsgROOTState
            -- \| otherwise                             -> return "ROOT"
        --Just HOI4UnitLeader
            -- \| expectedScope `matchScope` HOI4UnitLeader -> message MsgROOTUnitLeader
            -- \| otherwise                             -> return "ROOT"
        --Just HOI4Operative
            -- \| expectedScope `matchScope` HOI4Operative -> message MsgROOTOperative
            -- \| otherwise                             -> return "ROOT"
        --_ -> return "ROOT"
    "prev" -> --do
--      ss <- getScopeStack
--      traceM (f ++ ": pronoun PREV: scope stack is " ++ show ss)
        getPrevScope >>= \case -- will need editing
            Just HOI4Country
                | expectedScope `matchScope` HOI4Country -> message MsgPREVCountry
                | otherwise                             -> return "PREV"
            Just HOI4ScopeState
                | expectedScope `matchScope` HOI4ScopeState -> message MsgPREVState
                | otherwise                             -> return "PREV"
            Just HOI4UnitLeader
                | expectedScope `matchScope` HOI4UnitLeader -> message MsgPREVUnitLeader
                | otherwise                             -> return "PREV"
            Just HOI4Operative
                | expectedScope `matchScope` HOI4Operative -> message MsgPREVOperative
                | otherwise                             -> return "PREV"
            Just HOI4ScopeCharacter
                | expectedScope `matchScope` HOI4ScopeCharacter -> message MsgPREVCharacter
                | otherwise                             -> return "PREV"
            Just HOI4Division
                | expectedScope `matchScope` HOI4Division -> message MsgPREVDivision
                | otherwise                             -> return "PREV"
            Just HOI4From -> message MsgPREVFROM
            Just HOI4Misc -> message MsgMISC
            Just HOI4Custom -> message MsgPREVCustom
            _ -> return "PREV"
    "this" -> getCurrentScope >>= \case -- will need editing
        Just HOI4Country
            | expectedScope `matchScope` HOI4Country -> message MsgTHISCountry
            | otherwise                             -> return "THIS"
        Just HOI4ScopeState
            | expectedScope `matchScope` HOI4ScopeState -> message MsgTHISState
            | otherwise                             -> return "THIS"
        Just HOI4UnitLeader
            | expectedScope `matchScope` HOI4UnitLeader -> message MsgTHISUnitLeader
            | otherwise                             -> return "THIS"
        Just HOI4Operative
            | expectedScope `matchScope` HOI4Operative -> message MsgTHISOperative
            | otherwise                             -> return "THIS"
        Just HOI4ScopeCharacter
            | expectedScope `matchScope` HOI4ScopeCharacter -> message MsgTHISCharacter
            | otherwise                             -> return "THIS"
        Just HOI4Division
            | expectedScope `matchScope` HOI4Division -> message MsgTHISDivision
            | otherwise                             -> return "THIS"
        Just HOI4Misc -> message MsgMISC
        Just HOI4Custom -> message MsgPREVCustom
        _ -> return "THIS"
    "overlord" -> message MsgOverlord
    "faction_leader" -> message MsgFactionLeader
    "owner" -> getCurrentScope >>= \case
        Just HOI4ScopeState -> message MsgOwnerState
        Just HOI4UnitLeader -> message MsgOwnerUnit
        Just HOI4Operative -> message MsgOwnerUnit
        Just HOI4ScopeCharacter -> message MsgOwnerUnit
        _ -> message MsgOwner
    "controller" -> message MsgController
    "capital_scope" -> message MsgCapital
    "from" -> message MsgFROM -- TODO: Handle this properly (if possible)
    proscope
        | any (`T.isSuffixOf` proscope) [".overlord",".OVERLORD",".Overlord"] -> do
            let labelstrip
                    | ".overlord" `T.isSuffixOf` proscope = fromMaybe "<!--CHECK SCRIPT-->" (T.stripSuffix ".overlord" proscope)
                    | ".Overlord" `T.isSuffixOf` proscope = fromMaybe "<!--CHECK SCRIPT-->" (T.stripSuffix ".Overlord" proscope)
                    | ".OVERLORD" `T.isSuffixOf` proscope = fromMaybe "<!--CHECK SCRIPT-->" (T.stripSuffix ".OVERLORD" proscope)
                    | otherwise = proscope
                tagorpro = if T.length labelstrip == 3 then T.toUpper labelstrip else labelstrip
            tagloc <- do
                mflag <- eflag (Just HOI4Country) (Left tagorpro)
                return $ fromMaybe "<!--CHECK SCRIPT-->" mflag
            message $ MsgOverlordOf tagloc
        | any (`T.isSuffixOf` proscope) [".faction_leader",".FACTION_LEADER",".Faction_leader"] -> do
            let labelstrip
                    | ".faction_leader" `T.isSuffixOf` proscope = fromMaybe "<!--CHECK SCRIPT-->" (T.stripSuffix ".faction_leader" proscope)
                    | ".Faction_leader" `T.isSuffixOf` proscope = fromMaybe "<!--CHECK SCRIPT-->" (T.stripSuffix ".Faction_leader" proscope)
                    | ".FACTION_LEADER" `T.isSuffixOf` proscope = fromMaybe "<!--CHECK SCRIPT-->" (T.stripSuffix ".FACTION_LEADER" proscope)
                    | otherwise = proscope
                tagorpro = if T.length labelstrip == 3 then T.toUpper labelstrip else labelstrip
            tagloc <- do
                mflag <- eflag (Just HOI4Country) (Left tagorpro)
                return $ fromMaybe "<!--CHECK SCRIPT-->" mflag
            message $ MsgFactionLeaderOf tagloc
        | any (`T.isSuffixOf` proscope) [".owner",".OWNER",".Owner"] -> do
            let labelstrip
                    | ".owner" `T.isSuffixOf` proscope = fromMaybe "<!--CHECK SCRIPT-->" (T.stripSuffix ".owner" proscope)
                    | ".Owner" `T.isSuffixOf` proscope = fromMaybe "<!--CHECK SCRIPT-->" (T.stripSuffix ".Owner" proscope)
                    | ".OWNER" `T.isSuffixOf` proscope = fromMaybe "<!--CHECK SCRIPT-->" (T.stripSuffix ".OWNER" proscope)
                    | otherwise = proscope
            stateloc <-
                if all isDigit $ T.unpack labelstrip
                then getStateLoc $ read (T.unpack labelstrip)
                else do
                mstate <- eGetState (Left labelstrip)
                return $ fromMaybe "<!--CHECK SCRIPT-->" mstate
            message $ MsgOwnerOf stateloc
        | any (`T.isSuffixOf` proscope) [".controller",".CONTROLLER",".Controller"] -> do
            let labelstrip
                    | ".controller" `T.isSuffixOf` proscope = fromMaybe "<!--CHECK SCRIPT-->" (T.stripSuffix ".controller" proscope)
                    | ".Controller" `T.isSuffixOf` proscope = fromMaybe "<!--CHECK SCRIPT-->" (T.stripSuffix ".Controller" proscope)
                    | ".CONTROLLER" `T.isSuffixOf` proscope = fromMaybe "<!--CHECK SCRIPT-->" (T.stripSuffix ".CONTROLLER" proscope)
                    | otherwise = proscope
            stateloc <-
                if all isDigit $ T.unpack labelstrip
                then getStateLoc $ read (T.unpack labelstrip)
                else do
                mstate <- eGetState (Left labelstrip)
                return $ fromMaybe "<!--CHECK SCRIPT-->" mstate
            message $ MsgControllerOf stateloc
        | otherwise -> return $ Doc.strictText name -- something else; regurgitate untouched
    where
        Nothing `matchScope` _ = True
        Just expect `matchScope` actual
            | expect == actual = True
            | otherwise        = False

isTag :: Text -> Bool
isTag s = T.length s == 3 && T.all isUpper s

-- Tagged messages
varTags :: Trie (Text -> ScriptMessage)
varTags = Tr.fromList . map (first TE.encodeUtf8) $
    [("event_target", MsgEventTargetVar)
    ,("var"         , MsgVariable)
    ]

isPronoun :: Text -> Bool
isPronoun s = T.map toLower s `S.member` pronouns || (\ls -> ".owner" `T.isSuffixOf` ls || ".controller" `T.isSuffixOf` ls || ".faction_leader" `T.isSuffixOf` ls || ".overlord" `T.isSuffixOf` ls || ".prev" `T.isSuffixOf` ls || ".from" `T.isSuffixOf` ls) (T.toLower s)
    where
        pronouns = S.fromList
            ["root"
            ,"prev"
            ,"this"
            ,"from"
            ,"overlord"
            ,"faction_leader"
            ,"owner"
            ,"controller"
            ,"capital_scope"
            ]

-- Get the localization for a state ID, if available.
getStateLoc :: (IsGameData (GameData g), Monad m) =>
    Int -> PPT g m Text
getStateLoc n = do
    let stateid_t = T.pack (show n)
    mstateloc <- getGameL10nIfPresent ("STATE_" <> stateid_t)
    return $ case mstateloc of
        Just loc -> boldText loc <> " (" <> stateid_t <> ")"
        _ -> "State" <> stateid_t

eGetState :: (HOI4Info g, Monad m) =>
             Either Text (Text, Text) -> PPT g m (Maybe Text)
eGetState = \case
    Left name -> do
        pronouned <- pronoun (Just HOI4ScopeState) name
        let pronountext = Doc.doc2text pronouned
        return $ Just pronountext
    Right (vartag, var) -> tagged vartag var

-----------------------------------------------------------------
-- Script handlers that should be used directly, not via ppOne --
-----------------------------------------------------------------

-- | Data for @mean_time_to_happen@ clauses
data MTTH = MTTH
        {   mtth_years :: Maybe Int
        ,   mtth_months :: Maybe Int
        ,   mtth_days :: Maybe Int
        ,   mtth_modifiers :: [MTTHModifier]
        } deriving Show
-- | Data for @modifier@ clauses within @mean_time_to_happen@ clauses
data MTTHModifier = MTTHModifier
        {   mtthmod_factor :: Maybe Double
        ,   mtthmod_conditions :: GenericScript
        } deriving Show
-- | Empty MTTH
newMTTH :: MTTH
newMTTH = MTTH Nothing Nothing Nothing []
-- | Empty MTTH modifier
newMTTHMod :: MTTHModifier
newMTTHMod = MTTHModifier Nothing []

-- | Format a @mean_time_to_happen@ clause as wiki text.
ppMtth :: (HOI4Info g, Monad m) => Bool -> GenericScript -> PPT g m Doc
ppMtth isTriggeredOnly = ppMtth' . foldl' addField newMTTH
    where
        addField mtth [pdx| years    = !n   |] = mtth { mtth_years = Just n }
        addField mtth [pdx| months   = !n   |] = mtth { mtth_months = Just n }
        addField mtth [pdx| days     = !n   |] = mtth { mtth_days = Just n }
        addField mtth [pdx| modifier = @rhs |] = addMTTHMod mtth rhs
        addField mtth _ = mtth -- unrecognized
        addMTTHMod mtth scr = mtth {
                mtth_modifiers = mtth_modifiers mtth
                                 ++ [foldl' addMTTHModField newMTTHMod scr] } where
            addMTTHModField mtthmod [pdx| factor = !n |]
                = mtthmod { mtthmod_factor = Just n }
            addMTTHModField mtthmod stmt -- anything else is a condition
                = mtthmod { mtthmod_conditions = mtthmod_conditions mtthmod ++ [stmt] }
        ppMtth' (MTTH myears mmonths mdays modifiers) = do
            modifiers_pp'd <- intersperse PP.line <$> mapM pp_mtthmod modifiers
            let hasYears = isJust myears
                hasMonths = isJust mmonths
                hasDays = isJust mdays
                hasModifiers = not (null modifiers)
            return . mconcat $ (if isTriggeredOnly then [] else
                maybe []
                    (\years ->
                        [PP.int years, PP.space, Doc.strictText $ plural years "year" "years"]
                        ++
                        if hasMonths && hasDays then [",", PP.space]
                        else if hasMonths || hasDays then ["and", PP.space]
                        else [])
                    myears
                ++
                maybe []
                    (\months -> [PP.int months, PP.space, Doc.strictText $ plural months "month" "months"])
                    mmonths
                ++
                maybe []
                    (\days ->
                        (if hasYears && hasMonths then ["and", PP.space]
                         else []) -- if years but no months, already added "and"
                        ++
                        [PP.int days, PP.space, Doc.strictText $ plural days "day" "days"])
                    mdays
                ) ++
                (if hasModifiers then
                    (if isTriggeredOnly then
                        [PP.line, "'''Weight modifiers'''", PP.line]
                    else
                        [PP.line, "<br/>'''Modifiers'''", PP.line])
                    ++ modifiers_pp'd
                 else [])
        pp_mtthmod (MTTHModifier (Just factor) conditions) =
            case conditions of
                [_] -> do
                    conditions_pp'd <- ppScript conditions
                    return . mconcat $
                        [conditions_pp'd
                        ,PP.enclose ": '''×" "'''" (Doc.ppFloat factor)
                        ]
                _ -> do
                    conditions_pp'd <- indentUp (ppScript conditions)
                    return . mconcat $
                        ["*"
                        ,PP.enclose "'''×" "''':" (Doc.ppFloat factor)
                        ,PP.line
                        ,conditions_pp'd
                        ]
        pp_mtthmod (MTTHModifier Nothing _)
            = return "(invalid modifier! Bug in extractor?)"

--------------------------------
-- General statement handlers --
--------------------------------

-- | Generic handler for a simple compound statement. Usually you should use
-- 'compoundMessage' instead so the text can be localized.
compound :: (HOI4Info g, Monad m) =>
    Text -- ^ Text to use as the block header, without the trailing colon
    -> StatementHandler g m
compound header [pdx| %_ = @scr |]
    = withCurrentIndent $ \_ -> do -- force indent level at least 1
        headerMsg <- plainMsg (header <> ":")
        scriptMsgs <- ppMany scr
        return $ headerMsg ++ scriptMsgs
compound _ stmt = preStatement stmt

-- | Generic handler for a simple compound statement.
compoundMessage :: (HOI4Info g, Monad m) =>
    ScriptMessage -- ^ Message to use as the block header
    -> StatementHandler g m
compoundMessage header [pdx| %_ = @scr |]
    = withCurrentIndent $ \i -> do
        script_pp'd <- ppMany scr
        return ((i, header) : script_pp'd)
compoundMessage _ stmt = preStatement stmt

-- | Generic handler for a simple compound statement with extra info.
compoundMessageExtractTag :: (HOI4Info g, Monad m) =>
    Text
    -> (Text -> ScriptMessage) -- ^ Message to use as the block header
    -> StatementHandler g m
compoundMessageExtractTag xtract header [pdx| %_ = @scr |]
    = withCurrentIndent $ \i -> do
        let (xtracted, rest) = extractStmt (matchLhsText xtract) scr
        xtractflag <- case xtracted of
                Just [pdx| %_ = $vartag:$var |] -> eflag (Just HOI4Country) (Right (vartag, var))
                Just [pdx| %_ = $flag |] -> eflag (Just HOI4Country) (Left flag)
                _ -> return Nothing
        let flagd = case xtractflag of
                Just flag -> flag
                _ -> "<!-- Check Script -->"
        script_pp'd <- ppMany rest
        return ((i, header flagd) : script_pp'd)
compoundMessageExtractTag _ _ stmt = preStatement stmt

compoundMessageExtract :: (HOI4Info g, Monad m) =>
    Text
    -> (Text -> ScriptMessage) -- ^ Message to use as the block header
    -> StatementHandler g m
compoundMessageExtract xtract header [pdx| %_ = @scr |]
    = withCurrentIndent $ \i -> do
        let (mxtracted, rest) = extractStmt (matchLhsText xtract) scr
            xtracted = case mxtracted of
                Just [pdx| %_ = $txt |] -> txt
                _-> "<!-- Check game Script -->"
        script_pp'd <- ppMany rest
        return ((i, header xtracted) : script_pp'd)
compoundMessageExtract _ _ stmt = preStatement stmt

compoundMessageExtractNum :: (HOI4Info g, Monad m) =>
    Text
    -> (Double -> ScriptMessage) -- ^ Message to use as the block header
    -> StatementHandler g m
compoundMessageExtractNum xtract header stmt@[pdx| %_ = @scr |]
    = withCurrentIndent $ \i -> do
        let (mxtracted, rest) = extractStmt (matchLhsText xtract) scr
        case mxtracted of
            Just [pdx| %_ = !num |] -> do
                script_pp'd <- ppMany rest
                return ((i, header num) : script_pp'd)
            _-> preStatement stmt
compoundMessageExtractNum _ _ stmt = preStatement stmt

-- | Generic handler for a simple compound statement headed by a pronoun.
compoundMessagePronoun :: (HOI4Info g, Monad m) => StatementHandler g m
compoundMessagePronoun stmt@[pdx| $head = @scr |] = withCurrentIndent $ \i -> do
    params <- withCurrentFile $ \f -> case T.toLower head of
        "root" -> --do --ROOT
                --newscope <- getRootScope
                return (Just HOI4Country, Just MsgROOTSCOPECountry) --case newscope of
                    --Just HOI4Country -> Just MsgROOTSCOPECountry
                    --Just HOI4ScopeCharacter -> Just MsgROOTSCOPECharacter
                    --Just HOI4Operative -> Just MsgROOTSCOPEOperative
                    --Just HOI4ScopeState -> Just MsgROOTSCOPEState
                    --Just HOI4UnitLeader -> Just MsgROOTSCOPEUnitLeader
                    --_ -> Nothing) -- warning printed below
        "prev" -> do --PREV
                newscope <- getPrevScope
                return (newscope, case newscope of
                    Just HOI4Country -> Just MsgPREVSCOPECountry
                    Just HOI4ScopeCharacter -> Just MsgPREVSCOPECharacter
                    Just HOI4Operative -> Just MsgPREVSCOPEOperative
                    Just HOI4ScopeState -> Just MsgPREVSCOPEState
                    Just HOI4UnitLeader -> Just MsgPREVSCOPEUnitLeader
                    Just HOI4Misc -> Just MsgPREVSCOPEMisc
                    Just HOI4From -> Just MsgPREVSCOPEFROM -- Roll with it
                    Just HOI4Custom -> Just MsgPREVSCOPECustom
                    Nothing -> Just MsgPREVSCOPECustom2
                    _ -> Nothing) -- warning printed below
        "prev.prev" -> do --PREV
                newscope <- getPrevScopeCustom 2
                return (newscope, Just MsgPREVPREV)
        "prev.prev.prev" -> do --PREV
                newscope <- getPrevScopeCustom 3
                return (newscope, Just MsgPREVPREVPREV)
        "owner" -> do --PREV
                newscope <- getCurrentScope
                return (Just HOI4Country, case newscope of
                    Just HOI4ScopeState -> Just MsgOwnerStateSCOPE
                    Just HOI4ScopeCharacter -> Just MsgOwnerUnitSCOPE
                    Just HOI4UnitLeader -> Just MsgOwnerUnitSCOPE
                    Just HOI4Operative -> Just MsgOwnerUnitSCOPE
                    _ -> Just MsgOwnerSCOPE)
        "from" -> return (Just HOI4From, Just MsgFROMSCOPE) -- FROM / Should be some way to have different message depending on if it is event or decison, etc.
        "from.from" -> return (Just HOI4From, Just MsgFROMFROMSCOPE)
        "from.from.from" -> return (Just HOI4From, Just MsgFROMFROMFROMSCOPE)
        _ -> trace (f ++ ": compoundMessagePronoun: don't know how to handle head " ++ T.unpack head)
             $ return (Nothing, undefined)
    case params of
        (Just newscope, Just scopemsg) -> do
            script_pp'd <- scope newscope $ ppMany scr
            return $ (i, scopemsg) : script_pp'd
        (Nothing, Just scopemsg) -> do
            script_pp'd <- scope HOI4Custom $ ppMany scr
            return $ (i, scopemsg) : script_pp'd
        _ -> do
            withCurrentFile $ \f -> do
                traceM $ "compoundMessagePronoun: " ++ f ++ ": potentially invalid use of " ++ T.unpack head ++ " in " ++ show stmt
            preStatement stmt
compoundMessagePronoun stmt = preStatement stmt

-- | Generic handler for a simple compound statement with a tagged header.
compoundMessageTagged :: (HOI4Info g, Monad m) =>
    (Text -> ScriptMessage) -- ^ Message to use as the block header
    -> Maybe HOI4Scope -- ^ Scope to push on the stack, if any
    -> StatementHandler g m
compoundMessageTagged header mscope stmt@[pdx| $_:$tag = %_ |]
    = maybe id scope mscope $ compoundMessage (header tag) stmt
compoundMessageTagged _ _ stmt = preStatement stmt

-- | Generic handler for a statement whose RHS is a localizable atom.
-- with the ability to transform the localization key
withLocAtom' :: (HOI4Info g, Monad m) =>
    (Text -> ScriptMessage) -> (Text -> Text) -> StatementHandler g m
withLocAtom' msg xform [pdx| %_ = ?key |]
    = msgToPP . msg =<< getGameL10n (xform key)
withLocAtom' _ _ stmt = preStatement stmt

-- | Generic handler for a statement whose RHS is a localizable atom.
withLocAtom :: (HOI4Info g, Monad m) =>
    (Text -> ScriptMessage)
    -> GenericStatement -> PPT g m IndentedMessages
withLocAtom msg = withLocAtom' msg id

withLocAtomCompound :: (HOI4Info g, Monad m) =>
    (Text -> ScriptMessage)
        -> StatementHandler g m
withLocAtomCompound msg stmt@[pdx| %_ = %rhs |] = case rhs of
    CompoundRhs [scr] -> withLocAtom msg scr
    _ -> preStatement stmt
withLocAtomCompound _ stmt = preStatement stmt

-- | Generic handler for a statement whose RHS is a localizable atom.
-- with the ability to transform the localization key
withLocAtomKey' :: (HOI4Info g, Monad m) =>
    (Text -> Text -> ScriptMessage) -> (Text -> Text) -> StatementHandler g m
withLocAtomKey' msg xform [pdx| %_ = ?key |]
    = msgToPP . msg key =<< getGameL10n (xform key)
withLocAtomKey' _ _ stmt = preStatement stmt

-- | Generic handler for a statement whose RHS is a localizable atom.
withLocAtomKey :: (HOI4Info g, Monad m) =>
    (Text -> Text -> ScriptMessage)
    -> GenericStatement -> PPT g m IndentedMessages
withLocAtomKey msg = withLocAtomKey' msg id

-- | Generic handler for a statement whose RHS is a localizable atom and we
-- need a second one (passed to message as first arg).
withLocAtom2 :: (HOI4Info g, Monad m) =>
    ScriptMessage
        -> (Text -> Text -> Text -> ScriptMessage)
        -> StatementHandler g m
withLocAtom2 inMsg msg [pdx| %_ = ?key |]
    = msgToPP =<< msg key <$> messageText inMsg <*> getGameL10n key
withLocAtom2 _ _ stmt = preStatement stmt

-- | Generic handler for a statement whose RHS is a localizable atom, where we
-- also need an icon.
withLocAtomAndIcon :: (HOI4Info g, Monad m) =>
    Text -- ^ icon name - see
         -- <https://www.hoi4wiki.com/Template:Icon Template:Icon> on the wiki
        -> (Text -> Text -> ScriptMessage)
        -> StatementHandler g m
withLocAtomAndIcon iconkey msg stmt@[pdx| %_ = $vartag:$var |] = do
    mtagloc <- tagged vartag var
    case mtagloc of
        Just tagloc -> msgToPP $ msg (iconText iconkey) tagloc
        Nothing -> preStatement stmt
withLocAtomAndIcon iconkey msg [pdx| %_ = ?key |]
    = do what <- Doc.doc2text <$> allowPronoun Nothing (fmap Doc.strictText . getGameL10n) key
         msgToPP $ msg (iconText iconkey) what
withLocAtomAndIcon _ _ stmt = preStatement stmt

-- | Generic handler for a statement whose RHS is a localizable atom that
-- corresponds to an icon.
withLocAtomIcon :: (HOI4Info g, Monad m) =>
    (Text -> Text -> ScriptMessage)
        -> StatementHandler g m
withLocAtomIcon msg stmt@[pdx| %_ = ?key |]
    = withLocAtomAndIcon key msg stmt
withLocAtomIcon _ stmt = preStatement stmt

-- | Generic handler for a statement that needs both an atom and an icon, whose
-- meaning changes depending on which scope it's in.
withLocAtomIconHOI4Scope :: (HOI4Info g, Monad m) =>
    (Text -> Text -> ScriptMessage) -- ^ Message for country scope
        -> (Text -> Text -> ScriptMessage) -- ^ Message for state scope
        -> StatementHandler g m
withLocAtomIconHOI4Scope countrymsg statemsg stmt = do
    thescope <- getCurrentScope
    case thescope of
        Just HOI4Country -> withLocAtomIcon countrymsg stmt
        Just HOI4ScopeState -> withLocAtomIcon statemsg stmt
        _ -> preStatement stmt -- others don't make sense

-- | Generic handler for a statement where the RHS is a localizable atom, but
-- may be replaced with a tag or state to refer synecdochally to the
-- corresponding value.
locAtomTagOrState :: (HOI4Info g, Monad m) =>
    (Text -> Text -> ScriptMessage) -- ^ Message for atom
        -> (Text -> ScriptMessage) -- ^ Message for synecdoche
        -> StatementHandler g m
locAtomTagOrState atomMsg synMsg stmt@[pdx| %_ = $val |] =
    if isTag val || isPronoun val
       then tagOrStateIcon synMsg synMsg stmt
       else withLocAtomIcon atomMsg stmt
locAtomTagOrState atomMsg synMsg stmt@[pdx| %_ = $vartag:$var |] = do
    mtagloc <- tagged vartag var
    case mtagloc of
        Just tagloc -> msgToPP $ synMsg tagloc
        Nothing -> preStatement stmt
-- Example: religion = variable:From:new_ruler_religion (TODO: Better handling)
locAtomTagOrState atomMsg synMsg stmt@[pdx| %_ = $a:$b:$c |] =
    msgToPP $ synMsg ("<tt>" <> a <> ":" <> b <> ":" <> c <> "</tt>")
locAtomTagOrState _ _ stmt = preStatement stmt -- CHECK FOR USEFULNESS

withState :: (HOI4Info g, Monad m) =>
    (Text -> ScriptMessage)
        -> StatementHandler g m
withState msg stmt@[pdx| %lhs = $vartag:$var |] = do
    mtagloc <- eGetState (Right (vartag, var))
    case mtagloc of
        Just tagloc -> msgToPP $ msg tagloc
        Nothing -> preStatement stmt
withState msg stmt@[pdx| %lhs = $var |] = do
    mtagloc <- eGetState (Left var)
    case mtagloc of
        Just tagloc -> msgToPP $ msg tagloc
        Nothing -> preStatement stmt
withState msg [pdx| %lhs = !stateid |]
    = msgToPP . msg =<< getStateLoc stateid
withState _ stmt = preStatement stmt

-- As withLocAtom but no l10n.
withNonlocAtom :: (HOI4Info g, Monad m) => (Text -> ScriptMessage) -> StatementHandler g m
withNonlocAtom msg [pdx| %_ = ?text |] = msgToPP $ msg text
withNonlocAtom _ stmt = preStatement stmt

-- | As withlocAtom but wth no l10n and an additional bit of text.
withNonlocAtom2 :: (HOI4Info g, Monad m) =>
    ScriptMessage
        -> (Text -> Text -> ScriptMessage)
        -> StatementHandler g m
withNonlocAtom2 submsg msg [pdx| %_ = ?txt |] = do
    extratext <- messageText submsg
    msgToPP $ msg extratext txt
withNonlocAtom2 _ _ stmt = preStatement stmt

-- | Table of script atom -> icon key. Only ones that are different are listed.
scriptIconTable :: HashMap Text Text
scriptIconTable = HM.fromList
    [("industrial_complex"  , "cic")
    ,("arms_factory"        , "mic")
    ,("dockyard"            , "nic")
    ,("air_base"            , "air base")
    ,("naval_base"          , "naval base")
    ,("coastal_bunker"      , "coastal fort")
    ,("anti_air_building"   , "static aa")
    ,("synthetic_refinery"  , "synthetic")
    ,("radar_station"       , "radar station")
    ,("rocket_site"         , "rocket site")
    ,("nuclear_reactor"     , "reactor")
    ,("bunker"              , "land fort")
    ,("supply_node"         , "supply hub")
    ,("rail_way"            , "railway")
    ,("fuel_silo"           , "fuel silo")
    -- autonomy
    ,("autonomy_dominion"   , "dominion")
    ,("autonomy_satellite"  , "satellite")
    ]

-- | Table of script atom -> file. For things that don't have icons and should instead just
-- show an image. An empty string can be used as a short hand for just appending ".png".
scriptIconFileTable :: HashMap Text Text
scriptIconFileTable = HM.fromList
    [
    ]

-- Given a script atom, return the corresponding icon key, if any.
iconKey :: Text -> Maybe Text
iconKey atom = HM.lookup atom scriptIconTable


-- | As generic_icon except
--
-- * say "same as <foo>" if foo refers to a country (in which case, add a flag if possible)
-- * may not actually have an icon (localization file will know if it doesn't)
iconOrFlag :: (HOI4Info g, Monad m) =>
    (Text -> Text -> ScriptMessage)
        -> (Text -> ScriptMessage)
        -> Maybe HOI4Scope
        -> StatementHandler g m
iconOrFlag _ flagmsg expectScope stmt@[pdx| %_ = $vartag:$var |] = do
    mwhoflag <- eflag expectScope (Right (vartag, var))
    case mwhoflag of
        Just whoflag -> msgToPP . flagmsg $ whoflag
        Nothing -> preStatement stmt
iconOrFlag iconmsg flagmsg expectScope [pdx| $head = $name |] = msgToPP =<< do
    nflag <- flag expectScope name -- laziness means this might not get evaluated
--   when (T.toLower name == "prev") . withCurrentFile $ \f -> do
--       traceM $ f ++ ": iconOrFlag: " ++ T.unpack head ++ " = " ++ T.unpack name
--       ps <- getPrevScope
--       traceM $ "PREV scope is: " ++ show ps
    if isTag name || isPronoun name
        then return . flagmsg . Doc.doc2text $ nflag
        else iconmsg (iconText . HM.findWithDefault name name $ scriptIconTable) <$> getGameL10n name
iconOrFlag _ _ _ stmt = plainMsg $ preStatementText' stmt -- CHECK FOR USEFULNESS

-- | Message with icon and tag.
withFlagAndIcon :: (HOI4Info g, Monad m) =>
    Text
        -> (Text -> Text -> ScriptMessage)
        -> Maybe HOI4Scope
        -> StatementHandler g m
withFlagAndIcon iconkey flagmsg expectScope stmt@[pdx| %_ = $vartag:$var |] = do
    mwhoflag <- eflag expectScope (Right (vartag, var))
    case mwhoflag of
        Just whoflag -> msgToPP . flagmsg (iconText iconkey) $ whoflag
        Nothing -> preStatement stmt
withFlagAndIcon iconkey flagmsg expectScope [pdx| %_ = $name |] = msgToPP =<< do
    nflag <- flag expectScope name
    return . flagmsg (iconText iconkey) . Doc.doc2text $ nflag
withFlagAndIcon _ _ _ stmt = plainMsg $ preStatementText' stmt

-- | Handler for statements where RHS is a tag or state id.
tagOrState :: (HOI4Info g, Monad m) =>
    (Text -> ScriptMessage)
        -> (Text -> ScriptMessage)
        -> Maybe HOI4Scope
        -> StatementHandler g m
tagOrState tagmsg _ expectScope stmt@[pdx| %_ = $vartag:$var |] = do
    mwhoflag <- eflag expectScope (Right (vartag, var))
    case mwhoflag of
        Just whoflag -> msgToPP $ tagmsg whoflag
        Nothing -> preStatement stmt
tagOrState tagmsg provmsg expectScope stmt@[pdx| %_ = ?!eobject |]
    = msgToPP =<< case eobject of
            Just (Right tag) -> do
                tagflag <- flag expectScope tag
                return . tagmsg . Doc.doc2text $ tagflag
            Just (Left stateid) -> do -- is a state id
                state_loc <- getStateLoc stateid
                return . provmsg $ state_loc
            Nothing -> return (preMessage stmt)
tagOrState _ _ _ stmt = preStatement stmt -- CHECK FOR USEFULNESS

tagOrStateIcon :: (HOI4Info g, Monad m) =>
    (Text -> ScriptMessage)
        -> (Text -> ScriptMessage)
        -> StatementHandler g m
tagOrStateIcon tagmsg provmsg stmt@[pdx| $head = ?!eobject |]
    = msgToPP =<< case eobject of
            Just (Right tag) -> do -- string: is a tag or pronoun
--              when (T.toLower tag == "prev") . withCurrentFile $ \f -> do
--                  traceM $ f ++ ": tagOrStateIcon: " ++ T.unpack head ++ " = " ++ T.unpack tag
--                  ps <- getPrevScope
--                  traceM $ "PREV scope is: " ++ show ps
                tagflag <- flag Nothing tag
                return . tagmsg . Doc.doc2text $ tagflag
            Just (Left stateid) -> do -- is a state id
                state_loc <- getStateLoc stateid
                return . provmsg $ state_loc
            Nothing -> return (preMessage stmt)
tagOrStateIcon _ _ stmt = preStatement stmt

-- TODO (if necessary): allow operators other than = and pass them to message
-- handler
-- | Handler for numeric statements.
numeric :: (IsGameState (GameState g), Monad m) =>
    (Double -> ScriptMessage)
        -> StatementHandler g m
numeric msg [pdx| %_ = !n |] = msgToPP $ msg n
numeric _ stmt = plainMsg $ preStatementText' stmt

-- | Handler for numeric compare statements.
numericCompare :: (HOI4Info g, Monad m) =>
    Text -> Text ->
    (Double -> Text -> ScriptMessage) ->
    (Text -> Text -> ScriptMessage)
        -> StatementHandler g m
numericCompare gt lt msg msgvar stmt@[pdx| %_ = %num |] = case num of
    (floatRhs -> Just n) -> msgToPP $ msg n $ "equal to or " <> gt
    GenericRhs n [] -> msgToPP $ msgvar n $ "equal to or " <> gt
    GenericRhs nt [nv] -> let n = nt <> nv in msgToPP $ msgvar n $ "equal to or " <> gt
    _ -> trace ("Compare '=' failed : " ++ show stmt) $ preStatement stmt
numericCompare gt lt msg msgvar stmt@[pdx| %_ > %num |] = case num of
    (floatRhs -> Just n) -> msgToPP $ msg n gt
    GenericRhs n [] -> msgToPP $ msgvar n gt
    GenericRhs nt [nv] -> let n = nt <> nv in msgToPP $ msgvar n gt
    _ -> trace ("Compare '>' failed : " ++ show stmt) $ preStatement stmt
numericCompare gt lt msg msgvar stmt@[pdx| %_ < %num |] = case num of
    (floatRhs -> Just n) -> msgToPP $ msg n lt
    GenericRhs n [] -> msgToPP $ msgvar n lt
    GenericRhs nt [nv] -> let n = nt <> nv in msgToPP $ msgvar n lt
    _ -> trace ("Compare '<' failed : " ++ show stmt) $ preStatement stmt
numericCompare _ _ _ _ stmt = preStatement stmt

numericCompareCompound :: (HOI4Info g, Monad m) =>
    Text -> Text ->
    (Double -> Text -> ScriptMessage) ->
    (Text -> Text -> ScriptMessage)
        -> StatementHandler g m
numericCompareCompound gt lt msg msgvar stmt@[pdx| %_ = %rhs |] = case rhs of
    CompoundRhs [scr] -> numericCompare gt lt msg msgvar scr
    _ -> preStatement stmt
numericCompareCompound _ _ _ _ stmt = preStatement stmt

numericCompareLoc :: (HOI4Info g, Monad m) =>
    Text -> Text ->
    (Double -> Text -> Text -> ScriptMessage) ->
    (Text -> Text -> Text -> ScriptMessage)
        -> StatementHandler g m
numericCompareLoc gt lt msg msgvar stmt@[pdx| $txt = %num |] = do
    loc <- getGameL10n txt
    case num of
        (floatRhs -> Just n) -> msgToPP $ msg n ("equal to or " <> gt) loc
        GenericRhs n [] -> msgToPP $ msgvar n ("equal to or " <> gt) loc
        GenericRhs nt [nv] -> let n = nt <> nv in msgToPP $ msgvar n ("equal to or " <> gt) loc
        _ -> trace ("Compare '=' failed : " ++ show stmt) $ preStatement stmt
numericCompareLoc gt lt msg msgvar stmt@[pdx| $txt > %num |] = do
    loc <- getGameL10n txt
    case num of
        (floatRhs -> Just n) -> msgToPP $ msg n gt loc
        GenericRhs n [] -> msgToPP $ msgvar n gt loc
        GenericRhs nt [nv] -> let n = nt <> nv in msgToPP $ msgvar n gt loc
        _ -> trace ("Compare '>' failed : " ++ show stmt) $ preStatement stmt
numericCompareLoc gt lt msg msgvar stmt@[pdx| $txt < %num |] = do
    loc <- getGameL10n txt
    case num of
        (floatRhs -> Just n) -> msgToPP $ msg n lt loc
        GenericRhs n [] -> msgToPP $ msgvar n lt loc
        GenericRhs nt [nv] -> let n = nt <> nv in msgToPP $ msgvar n lt loc
        _ -> trace ("Compare '<' failed : " ++ show stmt) $ preStatement stmt
numericCompareLoc _ _ _ _ stmt = preStatement stmt

numericCompareCompoundLoc :: (HOI4Info g, Monad m) =>
    Text -> Text ->
    (Double -> Text -> Text -> ScriptMessage) ->
    (Text -> Text -> Text -> ScriptMessage)
        -> StatementHandler g m
numericCompareCompoundLoc gt lt msg msgvar stmt@[pdx| %_ = %rhs |] = case rhs of
    CompoundRhs [scr] -> numericCompareLoc gt lt msg msgvar scr
    _ -> preStatement stmt
numericCompareCompoundLoc _ _ _ _ stmt = preStatement stmt


-- | Handler for statements where the RHS is either a number or a tag.
numericOrTag :: (HOI4Info g, Monad m) =>
    (Double -> ScriptMessage)
        -> (Text -> ScriptMessage)
        -> StatementHandler g m
numericOrTag numMsg tagMsg stmt@[pdx| %_ = %rhs |] = msgToPP =<<
    case floatRhs rhs of
        Just n -> return $ numMsg n
        Nothing -> case textRhs rhs of
            Just t -> do -- assume it's a country
                tflag <- flag (Just HOI4Country) t
                return $ tagMsg (Doc.doc2text tflag)
            Nothing -> return (preMessage stmt)
numericOrTag _ _ stmt = preStatement stmt -- CHECK FOR USEFULNESS

-- | Handler for statements where the RHS is either a number or a tag, that
-- also require an icon.
numericOrTagIcon :: (HOI4Info g, Monad m) =>
    Text
        -> (Text -> Double -> ScriptMessage)
        -> (Text -> Text -> ScriptMessage)
        -> StatementHandler g m
numericOrTagIcon icon numMsg tagMsg stmt@[pdx| %_ = %rhs |] = msgToPP =<<
    case floatRhs rhs of
        Just n -> return $ numMsg (iconText icon) n
        Nothing -> case textRhs rhs of
            Just t -> do -- assume it's a country
                tflag <- flag (Just HOI4Country) t
                return $ tagMsg (iconText icon) (Doc.doc2text tflag)
            Nothing -> return (preMessage stmt)
numericOrTagIcon _ _ _ stmt = preStatement stmt -- CHECK FOR USEFULNESS

-- | Handler for a statement referring to a country. Use a flag.
withFlag :: (HOI4Info g, Monad m) =>
    (Text -> ScriptMessage) -> StatementHandler g m
withFlag msg stmt@[pdx| %_ = $vartag:$var |] = do
    mwhoflag <- eflag (Just HOI4Country) (Right (vartag, var))
    case mwhoflag of
        Just whoflag -> msgToPP . msg $ whoflag
        Nothing -> preStatement stmt
withFlag msg [pdx| %_ = $who |] = do
    whoflag <- flag (Just HOI4Country) who
    msgToPP . msg . Doc.doc2text $ whoflag
withFlag _ stmt = preStatement stmt

-- | Handler for a statement referring to a country. Use a flag.
withFlagAndTag :: (HOI4Info g, Monad m) =>
    (Text -> Text -> ScriptMessage) -> StatementHandler g m
withFlagAndTag msg stmt@[pdx| %_ = $vartag:$var |] = do
    mwhoflag <- eflag (Just HOI4Country) (Right (vartag, var))
    case mwhoflag of
        Just whoflag -> msgToPP $ msg whoflag ""
        Nothing -> preStatement stmt
withFlagAndTag msg [pdx| %_ = $who |] = do
    whoflag <- flagText (Just HOI4Country) who
    msgToPP $ msg whoflag  who
withFlagAndTag _ stmt = preStatement stmt

-- | Handler for yes-or-no statements.
withBool :: (HOI4Info g, Monad m) =>
    (Bool -> ScriptMessage)
        -> StatementHandler g m
withBool msg stmt = do
    fullmsg <- withBool' msg stmt
    maybe (preStatement stmt)
          return
          fullmsg

withBoolHOI4Scope :: (HOI4Info g, Monad m) =>
    (Bool -> ScriptMessage) -- ^ Message for country scope
        -> (Bool -> ScriptMessage) -- ^ Message for character scope
        -> StatementHandler g m
withBoolHOI4Scope countrymsg charactermsg stmt = do
    thescope <- getCurrentScope
    case thescope of
        Just HOI4Country -> withBool countrymsg stmt
        _ -> withBool charactermsg stmt

-- | Helper for 'withBool'.
withBool' :: (HOI4Info g, Monad m) =>
    (Bool -> ScriptMessage)
        -> GenericStatement
        -> PPT g m (Maybe IndentedMessages)
withBool' msg [pdx| %_ = ?yn |] | T.map toLower yn `elem` ["yes","no","false"]
    = fmap Just . msgToPP $ case T.toCaseFold yn of
        "yes" -> msg True
        "no"  -> msg False
        "false" -> msg False
        _     -> error "impossible: withBool matched a string that wasn't yes, no or false"
withBool' _ _ = return Nothing

-- | Like numericIconLoc, but for booleans
boolIconLoc :: (HOI4Info g, Monad m) =>
    Text
        -> Text
        -> (Text -> Text -> Bool -> ScriptMessage)
        -> StatementHandler g m
boolIconLoc the_icon what msg stmt
    = do
        whatloc <- getGameL10n what
        res <- withBool' (msg (iconText the_icon) whatloc) stmt
        maybe (preStatement stmt)
              return
              res

-- | Handler for statements whose RHS may be "yes"/"no" or a tag.
withFlagOrBool :: (HOI4Info g, Monad m) =>
    (Bool -> ScriptMessage)
        -> (Text -> ScriptMessage)
        -> StatementHandler g m
withFlagOrBool bmsg _ [pdx| %_ = yes |] = msgToPP (bmsg True)
withFlagOrBool bmsg _ [pdx| %_ = no  |]  = msgToPP (bmsg False)
withFlagOrBool _ tmsg stmt = withFlag tmsg stmt

-- | Handler for statements whose RHS is a number OR a tag/prounoun, with icon
withTagOrNumber :: (HOI4Info g, Monad m) =>
    Text
        -> (Text -> Double -> ScriptMessage)
        -> (Text -> Text -> ScriptMessage)
        -> StatementHandler g m
withTagOrNumber iconkey numMsg _ [pdx| %_ = !num |]
    = msgToPP $ numMsg (iconText iconkey) num
withTagOrNumber iconkey _ tagMsg scr@[pdx| %_ = $_ |]
    = withFlagAndIcon iconkey tagMsg (Just HOI4Country) scr
withTagOrNumber  _ _ _ stmt = plainMsg $ preStatementText' stmt -- CHECK FOR USEFULNESS

-- | Handler for statements that have a number and an icon.
numericIcon :: (IsGameState (GameState g), Monad m) =>
    Text
        -> (Text -> Double -> ScriptMessage)
        -> (Text -> Text -> ScriptMessage)
        -> StatementHandler g m
numericIcon the_icon msg _ [pdx| %_ = !amt |]
    = msgToPP $ msg (iconText the_icon) amt
numericIcon the_icon _ msgvar [pdx| %_ = $amt |]
    = msgToPP $ msgvar (iconText the_icon) amt
numericIcon the_icon _ msgvar [pdx| %_ = $amttag:$amt |]
    = msgToPP $ msgvar (iconText the_icon) (amttag <> ":" <> amt)
numericIcon _ _ _ stmt = plainMsg $ preStatementText' stmt

-- | Handler for statements that have a number and an icon, plus a fixed
-- localizable atom.
numericIconLoc :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    Text
        -> Text
        -> (Text -> Text -> Double -> ScriptMessage)
        -> (Text -> Text -> Text -> ScriptMessage)
        -> StatementHandler g m
numericIconLoc the_icon what msg _ [pdx| %_ = !amt |]
    = do whatloc <- getGameL10n what
         msgToPP $ msg (iconText the_icon) whatloc amt
numericIconLoc the_icon what _ msgvar [pdx| %_ = $amt |]
    = do whatloc <- getGameL10n what
         msgToPP $ msgvar (iconText the_icon) whatloc amt
numericIconLoc the_icon what _ msgvar [pdx| %_ = $amttag:$amt |]
    = do whatloc <- getGameL10n what
         msgToPP $ msgvar (iconText the_icon) whatloc (amttag <> ":" <> amt)
numericIconLoc _ _ _ _ stmt = plainMsg $ preStatementText' stmt

-- | Handler for statements that have a number and a localizable atom.
numericLoc :: (IsGameState (GameState g), IsGameData (GameData g), Monad m) =>
    Text
        -> (Text -> Double -> ScriptMessage)
        -> StatementHandler g m
numericLoc what msg [pdx| %_ = !amt |]
    = do whatloc <- getGameL10n what
         msgToPP $ msg whatloc amt
numericLoc _ _  stmt = plainMsg $ preStatementText' stmt

-- | Handler for values that use a different message and icon depending on
-- whether the value is positive or negative.
numericIconChange :: (HOI4Info g, Monad m) =>
    Text        -- ^ Icon for negative values
        -> Text -- ^ Icon for positive values
        -> (Text -> Double -> ScriptMessage) -- ^ Message for negative values
        -> (Text -> Double -> ScriptMessage) -- ^ Message for positive values
        -> StatementHandler g m
numericIconChange negicon posicon negmsg posmsg [pdx| %_ = !amt |]
    = if amt < 0
        then msgToPP $ negmsg (iconText negicon) amt
        else msgToPP $ posmsg (iconText posicon) amt
numericIconChange _ _ _ _ stmt = plainMsg $ preStatementText' stmt -- CHECK FOR USEFULNESS

----------------------
-- Text/value pairs --
----------------------

-- $textvalue
-- This is for statements of the form
--      head = {
--          what = some_atom
--          value = 3
--      }
-- e.g.
--      num_of_religion = {
--          religion = catholic
--          value = 0.5
--      }
-- There are several statements of this form, but with different "what" and
-- "value" labels, so the first two parameters say what those label are.
--
-- There are two message parameters, one for value < 1 and one for value >= 1.
-- In the example num_of_religion, value is interpreted as a percentage of
-- provinces if less than 1, or a number of provinces otherwise. These require
-- rather different messages.
--
-- We additionally attempt to localize the RHS of "what". If it has no
-- localization string, it gets wrapped in a @<tt>@ element instead.

-- convenience synonym
tryLoc :: (IsGameData (GameData g), Monad m) => Text -> PPT g m (Maybe Text)
tryLoc = getGameL10nIfPresent

-- | Get icon and localization for the atom given. Return @mempty@ if there is
-- no icon, and wrapped in @<tt>@ tags if there is no localization.
tryLocAndIcon :: (IsGameData (GameData g), Monad m) => Text -> PPT g m (Text,Text)
tryLocAndIcon atom = do
    loc <- tryLoc atom
    return (fromMaybe mempty (Just (iconText atom)),
            fromMaybe ("<tt>" <> atom <> "</tt>") loc)


-- | Get localization for the atom given. Return atom
-- if there is no localization.
tryLocMaybe :: (IsGameData (GameData g), Monad m) => Text -> PPT g m (Text,Text)
tryLocMaybe atom = do
    loc <- tryLoc atom
    return ("", fromMaybe atom loc)

data TextValue = TextValue
        {   tv_what :: Maybe Text
        ,   tv_value :: Maybe Double
        ,   tv_var :: Maybe Text
        }
newTV :: TextValue
newTV = TextValue Nothing Nothing Nothing

parseTV :: Foldable t => Text -> Text -> t GenericStatement -> TextValue
parseTV whatlabel vallabel = foldl' addLine newTV
    where
        addLine :: TextValue -> GenericStatement -> TextValue
        addLine tv [pdx| $label = ?what |] | label == whatlabel
            = tv { tv_what = Just what }
        addLine tv [pdx| $label = !val |] | label == vallabel
            = tv { tv_value = Just val }
        addLine tv [pdx| $label = $val |] | label == vallabel
            = tv { tv_var = Just val }
        addLine nor _ = nor

data TextValueComp = TextValueComp
        {   tvc_what :: Maybe Text
        ,   tvc_value :: Maybe Double
        ,   tvc_var :: Maybe Text
        ,   tvc_comp :: Maybe Text
        }
newTVC :: TextValueComp
newTVC = TextValueComp Nothing Nothing Nothing Nothing

parseTVC :: Foldable t =>
    Text -> Text -> Text -> Text -> t GenericStatement -> TextValueComp
parseTVC whatlabel vallabel gt lt = foldl' addLine newTVC
    where
        addLine :: TextValueComp -> GenericStatement -> TextValueComp
        addLine tvc [pdx| $label = ?what |] | label == whatlabel
            = tvc { tvc_what = Just what }
        addLine tvc [pdx| $label = !val |] | label == vallabel
            = tvc { tvc_value = Just val, tvc_comp = Just ("equal to or " <> gt) }
        addLine tvc [pdx| $label > !val |] | label == vallabel
            = tvc { tvc_value = Just val, tvc_comp = Just gt }
        addLine tvc [pdx| $label < !val |] | label == vallabel
            = tvc { tvc_value = Just val, tvc_comp = Just lt  }
        addLine tvc [pdx| $label = $val |] | label == vallabel
            = tvc { tvc_var = Just val, tvc_comp = Just ("equal to or " <> gt) }
        addLine tvc [pdx| $label > $val |] | label == vallabel
            = tvc { tvc_var = Just val, tvc_comp = Just gt }
        addLine tvc [pdx| $label < $val |] | label == vallabel
            = tvc { tvc_var = Just val, tvc_comp = Just lt  }
        addLine nor _ = nor

textValue :: forall g m. (HOI4Info g, Monad m) =>
    Text                                             -- ^ Label for "what"
        -> Text                                      -- ^ Label for "how much"
        -> (Text -> Text -> Double -> ScriptMessage) -- ^ Message constructor, if abs value < 1
        -> (Text -> Text -> Text -> ScriptMessage) -- ^ Message constructor, if abs value >= 1
        -> (Text -> PPT g m (Text, Text)) -- ^ Action to localize and get icon (applied to RHS of "what")
        -> StatementHandler g m
textValue whatlabel vallabel valmsg varmsg loc stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_tv (parseTV whatlabel vallabel scr)
    where
        pp_tv :: TextValue -> PPT g m ScriptMessage
        pp_tv tv = case (tv_what tv, tv_value tv, tv_var tv) of
            (Just what, Just value, _) -> do
                (what_icon, what_loc) <- loc what
                return $ valmsg what_icon what_loc value
            (Just what, _, Just var) -> do
                (what_icon, what_loc) <- loc what
                return $ varmsg what_icon what_loc var
            _ -> return $ preMessage stmt
textValue _ _ _ _ _ stmt = preStatement stmt


textValueKey :: forall g m. (HOI4Info g, Monad m) =>
    Text                                             -- ^ Label for "what"
        -> Text                                      -- ^ Label for "how much"
        -> (Text -> Text -> Double -> ScriptMessage) -- ^ Message constructor, for value
        -> (Text -> Text -> Text -> ScriptMessage) -- ^ Message constructor, for var
        -> StatementHandler g m
textValueKey whatlabel vallabel valmsg varmsg stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_tv (parseTV whatlabel vallabel scr)
    where
        pp_tv :: TextValue -> PPT g m ScriptMessage
        pp_tv tv = case (tv_what tv, tv_value tv, tv_var tv) of
            (Just what, Just value,_) -> do
                what_loc <- getGameL10n what
                return $ valmsg what_loc what value
            (Just what, _, Just var) -> do
                what_loc <- getGameL10n what
                return $ varmsg what_loc what var
            _ -> return $ preMessage stmt
textValueKey _ _ _ _ stmt = preStatement stmt

textValueCompare :: forall g m. (HOI4Info g, Monad m) =>
    Text                                             -- ^ Label for "what"
        -> Text                                      -- ^ Label for "how much"
        -> Text
        -> Text
        -> (Text -> Text -> Text -> Double -> ScriptMessage) -- ^ Message constructor, for val
        -> (Text -> Text -> Text -> Text -> ScriptMessage) -- ^ Message constructor, for var
        -> (Text -> PPT g m (Text, Text)) -- ^ Action to localize and get icon (applied to RHS of "what")
        -> StatementHandler g m
textValueCompare whatlabel vallabel gt lt valmsg varmsg loc stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_tv (parseTVC whatlabel vallabel gt lt scr)
    where
        pp_tv :: TextValueComp -> PPT g m ScriptMessage
        pp_tv tvc = case (tvc_what tvc, tvc_value tvc, tvc_var tvc, tvc_comp tvc) of
            (Just what, Just value, _, Just comp) -> do
                (what_icon, what_loc) <- loc what
                return $ valmsg what_icon what_loc comp value
            (Just what, _, Just var, Just comp) -> do
                (what_icon, what_loc) <- loc what
                return $ varmsg what_icon what_loc comp var
            _ -> return $ preMessage stmt
textValueCompare _ _ _ _ _ _ _ stmt = preStatement stmt

withNonlocTextValue :: forall g m. (HOI4Info g, Monad m) =>
    Text                                             -- ^ Label for "what"
        -> Text                                      -- ^ Label for "how much"
        -> ScriptMessage                             -- ^ submessage to send
        -> (Text -> Text -> Double -> ScriptMessage) -- ^ Message constructor
        -> (Text -> Text -> Text -> ScriptMessage) -- ^ Message constructor
        -> StatementHandler g m
withNonlocTextValue whatlabel vallabel submsg valmsg varmsg stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_tv (parseTV whatlabel vallabel scr)
    where
        pp_tv :: TextValue -> PPT g m ScriptMessage
        pp_tv tv = case (tv_what tv, tv_value tv, tv_var tv) of
            (Just what, Just value, _) -> do
                extratext <- messageText submsg
                return $ valmsg extratext what value
            (Just what, _, Just var) -> do
                extratext <- messageText submsg
                return $ varmsg extratext what var
            _ -> return $ preMessage stmt
withNonlocTextValue _ _ _ _ _ stmt = preStatement stmt

data ValueValue = ValueValue
        {   vv_what :: Maybe Double
        ,   vv_value :: Maybe Double
        ,   vv_var :: Maybe Text
        }
newVV :: ValueValue
newVV = ValueValue Nothing Nothing Nothing

parseVV :: Foldable t => Text -> Text -> t GenericStatement -> ValueValue
parseVV whatlabel vallabel = foldl' addLine newVV
    where
        addLine :: ValueValue -> GenericStatement -> ValueValue
        addLine vv [pdx| $label = !what |] | label == whatlabel
            = vv { vv_what = Just what }
        addLine vv [pdx| $label = !val |] | label == vallabel
            = vv { vv_value = Just val }
        addLine vv [pdx| $label = !val |] | label == vallabel
            = vv { vv_value = Just val }
        addLine nor _ = nor

valueValue :: forall g m. (HOI4Info g, Monad m) =>
    Text                                             -- ^ Label for "what"
        -> Text                                      -- ^ Label for "how much"
        -> (Double -> Double -> ScriptMessage) -- ^ Message constructor, if abs value < 1
        -> (Double -> Text -> ScriptMessage) -- ^ Message constructor, if abs value >= 1
        -> StatementHandler g m
valueValue whatlabel vallabel valmsg varmsg stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_vv (parseVV whatlabel vallabel scr)
    where
        pp_vv :: ValueValue -> PPT g m ScriptMessage
        pp_vv vv = case (vv_what vv, vv_value vv, vv_var vv) of
            (Just what, Just value, _) ->
                return $ valmsg what value
            (Just what, _, Just var) ->
                return $ varmsg what var
            _ -> return $ preMessage stmt
valueValue _ _ _ _ stmt = preStatement stmt

-- | Statements of the form
-- @
--      has_trade_modifier = {
--          who = ROOT
--          name = merchant_recalled
--      }
-- @
data TextAtom = TextAtom
        {   ta_what :: Maybe Text
        ,   ta_atom :: Maybe Text
        }
newTA :: TextAtom
newTA = TextAtom Nothing Nothing

parseTA :: Foldable t => Text -> Text -> t GenericStatement -> TextAtom
parseTA whatlabel atomlabel scr = foldl' addLine newTA scr
    where
        addLine :: TextAtom -> GenericStatement -> TextAtom
        addLine ta [pdx| $label = ?what |]
            | label == whatlabel
            = ta { ta_what = Just what }
        addLine ta [pdx| $label = ?at |]
            | label == atomlabel
            = ta { ta_atom = Just at }
        addLine ta scr = trace ("parseTA: Ignoring " ++ show scr) ta


textAtom :: forall g m. (HOI4Info g, Monad m) =>
    Text -- ^ Label for "what" (e.g. "who")
        -> Text -- ^ Label for atom (e.g. "name")
        -> (Text -> Text -> Text -> ScriptMessage) -- ^ Message constructor
        -> (Text -> PPT g m (Maybe Text)) -- ^ Action to localize, get icon, etc. (applied to RHS of "what")
        -> StatementHandler g m
textAtom whatlabel atomlabel msg loc stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_ta (parseTA whatlabel atomlabel scr)
    where
        pp_ta :: TextAtom -> PPT g m ScriptMessage
        pp_ta ta = case (ta_what ta, ta_atom ta) of
            (Just what, Just atom) -> do
                mwhat_loc <- loc what
                atom_loc <- getGameL10n atom
                let what_icon = iconText what
                    what_loc = fromMaybe ("<tt>" <> what <> "</tt>") mwhat_loc
                return $ msg what_icon what_loc atom_loc
            _ -> return $ preMessage stmt
textAtom _ _ _ _ stmt = preStatement stmt

textAtomKey :: forall g m. (HOI4Info g, Monad m) =>
    Text -- ^ Label for "what" (e.g. "who")
        -> Text -- ^ Label for atom (e.g. "name")
        -> (Text -> Text -> Text -> Text -> ScriptMessage) -- ^ Message constructor
        -> (Text -> PPT g m (Maybe Text)) -- ^ Action to localize, get icon, etc. (applied to RHS of "what")
        -> StatementHandler g m
textAtomKey whatlabel atomlabel msg loc stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_ta (parseTA whatlabel atomlabel scr)
    where
        pp_ta :: TextAtom -> PPT g m ScriptMessage
        pp_ta ta = case (ta_what ta, ta_atom ta) of
            (Just what, Just atom) -> do
                mwhat_loc <- loc what
                atom_loc <- getGameL10n atom
                let what_loc = fromMaybe ("<tt>" <> what <> "</tt>") mwhat_loc
                return $ msg what_loc atom_loc what atom
            _ -> return $ preMessage stmt
textAtomKey _ _ _ _ stmt = preStatement stmt

taDescAtomIcon :: forall g m. (HOI4Info g, Monad m) =>
    Text -> Text ->
    (Text -> Text -> Text -> ScriptMessage) -> StatementHandler g m
taDescAtomIcon tDesc tAtom msg stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_lai (parseTA tDesc tAtom scr)
    where
        pp_lai :: TextAtom -> PPT g m ScriptMessage
        pp_lai ta = case (ta_what ta, ta_atom ta) of
            (Just desc, Just atom) -> do
                descLoc <- getGameL10n desc
                atomLoc <- getGameL10n (T.toUpper atom) -- XXX: why does it seem to necessary to use toUpper here?
                return $ msg descLoc (iconText atom) atomLoc
            _ -> return $ preMessage stmt
taDescAtomIcon _ _ _ stmt = preStatement stmt

data TextFlag = TextFlag
        {   tf_what :: Maybe Text
        ,   tf_flag :: Maybe (Either Text (Text, Text))
        }
newTF :: TextFlag
newTF = TextFlag Nothing Nothing

parseTF :: Foldable t => Text -> Text -> t GenericStatement -> TextFlag
parseTF whatlabel flaglabel scr = foldl' addLine newTF scr
    where
        addLine :: TextFlag -> GenericStatement -> TextFlag
        addLine tf [pdx| $label = ?what |]
            | label == whatlabel
            = tf { tf_what = Just what }
        addLine tf [pdx| $label = $target |]
            | label == flaglabel
            = tf { tf_flag = Just (Left target) }
        addLine tf [pdx| $label = $vartag:$var |]
            | label == flaglabel
            = tf { tf_flag = Just (Right (vartag, var)) }
        addLine tf scr = trace ("parseTF: Ignoring " ++ show scr) tf

taTypeFlag :: forall g m. (HOI4Info g, Monad m) => Text -> Text -> (Text -> Text -> ScriptMessage) -> StatementHandler g m
taTypeFlag tType tFlag msg stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_tf (parseTF tType tFlag scr)
    where
        pp_tf :: TextFlag -> PPT g m ScriptMessage
        pp_tf tf = case (tf_what tf, tf_flag tf) of
            (Just typ, Just flag) -> do
                typeLoc <- getGameL10n typ
                flagLoc <- eflag (Just HOI4Country) flag
                case flagLoc of
                   Just flagLocd -> return $ msg typeLoc flagLocd
                   _-> return $ preMessage stmt
            _ -> return $ preMessage stmt
taTypeFlag _ _ _ stmt = preStatement stmt

-- | Helper for effects, where the argument is a single statement in a clause
-- E.g. generate_traitor_advisor_effect

getEffectArg :: Text -> GenericStatement -> Maybe GenericRhs
getEffectArg tArg stmt@[pdx| %_ = @scr |] = case scr of
        [[pdx| $arg = %val |]] | T.toLower arg == tArg -> Just val
        _ -> Nothing
getEffectArg _ _ = Nothing -- CHECK FOR USEFULNESS

simpleEffectNum :: forall g m. (HOI4Info g, Monad m) => Text ->  (Double -> ScriptMessage) -> StatementHandler g m
simpleEffectNum tArg msg stmt =
    case getEffectArg tArg stmt of
        Just (FloatRhs num) -> msgToPP (msg num)
        Just (IntRhs num) -> msgToPP (msg (fromIntegral num))
        _ -> trace ("warning: Not handled by simpleEffectNum: " ++ show stmt) $ preStatement stmt -- CHECK FOR USEFULNESS

simpleEffectAtom :: forall g m. (HOI4Info g, Monad m) => Text -> (Text -> Text -> ScriptMessage) -> StatementHandler g m
simpleEffectAtom tArg msg stmt =
    case getEffectArg tArg stmt of
        Just (GenericRhs atom _) -> do
            loc <- getGameL10n atom
            msgToPP $ msg (iconText atom) loc
        _ -> trace ("warning: Not handled by simpleEffectAtom: " ++ show stmt) $ preStatement stmt -- CHECK FOR USEFULNESS

-- AI decision factors

-- | Extract the appropriate message(s) from an @ai_will_do@ clause.
ppAiWillDo :: (HOI4Info g, Monad m) => AIWillDo -> PPT g m IndentedMessages
ppAiWillDo (AIWillDo mbase mods) = do
    mods_pp'd <- fold <$> traverse ppAiMod mods
    let baseWtMsg = maybe MsgNoBaseWeight MsgAIBaseWeight mbase
    iBaseWtMsg <- msgToPP baseWtMsg
    return $ iBaseWtMsg ++ mods_pp'd

-- | Extract the appropriate message(s) from a @modifier@ section within an
-- @ai_will_do@ clause.
ppAiMod :: (HOI4Info g, Monad m) => AIModifier -> PPT g m IndentedMessages
ppAiMod (AIModifier (Just multiplier) Nothing triggers) = do
    triggers_pp'd <- ppMany triggers
    case triggers_pp'd of
        [(i, triggerMsg)] -> do
            triggerText <- messageText triggerMsg
            return [(i, MsgAIFactorOneline triggerText multiplier)]
        _ -> withCurrentIndentZero $ \i -> return $
            (i, MsgAIFactorHeader multiplier)
            : map (first succ) triggers_pp'd -- indent up
ppAiMod (AIModifier Nothing (Just addition) triggers) = do
    triggers_pp'd <- ppMany triggers
    case triggers_pp'd of
        [(i, triggerMsg)] -> do
            triggerText <- messageText triggerMsg
            return [(i, MsgAIAddOneline triggerText addition)]
        _ -> withCurrentIndentZero $ \i -> return $
            (i, MsgAIAddHeader addition)
            : map (first succ) triggers_pp'd -- indent up
ppAiMod AIModifier {} =
    plainMsg "(missing multiplier/add for this factor)"

-- | Verify assumption about rhs
rhsAlways :: (HOI4Info g, Monad m) => Text -> ScriptMessage -> StatementHandler g m
rhsAlways assumedRhs msg [pdx| %_ = ?rhs |] | T.toLower rhs == assumedRhs = msgToPP msg
rhsAlways _ _ stmt = trace ("Expectation is wrong in statement " ++ show stmt) $ preStatement stmt

rhsAlwaysYes :: (HOI4Info g, Monad m) => ScriptMessage -> StatementHandler g m
rhsAlwaysYes = rhsAlways "yes"

rhsIgnored :: (IsGameState (GameState g), Monad m) =>
    ScriptMessage -> p -> PPT g m IndentedMessages
rhsIgnored msg stmt = msgToPP msg

rhsAlwaysEmptyCompound :: (HOI4Info g, Monad m) => ScriptMessage -> StatementHandler g m
rhsAlwaysEmptyCompound msg stmt@(Statement _ OpEq (CompoundRhs [])) = msgToPP msg
rhsAlwaysEmptyCompound _ stmt = trace ("Expectation is wrong in statement " ++ show stmt) $ preStatement stmt

-- Opinions

-- Add an opinion modifier towards someone (for a number of years).
data AddOpinion = AddOpinion {
        op_who :: Maybe (Either Text (Text, Text))
    ,   op_modifier :: Maybe Text
    ,   op_years :: Maybe Double
    } deriving Show
newAddOpinion :: AddOpinion
newAddOpinion = AddOpinion Nothing Nothing Nothing

opinion :: (HOI4Info g, Monad m) =>
    (Text -> Text -> Text -> ScriptMessage)
        -> (Text -> Text -> Text -> Double -> ScriptMessage)
        -> StatementHandler g m
opinion msgIndef msgDur stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_add_opinion (foldl' addLine newAddOpinion scr)
    where
        addLine :: AddOpinion -> GenericStatement -> AddOpinion
        addLine op [pdx| target        = $tag         |] = op { op_who = Just (Left tag) }
        addLine op [pdx| target        = $vartag:$var |] = op { op_who = Just (Right (vartag, var)) }
        addLine op [pdx| modifier      = ?label       |] = op { op_modifier = Just label }
        addLine op [pdx| years         = !n           |] = op { op_years = Just n }
        -- following two for add_mutual_opinion_modifier_effect
        addLine op [pdx| scope_country = $tag         |] = op { op_who = Just (Left tag) }
        addLine op [pdx| scope_country = $vartag:$var |] = op { op_who = Just (Right (vartag, var)) }
        addLine op [pdx| opinion_modifier = ?label    |] = op { op_modifier = Just label }
        addLine op _ = op
        pp_add_opinion op = case (op_who op, op_modifier op) of
            (Just ewhom, Just modifier) -> do
                mwhomflag <- eflag (Just HOI4Country) ewhom
                mod_loc <- getGameL10n modifier
                case (mwhomflag, op_years op) of
                    (Just whomflag, Nothing) -> return $ msgIndef modifier mod_loc whomflag
                    (Just whomflag, Just years) -> return $ msgDur modifier mod_loc whomflag years
                    _ -> return (preMessage stmt)
            _ -> trace ("opinion: who or modifier missing: " ++ show stmt) $ return (preMessage stmt)
opinion _ _ stmt = preStatement stmt

data HasOpinion = HasOpinion
        {   hop_target :: Maybe Text
        ,   hop_value :: Maybe Double
        ,   hop_valuevar :: Maybe Text
        ,   hop_ltgt :: Text
        }
newHasOpinion :: HasOpinion
newHasOpinion = HasOpinion Nothing Nothing Nothing undefined
hasOpinion :: forall g m. (HOI4Info g, Monad m) =>
    (Text -> Text -> Text -> ScriptMessage) ->
    StatementHandler g m
hasOpinion msg stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_hasOpinion (foldl' addLine newHasOpinion scr)
    where
        addLine :: HasOpinion -> GenericStatement -> HasOpinion
        addLine hop [pdx| target = ?target |] = hop { hop_target = Just target }
        addLine hop [pdx| value = !val |] = hop { hop_value = Just val, hop_ltgt = "equal to or more than" } -- at least
        addLine hop [pdx| value > !val |] = hop { hop_value = Just val, hop_ltgt = "more than" } -- at least
        addLine hop [pdx| value < !val |] = hop { hop_value = Just val, hop_ltgt = "less than" } -- less than
        addLine hop [pdx| value = $val |] = hop { hop_valuevar = Just val, hop_ltgt = "equal to or more than" } -- at least
        addLine hop [pdx| value > $val |] = hop { hop_valuevar = Just val, hop_ltgt = "more than" } -- at least
        addLine hop [pdx| value < $val |] = hop { hop_valuevar = Just val, hop_ltgt = "less than" } -- less than
        addLine hop _ = trace ("warning: unrecognized has_opinion clause in : " ++ show stmt) hop
        pp_hasOpinion :: HasOpinion -> PPT g m ScriptMessage
        pp_hasOpinion hop = case (hop_target hop, hop_value hop, hop_valuevar hop, hop_ltgt hop) of
            (Just target, Just value, _, ltgt) -> do
                target_flag <- flagText (Just HOI4Country) target
                let valuet = Doc.doc2text (colourNumSign True value)
                return (msg valuet target_flag ltgt)
            (Just target, _, Just valuet, ltgt) -> do
                target_flag <- flagText (Just HOI4Country) target
                return (msg valuet target_flag ltgt)
            _ -> return (preMessage stmt)
hasOpinion _ stmt = preStatement stmt

-- Events

data TriggerEvent = TriggerEvent
        { e_id :: Maybe Text
        , e_title_loc :: Maybe Text
        , e_days :: Maybe Double
        , e_hours :: Maybe Double
        , e_random :: Maybe Double
        , e_random_days :: Maybe Double
        , e_random_hours :: Maybe Double
        }
newTriggerEvent :: TriggerEvent
newTriggerEvent = TriggerEvent Nothing Nothing Nothing Nothing Nothing Nothing Nothing
triggerEvent :: forall g m. (HOI4Info g, Monad m) => ScriptMessage -> StatementHandler g m
triggerEvent evtType stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_trigger_event =<< foldM addLine newTriggerEvent scr
    where
        addLine :: TriggerEvent -> GenericStatement -> PPT g m TriggerEvent
        addLine evt [pdx| id = ?!eeid |]
            | Just eid <- either (\n -> T.pack (show (n::Int))) id <$> eeid
            = do
                mevt_t <- getEventTitle eid
                return evt { e_id = Just eid, e_title_loc = mevt_t }
        addLine evt [pdx| days = %rhs |]
            = return evt { e_days = floatRhs rhs }
        addLine evt [pdx| hours = %rhs |]
            = return evt { e_hours = floatRhs rhs }
        addLine evt [pdx| random = %rhs |]
            = return evt { e_random = floatRhs rhs }
        addLine evt [pdx| random_days = %rhs |]
            = return evt { e_random_days = floatRhs rhs }
        addLine evt [pdx| random_hours = %rhs |]
            = return evt { e_random_hours = floatRhs rhs }
        addLine evt _ = return evt
        pp_trigger_event :: TriggerEvent -> PPT g m ScriptMessage
        pp_trigger_event evt = do
            evtType_t <- messageText evtType
            case e_id evt of
                Just msgid ->
                    let loc = fromMaybe msgid (e_title_loc evt)
                        time = fromMaybe 0 (e_days evt) * 24 + fromMaybe 0 (e_hours evt)
                        timernd = time + fromMaybe 0 (e_random_days evt) * 24 + fromMaybe 0 (e_random evt) + fromMaybe 0 (e_hours evt)
                        tottimer = formatHours time <> if timernd /= time then " to " <> formatHours timernd else ""
                    in if time > 0 then
                        return $ MsgTriggerEventTime evtType_t msgid loc tottimer
                    else
                        return $ MsgTriggerEvent evtType_t msgid loc
                _ -> return $ preMessage stmt
triggerEvent evtType stmt@[pdx| %_ = ?!rid |]
    = msgToPP =<< pp_trigger_event =<< addLine newTriggerEvent rid
    where
        addLine :: TriggerEvent -> Maybe (Either Int Text) -> PPT g m TriggerEvent
        addLine evt eeid
            | Just eid <- either (\n -> T.pack (show (n::Int))) id <$> eeid
            = do
                mevt_t <- getEventTitle eid
                return evt { e_id = Just eid, e_title_loc = mevt_t }
        addLine evt _ = return evt
        pp_trigger_event :: TriggerEvent -> PPT g m ScriptMessage
        pp_trigger_event evt = do
            evtType_t <- messageText evtType
            case e_id evt of
                Just msgid -> do
                    let loc = fromMaybe msgid (e_title_loc evt)
                    return $ MsgTriggerEvent evtType_t msgid loc
                _ -> return $ preMessage stmt
triggerEvent _ stmt = preStatement stmt

-- Random

random :: (HOI4Info g, Monad m) => StatementHandler g m
random stmt@[pdx| %_ = @scr |]
    | (front, back) <- break
                        (\case
                            [pdx| chance = %_ |] -> True
                            _ -> False)
                        scr
      , not (null back)
      , [pdx| %_ = %rhs |] <- head back
      , Just chance <- floatRhs rhs
      = compoundMessage
          (MsgRandomChance chance)
          [pdx| %undefined = @(front ++ tail back) |]
    | otherwise = compoundMessage MsgRandom stmt
random stmt = preStatement stmt


toPct :: Double -> Double
toPct num = fromIntegral (round (num * 1000)) / 10 -- round to one digit after the point

data RandomMod = RandomMod{
     rm_mod  :: GenericScript
    ,rm_rest :: GenericScript
}
newRM :: RandomMod
newRM = RandomMod [] []

randomList :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
randomList stmt@[pdx| %_ = @scr |] = if all chk scr then -- Ugly solution for vars in random list
        fmtRandomList $ map entry scr
    else
        fmtRandomVarList $ map entryv scr
    where
        chk [pdx| !weight = @scr |] = True
        chk [pdx| %var = @scr |] = False
        chk _ = trace ("DEBUG: random_list " ++ show scr) (error "Bad clause in random_list check")
        entry [pdx| !weight = @scr |] = (fromIntegral weight, scr)
        entry _ = trace ("DEBUG: random_list " ++ show scr) (error "Bad clause in random_list, possibly vars?")
        entryv [pdx| $var = @scr |] = (var, scr)
        entryv [pdx| $_:$var = @scr |] = (var, scr)
        entryv [pdx| !weight = @scr |] = (T.pack (show weight), scr)
        entryv _ = trace ("DEBUG: random_list " ++ show scr) (error "Bad clause in random_list, possibly ints?")
        fmtRandomList entries = withCurrentIndent $ \i ->
            let total = sum (map fst entries)
            in (:) (i, MsgRandom) <$> (concat <$> indentUp (mapM (fmtRandomList' total) entries))
        fmtRandomList' total (wt, what) = do
            -- TODO: Could probably be simplified.
            let (mtrigger, rest) = extractStmt (matchLhsText "trigger") what
            rm <- foldM foldModifiers newRM rest
            trig <- (case mtrigger of
                Just s -> indentUp (compoundMessage MsgRandomListTrigger s)
                _ -> return [])
            mod <- ppMods rm
            body <- ppMany (rm_rest rm) -- has integral indentUp
            liftA2 (++)
                (msgToPP $ MsgRandomChanceHOI4 (toPct (wt / total)) wt)
                (pure (trig ++ mod ++ body))
        -- Ugly solution for vars in random list
        fmtRandomVarList entries = withCurrentIndent $ \i ->
            (:) (i, MsgRandom) <$> (concat <$> indentUp (mapM fmtRandomVarList' entries))
        fmtRandomVarList' (wt, what) = do
            -- TODO: Could probably be simplified.
            let (mtrigger, rest) = extractStmt (matchLhsText "trigger") what
            rm <- foldM foldModifiers newRM rest
            trig <- (case mtrigger of
                Just s -> indentUp (compoundMessage MsgRandomListTrigger s)
                _ -> return [])
            mod <- ppMods rm
            body <- ppMany (rm_rest rm) -- has integral indentUp
            liftA2 (++)
                (msgToPP $ MsgRandomVarChance wt)
                (pure (trig ++ mod ++ body))

        ppMods rm = concat <$> indentUp (mapM (\case
                s@[pdx| %_ = @scr |] ->
                    let
                        (mfactor, s') = extractStmt (matchLhsText "factor") scr
                        (madd, sa') = extractStmt (matchLhsText "add") scr
                    in
                        case mfactor of
                            Just [pdx| %_ = !factor |] -> do
                                cond <- ppMany s'
                                liftA2 (++) (msgToPP $ MsgRandomListModifier factor) (pure cond)
                            _ -> case madd of
                                    Just [pdx| %_ = !add |] -> do
                                        cond <- ppMany sa'
                                        liftA2 (++) (msgToPP $ MsgRandomListAddModifier add) (pure cond)
                                    _ -> preStatement s
                s -> preStatement s) (rm_mod rm))

        foldModifiers :: RandomMod -> GenericStatement -> PPT g m RandomMod
        foldModifiers rm stmt@[pdx| modifier = %s |] = return rm {rm_mod = rm_mod rm ++ [stmt]}
        foldModifiers rm stmt = return rm {rm_rest = rm_rest rm ++ [stmt]}
randomList _ = withCurrentFile $ \file ->
    error ("randomList sent strange statement in " ++ file)

-- DLC

hasDlc :: (HOI4Info g, Monad m) => StatementHandler g m
hasDlc [pdx| %_ = ?dlc |]
    = msgToPP $ MsgHasDLC dlc_icon dlc
    where
        mdlc_key = HM.lookup dlc . HM.fromList $
            [("Together for Victory", "tfv")
            ,("Death or Dishonor", "dod")
            ,("Waking the Tiger", "wtt")
            ,("Man the Guns", "mtg")
            ,("La Resistance", "lar")
            ,("Battle for the Bosporus", "bftb")
            ,("No Step Back", "nsb")
            ,("By Blood Alone", "bba")
            ]
        dlc_icon = maybe "" iconText mdlc_key
hasDlc stmt = preStatement stmt

withFlagOrState :: (HOI4Info g, Monad m) =>
    (Text -> ScriptMessage)
        -> (Text -> ScriptMessage)
        -> StatementHandler g m
withFlagOrState countryMsg _ stmt@[pdx| %_ = ?_ |]
    = withFlag countryMsg stmt
withFlagOrState countryMsg _ stmt@[pdx| %_ = $_:$_ |]
    = withFlag countryMsg stmt -- could be either
withFlagOrState _ stateMsg stmt@[pdx| %_ = !(_ :: Double) |]
    = withState stateMsg stmt
withFlagOrState _ _ stmt = preStatement stmt -- CHECK FOR USEFULNESS

customTriggerTooltip :: (HOI4Info g, Monad m) => StatementHandler g m
customTriggerTooltip [pdx| %_ = @scr |]
    -- ignore the custom tooltip -- BC - let's not
    = ppMany scr
customTriggerTooltip stmt = preStatement stmt

---------------
-- has focus --
---------------

focusProgress :: (HOI4Info g, Monad m) =>
    (Text -> Text -> Text -> Text -> ScriptMessage)
        -> StatementHandler g m
focusProgress msg stmt@[pdx| $lhs = @compa |] = do
    let nf = case getfoc compa of
            Just nfr -> nfr
            _-> "<!-- Check Script -->"
        compare = case getcomp compa of
            Just compr -> compr
            _-> "<!-- Check Script -->"
    nfs <- getNationalFocus
    gfx <- getInterfaceGFX
    let mnf = HM.lookup nf nfs
    case mnf of
        Nothing -> preStatement stmt -- unknown national focus
        Just nnf -> do
            let nfKey = nf_id nnf
                nfIcon = HM.findWithDefault "GFX_goal_unknown" (nf_icon nnf) gfx
            nf_loc <- getGameL10n nfKey
            msgToPP (msg nfIcon nfKey nf_loc compare)
    where
        getfoc :: [GenericStatement] -> Maybe Text
        getfoc [] = Nothing
        getfoc (stmt@[pdx| focus = $id |] : _) = Just id
        getfoc (_ : ss) = getfoc ss
        getcomp :: [GenericStatement] -> Maybe Text
        getcomp [] = Nothing
        getcomp (stmt@[pdx| progress > !num |] : _)
            = Just $ "more than " <> Doc.doc2text (reducedNum plainPc num)
        getcomp (stmt@[pdx| progress < !num |] : _)
            = Just $ "less than " <> Doc.doc2text (reducedNum plainPc num)
        getcomp (_ : ss) = getcomp ss
focusProgress _ stmt = preStatement stmt

handleFocus :: (HOI4Info g, Monad m) =>
    (Text -> Text -> Text -> ScriptMessage)
        -> StatementHandler g m
handleFocus msg stmt@[pdx| $lhs = $nf |] = do
    nfs <- getNationalFocus
    gfx <- getInterfaceGFX
    let mnf = HM.lookup nf nfs
    case mnf of
        Nothing -> preStatement stmt -- unknown national focus
        Just nnf -> do
            let nfKey = nf_id nnf
                nfIcon = HM.findWithDefault "GFX_goal_unknown" (nf_icon nnf) gfx
            nf_loc <- getGameL10n nfKey
            msgToPP (msg nfIcon nfKey nf_loc)
handleFocus _ stmt = preStatement stmt



data UncFoc = UncFoc
        {   uf_focus :: Text
        ,   uf_uncomplete_children :: Bool
        }
newUF :: UncFoc
newUF = UncFoc "<!-- Check Game Script -->" False

focusUncomplete :: (HOI4Info g, Monad m) =>
    (Text -> Text -> Text -> Bool -> ScriptMessage)
        -> StatementHandler g m
focusUncomplete msg stmt@[pdx| $lhs = @scr |] = do
    msgToPP =<< ppuf (foldl' addLine newUF scr)
    where
        addLine :: UncFoc -> GenericStatement -> UncFoc
        addLine uf [pdx| focus = ?what |] = uf { uf_focus =  what }
        addLine uf [pdx| uncomplete_children = %rhs |]
            | GenericRhs "yes" [] <- rhs = uf { uf_uncomplete_children = True }
            | GenericRhs "no"  [] <- rhs = uf { uf_uncomplete_children = False }
        addLine uf [pdx| refund_political_power = %_ |] = uf
        addLine uf scr = trace ("uncompleteFocus: Ignoring " ++ show scr) uf

        ppuf uf = do
            let nf = uf_focus uf
            nfs <- getNationalFocus
            gfx <- getInterfaceGFX
            let mnf = HM.lookup nf nfs
            case mnf of
                Nothing -> return $ preMessage stmt -- unknown national focus
                Just nnf -> do
                    let nfKey = nf_id nnf
                        nfIcon = HM.findWithDefault "GFX_goal_unknown" (nf_icon nnf) gfx
                    nf_loc <- getGameL10n nfKey
                    return $ msg nfIcon nfKey nf_loc (uf_uncomplete_children uf)
focusUncomplete _ stmt = preStatement stmt

------------------------------
-- Handler for xxx_variable --
------------------------------

data SetVariable = SetVariable
        { sv_which  :: Maybe Text
        , sv_which2 :: Maybe Text
        , sv_value  :: Maybe Double
        , sv_tooltip  :: Maybe Text
        }

newSV :: SetVariable
newSV = SetVariable Nothing Nothing Nothing Nothing

setVariable :: forall g m. (HOI4Info g, Monad m) =>
    (Text -> Text -> ScriptMessage) ->
    (Text -> Double -> ScriptMessage) ->
    StatementHandler g m
setVariable msgWW msgWV stmt@[pdx| %_ = @scr |]
    = pp_sv (foldl' addLine newSV scr)
    where
        addLine :: SetVariable -> GenericStatement -> SetVariable
        addLine sv [pdx| var = ?val |]
            = if isNothing (sv_which sv) then
                sv { sv_which = Just val }
              else
                sv { sv_which2 = Just val }
        addLine sv [pdx| value = !val |]
            = sv { sv_value = Just val }
        addLine sv [pdx| value = ?val |]
            = sv { sv_which2 = Just val }
        addLine sv [pdx| tooltip = ?txt |]
            = sv { sv_tooltip = Just txt }
        addLine sv [pdx| $var = !val |]
            = sv { sv_which = Just var, sv_value = Just val }
        addLine sv [pdx| $var = $val |]
            = sv { sv_which = Just var, sv_which2 = Just val }
        addLine sv [pdx| $vartag:$var = !val |]
            = sv { sv_which = Just (vartag <> ":" <> var), sv_value = Just val }
        addLine sv [pdx| $vartag:$var = $valtag:$val |]
            = sv { sv_which = Just (vartag <> ":" <> var), sv_which2 = Just (valtag <> ":" <> val) }
        addLine sv [pdx| $var = $valtag:$val |]
            = sv { sv_which = Just var, sv_which2 = Just (valtag <> ":" <> val) }
        addLine sv [pdx| $vartag:$var = $val |]
            = sv { sv_which = Just (vartag <> ":" <> var), sv_which2 = Just val }
        addLine sv _ = trace ("failed to parse var: " ++ show stmt) sv
        toTT :: Text -> Text
        toTT t = "<tt>" <> t <> "</tt>"
        pp_sv :: SetVariable -> PPT g m IndentedMessages
        pp_sv sv = do
            ttmsg <- case sv_tooltip sv of
                Just tt -> do
                    ttloc <- getGameL10n tt
                    indentUp $ msgToPP $ MsgVariableTooltip ttloc
                Nothing -> return []
            case (sv_which sv, sv_which2 sv, sv_value sv) of
                (Just v1, Just v2, Nothing) -> do
                    headmsg <- msgToPP $ msgWW (toTT v1) (toTT v2)
                    return $ headmsg ++ ttmsg
                (Just v,  Nothing, Just val) -> do
                    headmsg <- msgToPP $ msgWV (toTT v) val
                    return $ headmsg ++ ttmsg
                _ -> preStatement stmt
setVariable _ _ stmt = preStatement stmt

data ClampVariable = ClampVariable
        { clv_which  :: Text
        , clv_var :: Maybe Text
        , clv_var2 :: Maybe Text
        , clv_value  :: Maybe Double
        , clv_value2  :: Maybe Double
        }

newCLV :: ClampVariable
newCLV = ClampVariable undefined Nothing Nothing Nothing Nothing

clampVariable :: forall g m. (HOI4Info g, Monad m) =>
    (Text -> Double -> Double -> ScriptMessage) ->
    (Text -> Double -> Text -> ScriptMessage) ->
    (Text -> Text -> Double -> ScriptMessage) ->
    (Text -> Text -> Text -> ScriptMessage) ->
    StatementHandler g m
clampVariable msgVV msgVW msgWV msgWW stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_clv (foldl' addLine newCLV scr)
    where
        addLine :: ClampVariable -> GenericStatement -> ClampVariable
        addLine clv [pdx| var = $var |]
            = clv { clv_which = var }
        addLine clv [pdx| variable = $var |]
            = clv { clv_which = var }
        addLine clv [pdx| min = !val |]
            = clv { clv_value = Just val }
        addLine clv [pdx| max = !val |]
            = clv { clv_value2 = Just val }
        addLine clv [pdx| min = $var |]
            = clv { clv_var = Just var}
        addLine clv [pdx| max = $var |]
            = clv { clv_var2 = Just var }
        addLine clv _ = clv
        toTT :: Text -> Text
        toTT t = "<tt>" <> t <> "</tt>"
        pp_clv :: ClampVariable -> PPT g m ScriptMessage
        pp_clv clv = case (clv_value clv,  clv_value2 clv,
                             clv_var clv, clv_var2 clv) of
            (Just val, Just val2, Nothing, Nothing) -> do return $ msgVV (clv_which clv) val val2
            (Just val, Nothing, Nothing, Just v2) -> do return $ msgVW (clv_which clv) val (toTT v2)
            (Nothing, Just val2, Just v1, Nothing) -> do return $ msgWV (clv_which clv) (toTT v1) val2
            (Nothing, Nothing, Just v1, Just v2) -> do return $ msgWW (clv_which clv) (toTT v1) (toTT v2)
            _ ->  do return $ preMessage stmt
clampVariable _ _ _ _ stmt = preStatement stmt

data CheckVariable = CheckVariable
        { cv_which  :: Maybe Text
        , cv_which2 :: Maybe Text
        , cv_value  :: Maybe Double
        , cv_comp   :: Text
        }

newCV :: CheckVariable
newCV = CheckVariable Nothing Nothing Nothing "greater than or equals"

checkVariable :: forall g m. (HOI4Info g, Monad m) =>
    (Text -> Text -> Text -> ScriptMessage) ->
    (Text -> Text -> Double -> ScriptMessage) ->
    StatementHandler g m
checkVariable msgWW msgWV stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_cv (foldl' addLine newCV scr)
    where
        addLine :: CheckVariable -> GenericStatement -> CheckVariable
        addLine cv [pdx| var = $val |]
            = cv { cv_which = Just val }
        addLine cv [pdx| value = !val |]
            = cv { cv_value = Just val }
        addLine cv [pdx| value = $val |]
            = cv { cv_which2 = Just val }
        addLine cv [pdx| compare = $comp |]
            = cv { cv_comp = T.replace "_" " " comp}
        addLine cv [pdx| $var = !val |]
            = cv { cv_which = Just var, cv_value = Just val, cv_comp = "equals" }
        addLine cv [pdx| $var < !val |]
            = cv { cv_which = Just var, cv_value = Just val, cv_comp = "less than" }
        addLine cv [pdx| $var > !val |]
            = cv { cv_which = Just var, cv_value = Just val, cv_comp = "greater than" }
        addLine cv [pdx| $var = $val |]
            = cv { cv_which = Just var, cv_which2 = Just val, cv_comp = "equals" }
        addLine cv [pdx| $var < $val |]
            = cv { cv_which = Just var, cv_which2 = Just val, cv_comp = "less than" }
        addLine cv [pdx| $var > $val |]
            = cv { cv_which = Just var, cv_which2 = Just val, cv_comp = "greater than" }
        addLine cv _ = cv
        toTT :: Text -> Text
        toTT t = "<tt>" <> t <> "</tt>"
        pp_cv :: CheckVariable -> PPT g m ScriptMessage
        pp_cv cv = case (cv_which cv, cv_which2 cv, cv_value cv, cv_comp cv) of
            (Just v1, Just v2, Nothing, comp) -> do return $ msgWW comp (toTT v1) (toTT v2)
            (Just v,  Nothing, Just val, comp) -> do return $ msgWV comp (toTT v) val
            _ -> do return $ preMessage stmt
checkVariable _ _ stmt = preStatement stmt

-------------------------------------
-- Handler for export_to_variable  --
-------------------------------------

data ExportVariable = ExportVariable
        { ev_which  :: Maybe Text
        , ev_value :: Maybe Text
        , ev_who :: Maybe Text
        } deriving Show

newEV :: ExportVariable
newEV = ExportVariable Nothing Nothing Nothing

exportVariable :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
exportVariable stmt@[pdx| %_ = @scr |] = msgToPP =<< pp_ev (foldl' addLine newEV scr)
    where
        addLine :: ExportVariable -> GenericStatement -> ExportVariable
        addLine ev [pdx| which = ?val |]
            = ev { ev_which = Just val }
        addLine ev [pdx| variable_name = ?val |]
            = ev { ev_which = Just val }
        addLine ev [pdx| value = ?val |]
            = ev { ev_value = Just val }
        addLine ev [pdx| who = ?val |]
            = ev { ev_who = Just val }
        addLine ev stmt = trace ("Unknown in export_to_variable " ++ show stmt) ev
        toTT :: Text -> Text
        toTT t = "<tt>" <> t <> "</tt>"
        pp_ev :: ExportVariable -> PPT g m ScriptMessage
        pp_ev ExportVariable { ev_which = Just which, ev_value = Just value, ev_who = Nothing } =
            return $ MsgExportVariable (toTT which) value
        pp_ev ExportVariable { ev_which = Just which, ev_value = Just value, ev_who = Just who } = do
            whoLoc <- Doc.doc2text <$> allowPronoun (Just HOI4Country) (fmap Doc.strictText . getGameL10n) who
            return $ MsgExportVariableWho (toTT which) value whoLoc
        pp_ev ev = return $ trace ("Missing info for export_to_variable " ++ show ev ++ " " ++ show stmt) $ preMessage stmt
exportVariable stmt = trace ("Not handled in export_to_variable: " ++ show stmt) $ preStatement stmt

-----------------------------------
-- Handler for (set_)ai_attitude --
-----------------------------------
--aiAttitude :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
--aiAttitude stmt@[pdx| %_ = @scr |] =
--    let
--        (aiValue, rest) = extractStmt (matchLhsText "value") scr
--        aivalue = maybe "" 0 aiValue
--    in
--        msgToPP =<< pp_aia aivalue (parseTF "type" "id" rest)
--    where
--        pp_aia :: Double -> TextFlag -> PPT g m ScriptMessage
--        pp_aia aivalue tf = case (tf_what tf, tf_flag tf) of
--            (Just typeStrat, Just idTag) -> do
--                idflag <-  eflag (Just HOI4Country) idTag
--                let flagloc = fromMaybe "<!-- Check Script -->" idflag
--                return $ MsgAddAiStrategy flagloc aivalue typeStrat
--            _ -> return $ preMessage stmt
--aiAttitude stmt = trace ("Not handled in aiAttitude: " ++ show stmt) $ preStatement stmt

-- Helper
getMaybeRhsText :: Maybe GenericStatement -> Maybe Text
getMaybeRhsText (Just [pdx| %_ = $t |]) = Just t
getMaybeRhsText _ = Nothing

-------------------------------------------
-- Handler for add_building_construction --
-------------------------------------------

data HOI4AddBC = HOI4AddBC{
      addbc_type :: Text
    , addbc_level :: Maybe Double
    , addbc_levelvar :: Maybe Text
    , addbc_province :: Maybe [Double]
    , addbc_instant_build :: Bool
    , addbc_province_all :: Bool
    , addbc_province_coastal :: Bool
    , addbc_province_naval :: Bool
    , addbc_province_border :: Bool
    , addbc_province_border_country :: Maybe (Either Text (Text, Text))
    , addbc_limit_to_supply_node :: Bool
    , addbc_limit_to_victory_point :: Bool
    , addbc_limit_to_victory_point_num :: Maybe Double
    , addbc_limit_to_victory_point_comp :: Text
    , addbc_province_comp :: Text
    , addbc_province_level :: Maybe Double
    } deriving Show

newABC :: HOI4AddBC
newABC = HOI4AddBC "" Nothing Nothing Nothing False False False False False Nothing False False Nothing "" "" Nothing

addBuildingConstruction :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
addBuildingConstruction stmt@[pdx| %_ = @scr |] =
    msgToPP =<< pp_abc (foldl' addLine newABC scr)
    where
        addLine :: HOI4AddBC -> GenericStatement -> HOI4AddBC
        addLine abc [pdx| type = $build |] = abc { addbc_type = build }
        addLine abc stmt@[pdx| level = !num |] = abc { addbc_level = Just num }
        addLine abc stmt@[pdx| level = $txt |] = abc { addbc_levelvar = Just txt }
        addLine abc stmt@[pdx| level = $vartag:$var |] = abc { addbc_levelvar = Just (vartag <> ":" <> var) }
        addLine abc [pdx| instant_build = yes |] = abc { addbc_instant_build = True }
        addLine abc [pdx| province = !num |] = abc { addbc_province = Just [num] }
        addLine abc [pdx| province = @scr |] = foldl' addLine' abc scr
        addLine abc [pdx| $other = %_ |] = trace ("unknown section in add_building_construction: " ++ show other) abc
        addLine abc stmt = trace ("Unknown in add_building_construction: " ++ show stmt) abc

        addLine' :: HOI4AddBC -> GenericStatement -> HOI4AddBC
        addLine' abc [pdx| all_provinces = %rhs |]
            | GenericRhs "yes" [] <- rhs = abc { addbc_province_all = True }
            | otherwise = abc
        addLine' abc [pdx| limit_to_coastal = %rhs |]
            | GenericRhs "yes" [] <- rhs = abc { addbc_province_coastal = True }
            | otherwise = abc
        addLine' abc [pdx| limit_to_naval_base = %rhs |]
            | GenericRhs "yes" [] <- rhs = abc { addbc_province_naval = True }
            | otherwise = abc
        addLine' abc [pdx| limit_to_border = %rhs |]
            | GenericRhs "yes" [] <- rhs = abc { addbc_province_border = True }
            | otherwise = abc
        addLine' abc [pdx| limit_to_supply_node = %rhs |]
            | GenericRhs "yes" [] <- rhs = abc { addbc_limit_to_supply_node = True }
            | otherwise = abc
        addLine' abc [pdx| limit_to_border_country = $txt |] =
            abc { addbc_province_border_country = Just (Left txt) }
        addLine' abc [pdx| limit_to_border_country = $vartag:$var |] =
            abc { addbc_province_border_country = Just (Right (vartag, var)) }
        addLine' abc [pdx| id = !num |] =
            let oldprov = fromMaybe [] (addbc_province abc) in
            abc { addbc_province = Just (oldprov ++ [num :: Double]) }
        addLine' abc [pdx| limit_to_victory_point > !num |] =
            abc { addbc_limit_to_victory_point_comp = "higher than", addbc_limit_to_victory_point_num = Just num }
        addLine' abc [pdx| limit_to_victory_point < !num |] =
            abc {addbc_limit_to_victory_point_comp = "lower than", addbc_limit_to_victory_point_num = Just num }
        addLine' abc [pdx| limit_to_victory_point = %rhs |]
            | GenericRhs "yes" [] <- rhs = abc { addbc_limit_to_victory_point = True }
            | otherwise = abc
        addLine' abc [pdx| level > !num |] = abc { addbc_province_comp = "higher than", addbc_province_level = Just num }
        addLine' abc [pdx| level < !num |] = abc { addbc_province_comp = "lower than", addbc_province_level = Just num }
        addLine' abc [pdx| $other = %_ |] = trace ("unknown section in add_building_construction@province: " ++ show other) abc
        addLine' abc stmt = trace ("Unknown form in add_building_construction@province: " ++ show stmt) abc

        pp_abc :: HOI4AddBC -> PPT g m ScriptMessage
        pp_abc abc = do
            let buildicon = iconText (addbc_type abc)
            prov <- do
                allmsg <- if addbc_province_all abc then messageText MsgAllProvinces else return ""
                bordmsg <- if addbc_province_border abc then messageText MsgLimitToBorder else return ""
                coastmsg <- if addbc_province_coastal abc then messageText MsgLimitToCoastal else return ""
                navmsg <- if addbc_province_naval abc then messageText MsgLimitToNavalBase else return ""
                navmsg <- if addbc_province_naval abc then messageText MsgLimitToNavalBase else return ""
                let provmsg = case addbc_province abc of
                        Just id -> if length id > 1
                            then T.pack $ concat [", on the provinces (" , intercalate "), (" (map (show . round) id),")"]
                            else T.pack $ concat [", on the province (" , concatMap (show . round) id,")"]
                        _-> ""
                levelmsg <- case addbc_province_level abc of
                    Just level -> messageText $ MsgProvinceLevel (addbc_province_comp abc) level
                    _-> return ""
                bordcountmsg <- case addbc_province_border_country abc of
                    Just (Left txt) -> do
                        mflagloc <- eflag (Just HOI4Country) (Left txt)
                        let flagloc = fromMaybe "<!--CHECK SCRIPT-->" mflagloc
                        messageText $ MsgLimitToBorderCountry flagloc
                    Just (Right (vartag,var)) ->  do
                        mflagloc <- eflag (Just HOI4Country) (Right (vartag,var))
                        let flagloc = fromMaybe "<!--CHECK SCRIPT-->" mflagloc
                        messageText $ MsgLimitToBorderCountry flagloc
                    _-> return ""
                victmsg <- case ( addbc_limit_to_victory_point abc
                                , addbc_limit_to_victory_point_num abc) of
                    (False, Just num) -> messageText $ MsgLimitToVictoryPoint False (addbc_limit_to_victory_point_comp abc) num
                    (True, Nothing) -> messageText $ MsgLimitToVictoryPoint True "" 0
                    _ -> return ""
                return $ allmsg <> bordmsg <> coastmsg <> navmsg <> victmsg <> bordcountmsg <> provmsg <> levelmsg
            buildloc <- getGameL10n (addbc_type abc)
            case (addbc_level abc, addbc_levelvar abc) of
                (Just val, _)-> return $ MsgAddBuildingConstruction (addbc_instant_build abc) buildicon buildloc val prov
                (_, Just var)-> return $ MsgAddBuildingConstructionVar (addbc_instant_build abc) buildicon buildloc var prov
                _-> return $ preMessage stmt
addBuildingConstruction stmt = trace ("Not handled in addBuildingConstruction: " ++ show stmt) $ preStatement stmt

data HOI4SetBL = HOI4SetBL{
      sbl_type :: Text
    , sbl_level :: Maybe Double
    , sbl_levelvar :: Maybe Text
    , sbl_province :: Maybe [Double]
    , sbl_province_all :: Bool
    , sbl_province_coastal :: Bool
    , sbl_province_naval :: Bool
    , sbl_province_border :: Bool
    , sbl_province_comp :: Text
    , sbl_province_level :: Maybe Double
    } deriving Show

newSBL :: HOI4SetBL
newSBL = HOI4SetBL "" Nothing Nothing Nothing False False False False "" Nothing

setBuildingLevel :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
setBuildingLevel stmt@[pdx| %_ = @scr |] =
    msgToPP =<< ppSbl (foldl' addLine newSBL scr)
    where
        addLine :: HOI4SetBL -> GenericStatement -> HOI4SetBL
        addLine sbl [pdx| type = $build |] = sbl { sbl_type = build }
        addLine sbl [pdx| level = !num |] = sbl { sbl_level = Just num }
        addLine sbl [pdx| level = $txt |] = sbl { sbl_levelvar = Just txt }
        addLine sbl [pdx| province = !num |] = sbl { sbl_province = Just [num] }
        addLine sbl [pdx| province = @scr |] = foldl' addLine' sbl scr
        addLine sbl [pdx| instant_build = %_ |] = sbl
        addLine sbl [pdx| $other = %_ |] = trace ("unknown section in set_building_level: " ++ show other) sbl
        addLine sbl stmt = trace ("Unknown form in set_building_level: " ++ show stmt) sbl

        addLine' :: HOI4SetBL -> GenericStatement -> HOI4SetBL
        addLine' sbl [pdx| all_provinces = %rhs |]
            | GenericRhs "yes" [] <- rhs = sbl { sbl_province_all = True }
            | otherwise = sbl
        addLine' sbl [pdx| limit_to_coastal = %rhs |]
            | GenericRhs "yes" [] <- rhs = sbl { sbl_province_coastal = True }
            | otherwise = sbl
        addLine' sbl [pdx| limit_to_naval_base = %rhs |]
            | GenericRhs "yes" [] <- rhs = sbl { sbl_province_naval = True }
            | otherwise = sbl
        addLine' sbl [pdx| limit_to_border = %rhs |]
            | GenericRhs "yes" [] <- rhs = sbl { sbl_province_border = True }
            | otherwise = sbl
        addLine' sbl [pdx| id = !num |] =
            let oldprov = fromMaybe [] (sbl_province sbl) in
            sbl { sbl_province = Just (oldprov ++ [num :: Double]) }
        addLine' sbl [pdx| level > !num |] = sbl { sbl_province_comp = "higher than", sbl_province_level = Just num }
        addLine' sbl [pdx| level < !num |] = sbl { sbl_province_comp = "lower than", sbl_province_level = Just num }
        addLine' sbl [pdx| $other = %_ |] = trace ("unknown section in set_building_level@province: " ++ show other) sbl
        addLine' sbl stmt = trace ("Unknown form in set_building_level@province: " ++ show stmt) sbl

        ppSbl sbl = do
            let buildicon = iconText (sbl_type sbl)
            prov <- do
                allmsg <- if sbl_province_all sbl then messageText MsgAllProvinces else return ""
                bordmsg <- if sbl_province_border sbl then messageText MsgLimitToBorder else return ""
                coastmsg <- if sbl_province_coastal sbl then messageText MsgLimitToCoastal else return ""
                navmsg <- if sbl_province_naval sbl then messageText MsgLimitToNavalBase else return ""
                let provmsg = case sbl_province sbl of
                        Just id -> if length id > 1
                            then T.pack $ concat [", on the provinces (" , intercalate "), (" (map (show . round) id),")"]
                            else T.pack $ concat [", on the province (" , concatMap (show . round) id,")"]
                        _-> ""
                levelmsg <- case sbl_province_level sbl of
                    Just level -> messageText $ MsgProvinceLevel (sbl_province_comp sbl) level
                    _-> return ""
                return $ allmsg <> bordmsg <> coastmsg <> navmsg <> provmsg <> levelmsg
            buildloc <- getGameL10n (sbl_type sbl)
            case (sbl_level sbl, sbl_levelvar sbl) of
                (Just val, _)-> return $ MsgSetBuildingLevel buildicon buildloc val prov
                (_, Just var)-> return $ MsgSetBuildingLevelVar buildicon buildloc var prov
                _-> return $ preMessage stmt
setBuildingLevel stmt = preStatement stmt

----------------------------------
-- Handler for add_named_threat --
----------------------------------
foldCompound "addNamedThreat" "NamedThreat" "nt"
    []
    [CompField "threat" [t|Double|] Nothing True
    ,CompField "name" [t|Text|] Nothing True
    ]
    [|  do
        threatLoc <- getGameL10n _name
        tensionLoc <- getGameL10n "WORLD_TENSION_NAME"
        return $ MsgAddNamedThreat tensionLoc _threat threatLoc
    |]

----------------------------------
-- Handler for create_wargoal --
----------------------------------
data WGGenerator
    = WGGeneratorArr [Int]  -- province = key
    | WGGeneratorVar Text
            -- province = { id = key id = key }
            -- province = { all_provinces = yes	limit_to_border = yes}
    deriving Show
data CreateWG = CreateWG
    {   wg_type :: Maybe Text
    ,   wg_type_loc :: Maybe Text
    ,   wg_target_flag :: Maybe Text
    ,   wg_expire :: Maybe Double
    ,   wg_generator :: Maybe WGGenerator
    ,   wg_states :: [Text]
    } deriving Show

newCWG :: CreateWG
newCWG = CreateWG Nothing Nothing Nothing Nothing Nothing undefined

createWargoal :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
createWargoal stmt@[pdx| %_ = @scr |] =
    msgToPP . pp_create_wg =<< foldM addLine newCWG scr
    where
        addLine :: CreateWG -> GenericStatement -> PPT g m CreateWG
        addLine cwg [pdx| type = $wargoal |]
            = (\wgtype_loc -> cwg
                   { wg_type = Just wargoal
                   , wg_type_loc = Just wgtype_loc })
              <$> getGameL10n wargoal
        addLine cwg stmt@[pdx| target = ?target |]
            = (\target_loc -> cwg
                  { wg_target_flag = target_loc })
              <$> eflag (Just HOI4Country) (Left target)
        addLine cwg [pdx| target = $vartag:$var |]
            = (\target_loc -> cwg
                  { wg_target_flag = target_loc })
              <$> eflag (Just HOI4Country) (Right (vartag, var))
        addLine cwg [pdx| expire = %rhs |]
            = return cwg { wg_expire = floatRhs rhs }
        addLine cwg stmts@[pdx| generator = %state |] = case state of
            CompoundRhs array -> do
                let states = mapMaybe stateFromArray array
                statesloc <- traverse getStateLoc states
                return cwg { wg_generator = Just (WGGeneratorArr states)
                            ,wg_states = statesloc }
            GenericRhs vartag [vstate] ->
                return cwg { wg_generator = Just (WGGeneratorVar vstate)} --Need to deal with existing variables here
            GenericRhs vstate _ ->
                return cwg { wg_generator = Just (WGGeneratorVar vstate)} --Need to deal with existing variables here
            _ -> trace ("Unknown generator statement in create_wargoal: " ++ show stmts) $ return cwg
        addLine cwg stmt
            = trace ("unknown section in create_wargoal: " ++ show stmt) $ return cwg
        stateFromArray :: GenericStatement -> Maybe Int
        stateFromArray (StatementBare (IntLhs e)) = Just e
        stateFromArray stmt = trace ("Unknown in generator array statement: " ++ show stmt) Nothing
        pp_create_wg :: CreateWG -> ScriptMessage
        pp_create_wg cwg =
            let states = case wg_generator cwg of
                    Just (WGGeneratorArr arr) -> T.pack $ concat [" for the ", T.unpack $ plural (length arr) "state " "states " , intercalate ", " $ map T.unpack (wg_states cwg)]
                    Just (WGGeneratorVar var) -> T.pack (" for" ++ T.unpack var)
                    _ -> ""
            in case (wg_type cwg, wg_type_loc cwg,
                     wg_target_flag cwg,
                     wg_expire cwg) of
                (Nothing, _, _, _) -> preMessage stmt -- need WG type
                (_, _, Nothing, _) -> preMessage stmt -- need target
                (_, Just wgtype_loc, Just target_flag, Just days) -> MsgCreateWGDuration wgtype_loc target_flag days states
                (Just wgtype, Nothing, Just target_flag, Just days) -> MsgCreateWGDuration wgtype target_flag days states
                (_, Just wgtype_loc, Just target_flag, Nothing) -> MsgCreateWG wgtype_loc target_flag states
                (Just wgtype, Nothing, Just target_flag, Nothing) -> MsgCreateWG wgtype target_flag states
createWargoal stmt = preStatement stmt

----------------------------------
-- Handler for declare_war_on --
----------------------------------
data DWOGenerator
    = DWOGeneratorArr [Int]  -- province = key
    | DWOGeneratorVar Text
            -- province = { id = key id = key }
            -- province = { all_provinces = yes	limit_to_border = yes}
    deriving Show
data DeclareWarOn = DeclareWarOn
    {   dw_type :: Maybe Text
    ,   dw_type_loc :: Maybe Text
    ,   dw_target_flag :: Maybe Text
    ,   dw_generator :: Maybe DWOGenerator
    ,   dw_states :: [Text]
    } deriving Show

newDWO :: DeclareWarOn
newDWO = DeclareWarOn Nothing Nothing Nothing Nothing []

declareWarOn :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
declareWarOn stmt@[pdx| %_ = @scr |] =
    msgToPP . pp_create_dw =<< foldM addLine newDWO scr
    where
        addLine :: DeclareWarOn -> GenericStatement -> PPT g m DeclareWarOn
        addLine dwo [pdx| type = $wargoal |]
            = (\dwtype_loc -> dwo
                   { dw_type = Just wargoal
                   , dw_type_loc = Just dwtype_loc })
              <$> getGameL10n wargoal
        addLine dwo stmt@[pdx| target = $target |]
            = (\target_loc -> dwo
                  { dw_target_flag = target_loc })
              <$> eflag (Just HOI4Country) (Left target)
        addLine dwo [pdx| target = $vartag:$var |]
            = (\target_loc -> dwo
                  { dw_target_flag = target_loc })
              <$> eflag (Just HOI4Country) (Right (vartag, var))
        addLine dwo stmts@[pdx| generator = %state |] = case state of
            CompoundRhs array ->do
                let states = mapMaybe stateFromArray array
                statesloc <- traverse getStateLoc states
                return dwo { dw_generator = Just (DWOGeneratorArr states)
                            ,dw_states = statesloc }
            GenericRhs vartag [vstate] ->
                return dwo { dw_generator = Just (DWOGeneratorVar vstate)} --Need to deal with existing variables here
            GenericRhs vstate _ ->
                return dwo { dw_generator = Just (DWOGeneratorVar vstate)} --Need to deal with existing variables here
            _ -> trace ("Unknown generator statement in declare_war_on: " ++ show stmts) $ return dwo
        addLine dwo stmt
            = trace ("unknown section in declare_war_on: " ++ show stmt) $ return dwo
        stateFromArray :: GenericStatement -> Maybe Int
        stateFromArray (StatementBare (IntLhs e)) = Just e
        stateFromArray stmt = trace ("Unknown in generator array statement: " ++ show stmt) Nothing
        pp_create_dw :: DeclareWarOn -> ScriptMessage
        pp_create_dw dwo =
            let states = case dw_generator dwo of
                    Just (DWOGeneratorArr arr) -> T.pack $ concat ["for the ", T.unpack $ plural (length arr) "state " "states " , intercalate ", " $ map T.unpack (dw_states dwo)]
                    Just (DWOGeneratorVar var) -> T.pack ("for " ++ T.unpack var)
                    _ -> ""
            in case (dw_type dwo, dw_type_loc dwo,
                     dw_target_flag dwo) of
                (Nothing, _, _) -> preMessage stmt -- need DW type
                (_, _, Nothing) -> preMessage stmt -- need target
                (_, Just dwtype_loc, Just target_flag) -> MsgDeclareWarOn  target_flag dwtype_loc states
                (Just dwtype, Nothing, Just target_flag) -> MsgDeclareWarOn target_flag dwtype states
declareWarOn stmt = preStatement stmt

----------------------------------
-- Handler for annex_country --
----------------------------------
foldCompound "annexCountry" "AnnexCountry" "an"
    []
    [CompField "target" [t|Text|] Nothing True
    ,CompField "transfer_troops" [t|Text|] Nothing False
    ]
    [|  do
        let transferTroops = case _transfer_troops of
                Just "yes" -> " (troops transferred)"
                Just "no" -> " (troops not transferred)"
                _ -> ""
        targetTag <- flagText (Just HOI4Country) _target
        return $ MsgAnnexCountry targetTag transferTroops
    |]

--------------------
-- add_tech_boost --
--------------------

data AddTechBonus = AddTechBonus
        {   tb_name :: Maybe Text
        ,   tb_bonus :: Maybe Double
        ,   tb_uses :: Double
        ,   tb_ahead_reduction :: Maybe Double
        ,   tb_category :: [Text]
        ,   tb_technology :: [Text]
        }
newATB :: AddTechBonus
newATB = AddTechBonus Nothing Nothing 1 Nothing [] []
addTechBonus :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
addTechBonus stmt@[pdx| %_ = @scr |]
    = pp_atb =<< foldM addLine newATB scr
    where
        addLine :: AddTechBonus -> GenericStatement -> PPT g m AddTechBonus
        addLine atb [pdx| name = $name |] = do
            nameloc <- getGameL10n name
            return atb { tb_name = Just nameloc }
        addLine atb [pdx| bonus = !amt |] =
            return atb { tb_bonus = Just amt }
        addLine atb [pdx| ahead_reduction = !amt |] =
            return atb { tb_ahead_reduction = Just amt }
        addLine atb [pdx| uses = !amt  |]
            = return atb { tb_uses = amt }
        addLine atb [pdx| category = $cat |] = do
            let oldcat = tb_category atb
            catloc <- getGameL10n cat
            return atb { tb_category = oldcat ++ [catloc] }
        addLine atb [pdx| technology = $tech |] = do
            let oldtech = tb_technology atb
            techloc <- getGameL10n tech
            return atb { tb_technology = oldtech ++ [techloc] }
        addLine atb _ = return atb
        pp_atb :: AddTechBonus -> PPT g m IndentedMessages
        pp_atb atb = do
            let techcat = tb_category atb ++ tb_technology atb
                ifname = case tb_name atb of
                    Just name -> "(" <> italicText name <> ") "
                    _ -> ""
                uses = tb_uses atb
                tbmsg = case (tb_bonus atb, tb_ahead_reduction atb) of
                    (Just bonus, Just ahead) ->
                        MsgAddTechBonusAheadBoth bonus ahead ifname uses
                    (Just bonus, _) ->
                        MsgAddTechBonus bonus ifname uses
                    (_, Just ahead) ->
                        MsgAddTechBonusAhead ahead ifname uses
                    _ -> trace ("issues in add_technology_bonus: " ++ show stmt ) $ preMessage stmt
            techcatmsg <- mapM (\tc ->withCurrentIndent $ \i -> return [(i+1, MsgUnprocessed tc)]) techcat
            tbmsg_pp <- msgToPP tbmsg
            return $ tbmsg_pp ++ concat techcatmsg
addTechBonus stmt = preStatement stmt

------------------------------------------
-- handlers for various flag statements --
------------------------------------------

data SetFlag = SetFlag
        {   sf_flag :: Text
        ,   sf_value :: Maybe Double
        ,   sf_days :: Maybe Double
        ,   sf_dayst :: Maybe Text
        }

newSF :: SetFlag
newSF = SetFlag undefined Nothing Nothing Nothing
setFlag :: forall g m. (HOI4Info g, Monad m) => ScriptMessage -> StatementHandler g m
setFlag msgft stmt@[pdx| %_ = $flag |] = withNonlocAtom2 msgft MsgSetFlag stmt
setFlag msgft stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_sf =<< foldM addLine newSF scr
    where
        addLine :: SetFlag -> GenericStatement -> PPT g m SetFlag
        addLine sf [pdx| flag = $flag |] =
            return sf { sf_flag = flag }
        addLine sf [pdx| value = !amt |] =
            return sf { sf_value = Just amt }
        addLine sf [pdx| days = !amt |] =
            return sf { sf_days = Just amt }
        addLine sf [pdx| days = $amt |] =
            return sf { sf_dayst = Just amt }
        addLine sf stmt
            = trace ("unknown section in set_country_flag: " ++ show stmt) $ return sf
        pp_sf sf = do
            let value = case sf_value sf of
                    Just num -> T.pack $ " to " ++ show (round num)
                    _ -> ""
                days = case (sf_days sf, sf_dayst sf) of
                    (Just day, _) -> " for " <> formatDays day
                    (_, Just day) -> " for " <> day <> " days"
                    _ -> ""
            msgfts <- messageText msgft
            return $ MsgSetFlagFor msgfts (sf_flag sf) value days
setFlag _ stmt = preStatement stmt

data HasFlag = HasFlag
        {   hf_flag :: Text
        ,   hf_value :: Text
        ,   hf_days :: Text
        ,   hf_date :: Text
        }

newHF :: HasFlag
newHF = HasFlag undefined "" "" ""
hasFlag :: forall g m. (HOI4Info g, Monad m) => ScriptMessage -> StatementHandler g m
hasFlag msgft stmt@[pdx| %_ = $flag |] = withNonlocAtom2 msgft MsgHasFlag stmt
hasFlag msgft stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_hf =<< foldM addLine newHF scr
    where
        addLine :: HasFlag -> GenericStatement -> PPT g m HasFlag
        addLine hf [pdx| flag = $flag |] =
            return hf { hf_flag = flag }
        addLine hf [pdx| value = !amt |] =
            let amtd = " equal to or more than " <> show (amt :: Int) in
            return hf { hf_value = T.pack amtd }
        addLine hf [pdx| value < !amt |] =
            let amtd = " to less than " <> show (amt :: Int) in
            return hf { hf_value = T.pack amtd }
        addLine hf [pdx| value > !amt |] =
            let amtd = " to more than " <> show (amt :: Int) in
            return hf { hf_value = T.pack amtd }
        addLine hf [pdx| days < !amt |] =
            let amtd = " for less than " <> show (amt :: Int) <> " days" in
            return hf { hf_days = T.pack amtd }
        addLine hf [pdx| days > !amt |] =
            let amtd = " for more than " <> show (amt :: Int) <> " days" in
            return hf { hf_days = T.pack amtd }
        addLine hf [pdx| date > %amt |] =
            let amtd = " later than " <> show amt in
            return hf { hf_date = T.pack amtd }
        addLine hf [pdx| date < %amt |] =
            let amtd = " earlier than " <> show amt in
            return hf { hf_date = T.pack amtd }
        addLine hf stmt
            = trace ("unknown section in has_country_flag: " ++ show stmt) $ return hf
        pp_hf hf = do
            msgfts <- messageText msgft
            return $ MsgHasFlagFor msgfts (hf_flag hf) (hf_value hf) (hf_days hf) (hf_date hf)
hasFlag _ stmt = preStatement stmt

----------------------------------
-- Handler for add_to_war --
----------------------------------
foldCompound "addToWar" "AddToWar" "atw"
    []
    [CompField "targeted_alliance" [t|Text|] Nothing True
    ,CompField "enemy" [t|Text|] Nothing True
    ,CompField "hostility_reason" [t|Text|] Nothing False -- guarantee, asked_to_join, war, ally
    ]
    [|  do
        let reason = case _hostility_reason of
                Just "guarantee" -> ""
                Just "asked_to_join" -> ""
                Just "war" -> ""
                Just "ally" -> ""
                _ -> ""
        ally <- flagText (Just HOI4Country) _targeted_alliance
        enemy <- flagText (Just HOI4Country) _enemy
        return $ MsgAddToWar ally enemy reason
    |]

------------------------------
-- Handler for set_autonomy --
------------------------------
data SetAutonomy = SetAutonomy
        {   sa_target :: Maybe Text
        ,   sa_autonomy_state :: Maybe Text
        ,   sa_freedom_level :: Maybe Double
        ,   sa_end_wars :: Bool
        ,   sa_end_civil_wars :: Bool
        }

newSA :: SetAutonomy
newSA = SetAutonomy Nothing Nothing Nothing True True
setAutonomy :: forall g m. (HOI4Info g, Monad m) =>
    (Text -> Text -> Text -> Double -> Text -> ScriptMessage) -> StatementHandler g m
setAutonomy msg stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_sa =<< foldM addLine newSA scr
    where
        addLine :: SetAutonomy -> GenericStatement -> PPT g m SetAutonomy
        addLine sa [pdx| target = $vartag:$var |] = do
            flagd <- eflag (Just HOI4Country) (Right (vartag,var))
            return sa { sa_target = flagd }
        addLine sa [pdx| target = ?txt |] = do
            flagd <- eflag (Just HOI4Country) (Left txt)
            return sa { sa_target = flagd }
        addLine sa [pdx| autonomy_state = $txt |] =
            return sa { sa_autonomy_state = Just txt }
        addLine sa [pdx| autonomous_state = $txt |] =
            return sa { sa_autonomy_state = Just txt }
        addLine sa [pdx| freedom_level = !amt |] =
            return sa { sa_freedom_level = Just (amt :: Double) }
        addLine sa [pdx| end_wars = $yn |] =
            return sa { sa_end_wars = False }
        addLine sa [pdx| end_civil_wars = $yn |] =
            return sa { sa_end_civil_wars = False }
        addLine sa [pdx| release_non_owned_controlled = %_|] =
            return sa
        addLine sa stmt
            = trace ("unknown section in set_autonomy: " ++ show stmt) $ return sa
        pp_sa sa = do
            let endwar = case (sa_end_wars sa, sa_end_civil_wars sa) of
                    (True, True) -> T.pack " and end wars and civil wars for subject"
                    (True, False) -> T.pack " and end wars for subject"
                    (False, True) -> T.pack " and end civil wars for subject"
                    _ -> ""
                freedom = fromMaybe 0 (sa_freedom_level sa)
                autonomy_state = fromMaybe "<!-- Check Script -->" (sa_autonomy_state sa)
                target = fromMaybe "<!-- Check Script -->" (sa_target sa)
            autonomy <- getGameL10n autonomy_state
            return $ msg target (iconText autonomy) autonomy freedom endwar
setAutonomy _ stmt = preStatement stmt

------------------------------
-- Handler for set_politics --
------------------------------
data SetPolitics = SetPolitics
        {   sp_ruling_party :: Text
        ,   sp_elections_allowed :: Maybe Text
        ,   sp_last_election :: Maybe Text
        ,   sp_election_frequency :: Maybe Double
        ,   sp_election_frequencyvar :: Maybe Text
        ,   sp_long_name :: Maybe Text
        ,   sp_name :: Maybe Text
        }

newSP :: SetPolitics
newSP = SetPolitics undefined Nothing Nothing Nothing Nothing Nothing Nothing
setPolitics :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
setPolitics stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_sp =<< foldM addLine newSP scr
    where
        addLine :: SetPolitics -> GenericStatement -> PPT g m SetPolitics
        addLine sp [pdx| ruling_party = $txt |] = return sp { sp_ruling_party = txt }
        addLine sp [pdx| elections_allowed = %_ |] = return sp
        addLine sp [pdx| last_election = %_ |] = return sp
        addLine sp [pdx| election_frequency = $txt |] =
            return sp { sp_election_frequencyvar = Just txt }
        addLine sp [pdx| election_frequency = !amt |] =
            return sp { sp_election_frequency = Just (amt :: Double) }
        addLine sp [pdx| long_name = $yn |] = return sp
        addLine sp [pdx| name = $yn |] = return sp
        addLine sp stmt
            = trace ("unknown section in set_politics: " ++ show stmt) $ return sp
        pp_sp sp = do
            let freq = fromMaybe 0 (sp_election_frequency sp)
            party <- getGameL10n (sp_ruling_party sp)
            case sp_election_frequencyvar sp of
                Just freq -> return $ MsgSetPoliticsVar (iconText party) party freq
                _ -> return $ MsgSetPolitics (iconText party) party freq
setPolitics stmt = preStatement stmt

------------------------------------
-- Handler for has_country_leader --
------------------------------------
foldCompound "hasCountryLeader" "HasLeader" "hcl"
    []
    [CompField "character" [t|Text|] Nothing False
    ,CompField "ruling_only" [t|Text|] Nothing False
    ,CompField "name" [t|Text|] Nothing False
    ,CompField "id" [t|Double|] Nothing False
    ]
    [|  do
        let charjust = case (_character, _name, _id) of
                (Just character, _, _) -> character
                (_, Just name, _) -> name
                (_, _, Just id)-> T.pack $ show $ floor id
                _ -> "<!-- Check Script -->"
        charloc <- getGameL10n charjust
        return $ MsgHasCountryLeader charloc
    |]

------------------------------------
-- Handler for has_country_leader --
------------------------------------
foldCompound "setPartyName" "SetPartyName" "spn"
    []
    [CompField "ideology" [t|Text|] Nothing True
    ,CompField "long_name" [t|Text|] Nothing False
    ,CompField "name" [t|Text|] Nothing True
    ]
    [|  do
        let long_name = fromMaybe "" _long_name
        ideo_loc <- getGameL10n _ideology
        long_loc <- getGameL10n long_name
        short_loc <- getGameL10n _name
        return $ MsgSetPartyName ideo_loc short_loc long_loc
    |]

---------------------------------
-- Handler for load_focus_tree --
---------------------------------

loadFocusTree :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
loadFocusTree stmt@[pdx| %_ = $txt |] = withNonlocAtom MsgLoadFocusTree stmt
loadFocusTree stmt@[pdx| %_ = @scr |] = case extractStmt (matchLhsText "keep_completed") scr of
    (Just keep,_)-> textAtom "tree" "keep_completed" MsgLoadFocusTreeKeep noloc stmt
    _-> case extractStmt (matchLhsText "tree") scr of
        (Just tree,_) -> withNonlocAtom MsgLoadFocusTree tree
        _-> preStatement stmt
loadFocusTree stmt = preStatement stmt

noloc :: (HOI4Info g, Monad m) => Text -> PPT g m (Maybe Text)
noloc txt = return Nothing
---------------------------------
-- Handler for set_nationality --
---------------------------------

setNationality :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
setNationality stmt@[pdx| %_ = $txt |] = withFlag MsgSetNationality stmt
setNationality stmt@[pdx| %_ = @scr |] = taTypeFlag "character" "target_country" MsgSetNationalityChar stmt
setNationality stmt = preStatement stmt

prioritize :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
prioritize stmt@[pdx| %_ = @arr |] = do
                let states = mapMaybe stateFromArray arr
                    stateFromArray (StatementBare (IntLhs e)) = Just e
                    stateFromArray stmt = trace ("Unknown in prioritize array statement: " ++ show stmt) Nothing
                statesloc <- traverse getStateLoc states
                let stateslocced = T.pack $ T.unpack (plural (length statesloc) "state " "states ") ++ intercalate ", " (map T.unpack statesloc)
                msgToPP $ MsgPrioritize stateslocced
prioritize stmt = preStatement stmt

hasWarGoalAgainst :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
hasWarGoalAgainst stmt@[pdx| %_ = $txt |] = withFlag MsgHasWargoalAgainst stmt
hasWarGoalAgainst stmt@[pdx| %_ = @scr |] = textAtom "target" "type" MsgHasWargoalAgainstType tryLoc stmt
hasWarGoalAgainst stmt = preStatement stmt

-------------------------------------
-- Handler for diplomatic_relation --
-------------------------------------
foldCompound "diplomaticRelation" "DiplomaticRelation" "dr"
    []
    [CompField "country" [t|Text|] Nothing True
    ,CompField "relation" [t|Text|] Nothing True
    ,CompField "active" [t|Text|] Nothing False
    ]
    [|  do
        let active = case _active of
                Just "no" -> False
                Just "yes" -> True
                _ -> True
            relation = case _relation of
                "non_aggression_pact" -> if active then "Enters a {{icon|nap|1}} with " else "Disbands the {{icon|nap|1}} with "
                "guarantee" -> if active then "Grants a guarantee of independence for " else "Cancels it's guarantee of independence for "
                "puppet" -> if active then "Becomes a subject of " else "Is no longer a subject of "
                "military_access" -> if active then "Grants military access for " else "Revokes military access for "
                "docking_rights" -> if active then "Grants docking rights for " else "Revokes docking rights for "
                _ -> "<!-- Check Script -->"
        flag <- flagText (Just HOI4Country) _country
        return $ MsgDiplomaticRelation relation flag
    |]

hasArmySize :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
hasArmySize stmt@[pdx| %_ = @scr |] = do
    let (_size, _) = extractStmt (matchLhsText "size") scr
        (_type, _) = extractStmt (matchLhsText "type") scr
    (comp, amt) <- case _size of
        Just [pdx| %_ < !num |] -> return ("less than", num)
        Just [pdx| %_ > !num |] -> return ("more than", num)
        _ -> return ("<!-- Check Script -->", 0)
    typed <- case _type of
        Just [pdx| %_ = $txt |] -> if txt == "anti_tank" then return " anti-tank" else return $ " " <> txt
        _ -> return " "
    msgToPP $ MsgHasArmySize comp amt typed
hasArmySize stmt = preStatement stmt

startCivilWar :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
startCivilWar stmt@[pdx| %_ = @scr |] = do
    let (_ideology, _) = extractStmt (matchLhsText "ideology") scr
        (_size, _) = extractStmt (matchLhsText "size") scr
    size <- case _size of
        Just [pdx| %_ = !num |] -> return $ Doc.doc2text (reducedNum (colourPc False) num)
        Just [pdx| %_ = ?var |] -> return var
        _ -> return "<!-- Check Script -->"
    ideology <- case _ideology of
        Just [pdx| %_ = $txt |] -> getGameL10n txt
        _ -> return "<!-- Check Script -->"
    msgToPP $ MsgStartCivilWar ideology size
startCivilWar stmt = preStatement stmt

createEquipmentVariant :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
createEquipmentVariant stmt@[pdx| %_ = @scr |] = do
    let (_name, _) = extractStmt (matchLhsText "name") scr
        (_typed, _) = extractStmt (matchLhsText "type") scr
    name <- case _name of
        Just [pdx| %_ = ?txt |] -> return txt
        _ -> return "<!-- Check Script -->"
    typed <- case _typed of
        Just [pdx| %_ = $txt |] -> getGameL10n txt
        _ -> return "<!-- Check Script -->"
    msgToPP $ MsgCreateEquipmentVariant typed name
createEquipmentVariant stmt = preStatement stmt

-- | Handler for set_rule
setRule :: forall g m. (HOI4Info g, Monad m) =>
    (Double -> ScriptMessage) -- ^ Message to use as the block header
    -> StatementHandler g m
setRule header [pdx| %_ = @scr |]
    = withCurrentIndent $ \i -> do
        rules_pp'd <- ppRules scr
        let numrules = fromIntegral $ length scr
        return ((i, header numrules) : rules_pp'd)
    where
        ppRules :: GenericScript -> PPT g m IndentedMessages
        ppRules scr = indentUp (concat <$> mapM ppRule scr)
        ppRule :: StatementHandler g m
        ppRule stmt@[pdx| $lhs = ?yn |] =
            case yn of
                "yes" -> do
                    let lhst = T.toUpper lhs
                    loc <- getGameL10n lhst
                    msgToPP $ MsgSetRuleYesNo "{{icon|yes}}" loc
                "no" -> do
                    let lhst = T.toUpper lhs
                    loc <- getGameL10n lhst
                    msgToPP $ MsgSetRuleYesNo "{{icon|no}}" loc
                _ -> preStatement stmt
        ppRule stmt = trace ("unknownsecton found in set_rule for " ++ show stmt) preStatement stmt
setRule _ stmt = preStatement stmt

-------------------------------------
-- Handler for add_doctrine_cost_reduction  --
-------------------------------------
data DoctrineCostReduction = DoctrineCostReduction
        {   dcr_name :: Maybe Text
        ,   dcr_cost_reduction :: Double
        ,   dcr_uses :: Double
        ,   dcr_category :: [Text]
        ,   dcr_technology :: [Text]
        }
newDCR :: DoctrineCostReduction
newDCR = DoctrineCostReduction Nothing undefined 1 [] []
addDoctrineCostReduction :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
addDoctrineCostReduction stmt@[pdx| %_ = @scr |]
    = pp_dcr =<< foldM addLine newDCR scr
    where
        addLine :: DoctrineCostReduction -> GenericStatement -> PPT g m DoctrineCostReduction
        addLine dcr [pdx| name = $name |] = do
            nameloc <- getGameL10n name
            return dcr { dcr_name = Just nameloc }
        addLine dcr [pdx| cost_reduction = !amt |] =
            return dcr { dcr_cost_reduction = amt }
        addLine dcr [pdx| uses = !amt  |]
            = return dcr { dcr_uses = amt }
        addLine dcr [pdx| category = $cat |] = do
            let oldcat = dcr_category dcr
            catloc <- getGameL10n cat
            return dcr { dcr_category = oldcat ++ [catloc] }
        addLine dcr [pdx| technology = $tech |] = do
            let oldtech = dcr_technology dcr
            techloc <- getGameL10n tech
            return dcr { dcr_technology = oldtech ++ [techloc] }
        addLine dcr _ = return dcr
        pp_dcr :: DoctrineCostReduction -> PPT g m IndentedMessages
        pp_dcr dcr = do
            let techcat = dcr_category dcr ++ dcr_technology dcr
                ifname = case dcr_name dcr of
                    Just name -> "(" <> italicText name <> ") "
                    _ -> ""
                dcrmsg =  MsgAddDoctrineCostReduction (dcr_uses dcr) (dcr_cost_reduction dcr) ifname
            techcatmsg <- mapM (\tc ->withCurrentIndent $ \i -> return [(i+1, MsgUnprocessed tc)]) techcat
            dcrmsg_pp <- msgToPP dcrmsg
            return $ dcrmsg_pp ++ concat techcatmsg
addDoctrineCostReduction stmt = preStatement stmt

-------------------------------------
-- Handler for free_building_slots --
-------------------------------------
data FreeBuildingSlots = FreeBuildingSlots
        {   fbs_building :: Text
        ,   fbs_size :: Double
        ,   fbs_comp :: Text
        ,   fbs_include_locked :: Bool
        }

newFBS :: FreeBuildingSlots
newFBS = FreeBuildingSlots undefined undefined undefined False
freeBuildingSlots  :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
freeBuildingSlots stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_fbs =<< foldM addLine newFBS scr
    where
        addLine :: FreeBuildingSlots -> GenericStatement -> PPT g m FreeBuildingSlots
        addLine fbs [pdx| building = $txt |] = do
            txtd <- getGameL10n txt
            return fbs { fbs_building = txtd }
        addLine fbs [pdx| size < !amt |] =
            let comp = "less than" in
            return fbs { fbs_comp = comp, fbs_size = amt }
        addLine fbs [pdx| size > !amt |] =
            let comp = "more than" in
            return fbs { fbs_comp = comp, fbs_size = amt}
        addLine fbs [pdx| include_locked = %_ |] =
            return fbs { fbs_include_locked = True }
        addLine fbs stmt
            = trace ("unknown section in free_building_slots: " ++ show stmt) $ return fbs
        pp_fbs fbs = do
            return $ MsgFreeBuildingSlots (fbs_comp fbs) (fbs_size fbs) (fbs_building fbs) (fbs_include_locked fbs)
freeBuildingSlots stmt = preStatement stmt

addAutonomyRatio :: forall g m. (HOI4Info g, Monad m) =>
    (Text -> Text -> Double -> ScriptMessage) -> (Text -> Text -> Text -> ScriptMessage) -> StatementHandler g m
addAutonomyRatio valmsg varmsg stmt@[pdx| %_ = @scr |] = case length scr of
    2 -> textValue "localization" "value" valmsg varmsg tryLocMaybe stmt
    1 -> do
        let (_value, _) = extractStmt (matchLhsText "value") scr
        case _value of
            Just [pdx| %_ = !num |] -> msgToPP $ valmsg "" "" num
            Just [pdx| %_ = $var |] -> msgToPP $ varmsg "" "" var
            _ -> preStatement stmt
    _ -> preStatement stmt
addAutonomyRatio _ _ stmt = preStatement stmt

--------------------------------
-- Handler for send_equipment --
--------------------------------
data SendEquipment = SendEquipment
        {   se_equipment :: Text
        ,   se_amount :: Text
        ,   se_old_prioritised :: Bool
        ,   se_target :: Maybe Text
        }

newSE :: SendEquipment
newSE = SendEquipment undefined undefined False Nothing
sendEquipment  :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
sendEquipment stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_se =<< foldM addLine newSE scr
    where
        addLine :: SendEquipment -> GenericStatement -> PPT g m SendEquipment
        addLine se [pdx| equipment = $txt |] = do
            txtd <- getGameL10n txt
            return se { se_equipment = txtd }
        addLine se [pdx| type = $txt |] = do
            txtd <- getGameL10n txt
            return se { se_equipment = txtd }
        addLine se [pdx| amount = !amt |] =
            let amtd = T.pack $ show (amt :: Int)  in
            return se { se_amount = amtd }
        addLine se [pdx| amount = $amt |] =
            return se { se_amount = amt }
        addLine se [pdx| old_prioritised = %rhs |]
            | GenericRhs "yes" [] <- rhs = return se { se_old_prioritised = True }
            | GenericRhs "no"  [] <- rhs = return se { se_old_prioritised = False }
        addLine se [pdx| target = $vartag:$var |] = do
            flagd <- eflag (Just HOI4Country) (Right (vartag,var))
            return se { se_target = flagd }
        addLine se [pdx| target = $tag |] = do
            flagd <- eflag (Just HOI4Country) (Left tag)
            return se { se_target = flagd }
        addLine se stmt
            = trace ("unknown section in send_equipment: " ++ show stmt) $ return se
        pp_se se = do
            let target = fromMaybe "<!-- Check Script -->" (se_target se)
            return $ MsgSendEquipment (se_amount se) (se_equipment se) target (se_old_prioritised se)
sendEquipment stmt = preStatement stmt

--------------------------------
-- Handler for build_railway --
--------------------------------
data BuildRailway = BuildRailway
        {   br_level :: Double
        ,   br_build_only_on_allied :: Bool
        ,   br_fallback :: Bool
        ,   br_path :: Maybe [Double]
        ,   br_start_state :: Maybe Text
        ,   br_target_state :: Maybe Text
        ,   br_start_province :: Maybe Double
        ,   br_target_province :: Maybe Double
        }

newBR :: BuildRailway
newBR = BuildRailway 1 False False Nothing Nothing Nothing Nothing Nothing
buildRailway  :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
buildRailway stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_br =<< foldM addLine newBR scr
    where
        addLine :: BuildRailway -> GenericStatement -> PPT g m BuildRailway
        addLine br [pdx| $lhs = %rhs |] = case lhs of
            "level" -> case rhs of
                (floatRhs -> Just num) -> return br { br_level = num }
                _ -> trace "bad level in build_railway" $ return br
            "build_only_on_allied" -> return br
            "fallback" -> return br
            "controller_priority" -> return br
            "path" -> case rhs of
                CompoundRhs arr ->
                    let provs = mapMaybe provinceFromArray arr in
                    return br { br_path = Just provs }
                _ -> trace "bad path in build_railway" $ return br
            "start_state" -> case rhs of
                IntRhs num -> do
                    stateloc <- getStateLoc num
                    return br { br_start_state = Just stateloc }
                GenericRhs vartag [var] -> do
                    stated <- eGetState (Right (vartag,var))
                    return br { br_start_state = stated }
                GenericRhs txt [] -> do
                    stated <- eGetState (Left txt)
                    return br { br_start_state = stated }
                _ -> trace "bad start_state in build_railway" $ return br
            "target_state" -> case rhs of
                IntRhs num -> do
                    stateloc <- getStateLoc num
                    return br { br_target_state = Just stateloc }
                GenericRhs vartag [var] -> do
                    stated <- eGetState (Right (vartag, var))
                    return br { br_target_state = stated }
                GenericRhs txt [] -> do
                    stated <- eGetState (Left txt)
                    return br { br_target_state = stated }
                _ -> trace "bad target_state in build_railway" $ return br

            "start_province" ->
                    return br { br_start_province = floatRhs rhs }
            "target_province" ->
                    return br { br_target_province = floatRhs rhs }
            other -> trace ("unknown section in build_railway: " ++ show stmt) $ return br
        addLine br stmt
            = trace ("unknown form in build_railway: " ++ show stmt) $ return br
        provinceFromArray :: GenericStatement -> Maybe Double
        provinceFromArray (StatementBare (IntLhs e)) = Just $ fromIntegral e
        provinceFromArray stmt = trace ("Unknown in generator array statement: " ++ show stmt) Nothing
        pp_br br = do
            case br_path br of
                Just path -> do
                    let paths = T.pack $ concat ["on the provinces (" , intercalate "), (" (map (show . round) path),")"]
                    return $ MsgBuildRailwayPath (br_level br) paths
                _ -> case (br_start_state br, br_target_state br,
                           br_start_province br, br_target_province br) of
                        (Just start, Just end, _,_) -> return $ MsgBuildRailway (br_level br) start end
                        (_,_, Just start, Just end) -> return $ MsgBuildRailwayProv (br_level br) start end
                        _ -> return $ preMessage stmt
buildRailway stmt = preStatement stmt

data CanBuildRailway = CanBuildRailway
        {   cbr_start_state :: Maybe Text
        ,   cbr_target_state :: Maybe Text
        ,   cbr_start_province :: Maybe Double
        ,   cbr_target_province :: Maybe Double
        }

newCBR :: CanBuildRailway
newCBR = CanBuildRailway Nothing Nothing Nothing Nothing
canBuildRailway  :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
canBuildRailway stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_cbr =<< foldM addLine newCBR scr
    where
        addLine :: CanBuildRailway -> GenericStatement -> PPT g m CanBuildRailway
        addLine cbr [pdx| $lhs = %rhs |] = case lhs of
            "start_state" -> case rhs of
                IntRhs num -> do
                    stateloc <- getStateLoc num
                    return cbr { cbr_start_state = Just stateloc }
                GenericRhs vartag [var] -> do
                    stated <- eGetState (Right (vartag,var))
                    return cbr { cbr_start_state = stated }
                GenericRhs txt [] -> do
                    stated <- eGetState (Left txt)
                    return cbr { cbr_start_state = stated }
                _ -> trace "bad start_state in build_railway" $ return cbr
            "target_state" -> case rhs of
                IntRhs num -> do
                    stateloc <- getStateLoc num
                    return cbr { cbr_target_state = Just stateloc }
                GenericRhs vartag [var] -> do
                    stated <- eGetState (Right (vartag, var))
                    return cbr { cbr_target_state = stated }
                GenericRhs txt [] -> do
                    stated <- eGetState (Left txt)
                    return cbr { cbr_target_state = stated }
                _ -> trace "bad target_state in build_railway" $ return cbr

            "start_province" ->
                    return cbr { cbr_start_province = floatRhs rhs }
            "target_province" ->
                    return cbr { cbr_target_province = floatRhs rhs }
            "build_only_on_allied" -> return cbr
            other -> trace ("unknown section in can_build_railway: " ++ show stmt) $ return cbr
        addLine cbr stmt
            = trace ("unknown form in can_build_railway: " ++ show stmt) $ return cbr
        pp_cbr cbr =
            case (cbr_start_state cbr, cbr_target_state cbr,
                           cbr_start_province cbr, cbr_target_province cbr) of
                        (Just start, Just end, _,_) -> return $ MsgCanBuildRailway start end
                        (_,_, Just start, Just end) -> return $ MsgCanBuildRailwayProv start end
                        _ -> return $ preMessage stmt
canBuildRailway stmt = preStatement stmt

------------------------------
-- Handler for add_resource --
------------------------------
data AddResource = AddResource
        {   ar_type :: Text
        ,   ar_amount :: Maybe Double
        ,   ar_amountvar :: Maybe Text
        ,   ar_state :: Maybe Double
        }

newAR :: AddResource
newAR = AddResource undefined Nothing Nothing Nothing
addResource  :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
addResource stmt@[pdx| %_ = @scr |]
    = msgToPP =<< pp_ar =<< foldM addLine newAR scr
    where
        addLine :: AddResource -> GenericStatement -> PPT g m AddResource
        addLine ar [pdx| type = $txt |] = return ar { ar_type = txt }
        addLine ar [pdx| amount = !num |] = return ar { ar_amount = Just num }
        addLine ar [pdx| amount = $txt |] = return ar { ar_amountvar = Just txt }
        addLine ar [pdx| state = !num |] = return ar { ar_state = Just num }
        addLine ar [pdx| $other = %_ |] = trace ("unknown section in add_resource: " ++ show other) $ return ar
        addLine ar stmt = trace ("unknown form in add_resource: " ++ show stmt) $ return ar
        pp_ar ar = do
            let buildicon = iconText $ ar_type ar
            stateloc <- maybe (return "") (getStateLoc . round) $ ar_state ar
            buildloc <- getGameL10n $ "PRODUCTION_MATERIALS_" <> T.toUpper (ar_type ar)
            case (ar_amount ar, ar_amountvar ar) of
                    (Just amount, _) -> return $ MsgAddResource buildicon buildloc amount stateloc
                    (_, Just amountvar) -> return $ MsgAddResourceVar buildicon buildloc amountvar stateloc
                    _ -> return $ preMessage stmt
addResource stmt = preStatement stmt

-------------------------------------------
-- Handler for modify_building_resources --
-------------------------------------------
foldCompound "modifyBuildingResources" "ModifyBuildingResources" "mbr"
    []
    [CompField "building" [t|Text|] Nothing True
    ,CompField "resource" [t|Text|] Nothing True
    ,CompField "amount" [t|Double|] Nothing True
    ]
    [|  do
        let buildicon = iconText _building
            resourceicon = iconText _resource
        return $ MsgModifyBuildingResources buildicon resourceicon _amount
    |]

----------
-- date --
----------


handleDate :: (Monad m, HOI4Info g) =>
    Text -> Text -> StatementHandler g m
handleDate after before  stmt@[pdx| %_ = %date |] = case date of
    DateRhs Date {year = year, month = month, day = day} -> do
        monthloc <- isMonth month
        msgToPP $ MsgDate after monthloc (fromIntegral day) (fromIntegral year)
    _ -> preStatement stmt
handleDate after before stmt@[pdx| %_ > %date |] = case date of
    DateRhs Date {year = year, month = month, day = day} ->  do
        monthloc <- isMonth month
        msgToPP $ MsgDate after monthloc (fromIntegral day) (fromIntegral year)
    _ -> preStatement stmt
handleDate after before stmt@[pdx| %_ < %date |] = case date of
    DateRhs Date {year = year, month = month, day = day} ->  do
        monthloc <- isMonth month
        msgToPP $ MsgDate before monthloc (fromIntegral day) (fromIntegral year)
    _ -> preStatement stmt
handleDate _ _ stmt = preStatement stmt


isMonth :: (IsGameData (GameData g), Monad m) =>
    Int -> PPT g m Text
isMonth month
    = getGameL10n $ case month of
            1 -> "January"
            2 -> "February"
            3 -> "March"
            4 -> "April"
            5 -> "May"
            6 -> "June"
            7 -> "July"
            8 -> "August"
            9 -> "September"
            10 -> "October"
            11 -> "November"
            12 -> "December"
            0 -> "" -- no programmer counting, is used when only year is used to check
            14 -> "14th month for some reason" -- for some reason there is a month 14, but not idea why and what for.
            _ -> error ("impossible: tried to localize bad month number" ++ show month)

setTechnology :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
setTechnology stmt@[pdx| %_ = @scr |] =
        let (_, rest) = extractStmt (matchLhsText "popup") scr in
        mapM (\case
            stmt2@[pdx| $tech = !addrm |] -> do
                mtechloc <- getGameL10nIfPresent tech
                case mtechloc of
                    Just techloc -> msgToPP' $ MsgSetTechnology addrm techloc
                    _ -> msgToPP' $ MsgSetTechnology addrm (typewriterText tech)
            unknowntechformat -> msgToPP' $ preMessage unknowntechformat)
            rest
setTechnology stmt = preStatement stmt

setCapital :: forall g m. (HOI4Info g, Monad m) =>
    (Text -> ScriptMessage) -> StatementHandler g m
setCapital msg stmt@[pdx| %_ = @scr |] =
        let (_, rest) = extractStmt (matchLhsText "remember_old_capital") scr in
        case rest of
            [[pdx| state = !state |]] -> do
                stateloc <- getStateLoc state
                msgToPP $ msg stateloc
            [[pdx| state = $state |]] -> do
                stated <- eGetState (Left state)
                let stateloc = fromMaybe "<!-- Check Script -->"  stated
                msgToPP $ msg stateloc
            [[pdx| state = $vartag:$var |]] -> do
                stated <- eGetState (Right (vartag, var))
                let stateloc = fromMaybe "<!-- Check Script -->"  stated
                msgToPP $ msg stateloc
            _ -> preStatement stmt
setCapital msg stmt = withFlag msg stmt


setPopularities :: (HOI4Info g, Monad m) => StatementHandler g m
setPopularities [pdx| %_ = @scr |] = do
    basemsg <- msgToPP MsgSetPopularities
    popmsg <- fold <$> indentUp (traverse getpops scr)
    return $ basemsg ++ popmsg
    where
        getpops stmt@[pdx| $ideo = !num |] = do
            ideoloc <- getGameL10n ideo
            msgToPP $ MsgSetPopularity ideo ideoloc num
        getpops stmt@[pdx| $ideo = ?txt |] = do
            ideoloc <- getGameL10n ideo
            msgToPP $ MsgSetPopularityVar ideo ideoloc txt
        getpops stmt = preStatement stmt
setPopularities stmt = preStatement stmt

------------------------------
-- Handler for add_equipment_to_stockpile --
------------------------------
data AddEquipment = AddEquipment
        {   ae_type :: Text
        ,   ae_amount :: Maybe Double
        ,   ae_amountvar :: Maybe Text
        ,   ae_producer :: Maybe (Either Text (Text, Text))
        ,   ae_variant :: Maybe Text
        }

newAE :: AddEquipment
newAE = AddEquipment undefined Nothing Nothing Nothing Nothing
addEquipment  :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
addEquipment stmt@[pdx| %_ = @scr |]
    = msgToPP =<< ppAe =<< foldM addLine newAE scr
    where
        addLine :: AddEquipment -> GenericStatement -> PPT g m AddEquipment
        addLine ae [pdx| type = ?txt |] = return ae { ae_type = txt }
        addLine ae [pdx| amount = !num |] = return ae { ae_amount = Just num }
        addLine ae [pdx| amount = ?txt |] = return ae { ae_amountvar = Just txt }
        addLine ae [pdx| producer = ?tag |] = return ae { ae_producer = Just (Left tag) }
        addLine ae [pdx| producer = $vartag:$var |] = return ae { ae_producer = Just (Right (vartag, var)) }
        addLine ae [pdx| variant_name = ?txt |] = return ae { ae_variant = Just txt }
        addLine ae [pdx| $other = %_ |] = trace ("unknown section in add_equipment_to_stockpile: " ++ show other) $ return ae
        addLine ae stmt = trace ("unknown form in add_equipment_to_stockpile: " ++ show stmt) $ return ae
        ppAe ae = do
            let variant = fromMaybe "" $ ae_variant ae
            flaglocm <- case ae_producer ae of
                Just producer -> eflag (Just HOI4Country) producer
                _ -> return Nothing
            let flagloc = fromMaybe "" flaglocm
            equiploc <- getGameL10n $ ae_type ae
            case (ae_amount ae, ae_amountvar ae) of
                    (Just amount, _) -> return $ MsgAddEquipmentToStockpile amount flagloc equiploc variant
                    (_, Just amountvar) -> return $ MsgAddEquipmentToStockpileVar amountvar flagloc equiploc variant
                    _ -> return $ preMessage stmt
addEquipment stmt = preStatement stmt

--------------------------------------
-- Handler for give_resource_rights --
--------------------------------------
data GiveRights = GiveRights
        {   gr_receiver :: Text
        ,   gr_state :: Maybe Int
        ,   gr_statevar :: Maybe Text
        }

newGR :: GiveRights
newGR = GiveRights undefined Nothing Nothing
giveResourceRights :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
giveResourceRights stmt@[pdx| %_ = @scr |]
    = msgToPP =<< ppGR =<< foldM addLine newGR scr
    where
        addLine :: GiveRights -> GenericStatement -> PPT g m GiveRights
        addLine gr [pdx| receiver = ?txt |] = return gr { gr_receiver = txt }
        addLine gr [pdx| state = !num |] = return gr { gr_state = Just num }
        addLine gr [pdx| state = ?txt |] = return gr { gr_statevar = Just txt }
        addLine gr [pdx| $other = %_ |] = trace ("unknown section in give_resource_rights: " ++ show other) $ return gr
        addLine gr stmt = trace ("unknown form in give_resource_rights: " ++ show stmt) $ return gr
        ppGR :: GiveRights -> PPT g m ScriptMessage
        ppGR gr = do
            flag_loc <- flagText (Just HOI4Country) (gr_receiver gr)
            case (gr_state gr, gr_statevar gr) of
                (Just state, _) -> do
                    state_loc <- getStateLoc state
                    return $ MsgGiveResourceRights flag_loc state_loc
                (_, Just state) -> do
                    mstate <- eGetState (Left state)
                    let state_loc = fromMaybe "<!-- Check Script -->" mstate
                    return $ MsgGiveResourceRights flag_loc state_loc
                _ -> return $ preMessage stmt
giveResourceRights stmt = preStatement stmt

--------------------------------------
-- Handler for add_ace --
--------------------------------------

data AddAce = AddAce
        {   aa_name :: Text
        ,   aa_surname :: Text
        ,   aa_callsign :: Text
        }

newAA :: AddAce
newAA = AddAce undefined undefined undefined
addAce  :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
addAce stmt@[pdx| %_ = @scr |]
    = msgToPP =<< ppAa =<< foldM addLine newAA scr
    where
        addLine :: AddAce -> GenericStatement -> PPT g m AddAce
        addLine aa [pdx| name = ?txt |] = return aa { aa_name = txt }
        addLine aa [pdx| surname = ?txt |] = return aa { aa_surname = txt }
        addLine aa [pdx| callsign = ?txt |] = return aa { aa_callsign = txt }
        addLine aa [pdx| type = ?_ |] = return aa
        addLine aa [pdx| is_female = ?_ |] = return aa
        addLine aa [pdx| $other = %_ |] = trace ("unknown section in add_ace: " ++ show other) $ return aa
        addLine aa stmt = trace ("unknown form in add_ace: " ++ show stmt) $ return aa
        ppAa aa = do
            return $ MsgAddAce (aa_name aa) (aa_callsign aa) (aa_surname aa)
addAce stmt = preStatement stmt

-------------------------------
-- Handler for has_navy_size --
------------------------------

data NavySize = NavySize
        {   ns_size :: Maybe Double
        ,   ns_sizevar :: Maybe Text
        ,   ns_comp :: Text
        ,   ns_type :: Maybe Text
        ,   ns_archetype :: Maybe Text
        }

newNS :: NavySize
newNS = NavySize Nothing Nothing undefined Nothing Nothing

hasNavySize :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
hasNavySize stmt@[pdx| %_ = @scr |]
    = msgToPP =<< ppNS =<< foldM addLine newNS scr
    where
        addLine :: NavySize -> GenericStatement -> PPT g m NavySize
        addLine ns [pdx| size < !num |] = return ns { ns_comp = "less than", ns_size = Just num}
        addLine ns [pdx| size > !num |] = return ns { ns_comp = "more than", ns_size = Just num }
        addLine ns [pdx| size < $num |] = return ns { ns_comp = "less than", ns_sizevar = Just num}
        addLine ns [pdx| size > $num |] = return ns { ns_comp = "more than", ns_sizevar = Just num }
        addLine ns [pdx| type = $txt |] = return ns { ns_type = Just txt }
        addLine ns [pdx| unit = $txt |] = return ns { ns_type = Just txt }
        addLine ns [pdx| archetype = ?txt |] = return ns { ns_archetype = Just txt }
        addLine ns [pdx| $other = %_ |] = trace ("unknown section in has_navy_size: " ++ show other) $ return ns
        addLine ns stmt = trace ("unknown form in has_navy_size: " ++ show stmt) $ return ns
        ppNS ns = do
            typed <- case(ns_type ns, ns_archetype ns) of
                (Just txt, _) -> getGameL10n txt
                (_, Just txt) -> getGameL10n txt
                _ -> return ""
            case (ns_size ns, ns_sizevar ns) of
                (Just amt, _) -> return $ MsgHasNavySize (ns_comp ns) amt typed
                (_, Just amt) -> return $ MsgHasNavySizeVar (ns_comp ns) amt typed
                _ -> return $ preMessage stmt
hasNavySize stmt = preStatement stmt

-----------------------------------
-- Handler for division_template --
-----------------------------------

divisionTemplate :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
divisionTemplate stmt@[pdx| %_ = @scr |] = do
    let (mname, _) = extractStmt (matchLhsText "name") scr
    case mname of
        Just [pdx| %_ = ?txt |] -> msgToPP $ MsgDivisionTemplate txt
        _ -> preStatement stmt
divisionTemplate  stmt = preStatement stmt

locandid :: (Monad m, HOI4Info g) =>
    (Text -> Text -> ScriptMessage) -> StatementHandler g m
locandid msg [pdx| %_ = ?key |] = do
    loc <- getGameL10n key
    msgToPP $ msg loc key
locandid _ stmt = preStatement stmt

-----------------------------
-- Handler for create_unit --
-----------------------------

createUnit :: (Monad m, HOI4Info g) => StatementHandler g m
createUnit stmt@[pdx| %_ = @scr |] = do
    let (division,rest) = extractStmt (matchLhsText "division") scr
        (owner, _) = extractStmt (matchLhsText "owner") rest
    divis <- case division of
        Just [pdx| %_ = ?txt |] -> do
            let divtempi = fromMaybe 0 $ findString "division_template" txt
                divtemps = T.drop 1 $ T.dropWhile (/= '\"') (T.drop divtempi txt)
            return $ T.dropEnd 1 (T.dropWhileEnd (/= '\"') divtemps)
        _ -> return "<!-- Check game Script -->"
    owner <- case owner of
        Just [pdx| %_ = ?txt |] -> flagText (Just HOI4Country) txt
        _ -> return "<!-- Check game Script -->"
    msgToPP $ MsgCreateUnit owner divis
    where
    findString :: Text -> Text -> Maybe Int
    findString search str = findIndex (T.isPrefixOf search) (T.tails str)
createUnit stmt = preStatement stmt

---------------------------------
-- Handler for damage_building --
---------------------------------

data DamageBuilding = DamageBuilding
        {   db_type :: Text
        ,   db_damage :: Maybe Double
        ,   db_damagevar :: Maybe Text
        ,   db_province :: Maybe Double
        }

newDB :: DamageBuilding
newDB = DamageBuilding undefined Nothing Nothing Nothing

damageBuilding :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
damageBuilding stmt@[pdx| %_ = @scr |]
    = msgToPP =<< ppDB =<< foldM addLine newDB scr
    where
        addLine :: DamageBuilding -> GenericStatement -> PPT g m DamageBuilding
        addLine db [pdx| type = ?txt |] = return db { db_type = txt }
        addLine db [pdx| damage = !num |] = return db { db_damage = Just num }
        addLine db [pdx| damage = $txt |] = return db { db_damagevar = Just txt }
        addLine db [pdx| province = !num |] = return db {db_province = Just num}
        addLine db [pdx| $other = %_ |] = trace ("unknown section in damage_building: " ++ show other) $ return db
        addLine db stmt = trace ("unknown form in damage_building: " ++ show stmt) $ return db
        ppDB db = do
            let typeicon = iconText (db_type db)
                prov = fromMaybe (-1) (db_province db)
            typeloc <- getGameL10n (db_type db)
            case (db_damage db, db_damagevar db) of
                (Just amt, _) -> return $ MsgDamageBuilding typeicon typeloc amt prov
                (_, Just amt) -> return $ MsgDamageBuildingVar typeicon typeloc amt prov
                _ -> return $ preMessage stmt
damageBuilding stmt = preStatement stmt

------ region handler -----

withRegion :: (HOI4Info g, Monad m) =>
        StatementHandler g m
withRegion stmt@[pdx| %lhs = $vartag:$var |] = do
    mtagloc <- tagged vartag var
    case mtagloc of
        Just tagloc -> msgToPP $ MsgRegion tagloc
        Nothing -> preStatement stmt
withRegion stmt@[pdx| %lhs = $var |]
    = msgToPP $ MsgRegion ("<tt>" <> var <> "</tt>" )
withRegion [pdx| %lhs = !stateid |]
    = msgToPP . MsgRegion =<< getRegionLoc stateid
withRegion stmt = preStatement stmt

getRegionLoc :: (IsGameData (GameData g), Monad m) =>
    Int -> PPT g m Text
getRegionLoc n = do
    let regionid_t = T.pack (show n)
    mregionloc <- getGameL10nIfPresent ("STRATEGICREGION_" <> regionid_t)
    return $ case mregionloc of
        Just loc -> boldText loc <> " (" <> regionid_t <> ")"
        _ -> "Region" <> regionid_t

------------------------------------
-- handler for divisions_in_state --
------------------------------------

data DivisionsInState = DivisionsInState
        {   ds_size :: Double
        ,   ds_comp :: Text
        ,   ds_type :: Maybe Text
        ,   ds_state :: Maybe Int
        ,   ds_statevar :: Maybe (Either Text (Text, Text))
        ,   ds_border_state :: Maybe Int
        ,   ds_border_statevar :: Maybe (Either Text (Text, Text))
        }

newDS :: DivisionsInState
newDS = DivisionsInState undefined undefined Nothing Nothing Nothing Nothing Nothing

divisionsInState :: forall g m. (HOI4Info g, Monad m) =>
    (Text -> Double -> Text -> Text -> Text -> ScriptMessage) -> StatementHandler g m
divisionsInState msg stmt@[pdx| %_ = @scr |]
    = msgToPP =<< ppDS =<< foldM addLine newDS scr
    where
        addLine :: DivisionsInState -> GenericStatement -> PPT g m DivisionsInState
        addLine ds [pdx| size > !num |] = return ds { ds_comp = "more than", ds_size = num }
        addLine ds [pdx| size < !num |] = return ds { ds_comp = "less than", ds_size = num }
        addLine ds [pdx| amount > !num |] = return ds { ds_comp = "more than", ds_size = num }
        addLine ds [pdx| amount < !num |] = return ds { ds_comp = "less than", ds_size = num }
        addLine ds [pdx| type = $txt |] = return ds { ds_type = Just txt }
        addLine ds [pdx| state = !num |] = return ds {ds_state = Just num}
        addLine ds [pdx| state = $vartag:$var |] = return ds { ds_statevar = Just (Right (vartag,var))}
        addLine ds [pdx| state = $var |] = return ds { ds_statevar = Just (Left var)}
        addLine ds [pdx| border_state = !num |] = return ds { ds_border_state = Just num}
        addLine ds [pdx| border_state = $vartag:$var |] = return ds { ds_border_statevar = Just (Right (vartag,var))}
        addLine ds [pdx| border_state = $var |] = return ds { ds_border_statevar = Just (Left var)}
        addLine ds [pdx| $other = %_ |] = trace ("unknown section in divisionsInState: " ++ show other) $ return ds
        addLine ds stmt = trace ("unknown form in divisionsInState: " ++ show stmt) $ return ds
        ppDS :: DivisionsInState -> PPT g m ScriptMessage
        ppDS ds = do
            borderstate <- case (ds_border_state ds, ds_border_statevar ds) of
                (Just state,_) -> getStateLoc state
                (_,Just (Left state)) -> do
                    mstate <- eGetState (Left state)
                    return $ fromMaybe "<!-- Check Script -->" mstate
                (_,Just (Right state)) -> do
                    mstate <- eGetState (Right state)
                    return $ fromMaybe "<!-- Check Script -->" mstate
                _-> return "<!-- Check Script -->"
            typeloc <- maybe (return "") getGameL10n (ds_type ds)
            stateloc <- case (ds_state ds, ds_statevar ds) of
                (Just state,_) -> getStateLoc state
                (_,Just (Left state)) -> do
                    mstate <- eGetState (Left state)
                    return $ fromMaybe "" mstate
                (_,Just (Right state)) -> do
                    mstate <- eGetState (Right state)
                    return $ fromMaybe "" mstate
                _-> return ""
            return $ msg (ds_comp ds) (ds_size ds) typeloc stateloc borderstate
divisionsInState _ stmt = preStatement stmt

-------------------------------------------------------
-- handler for delete_units and delete_unit_template --
-------------------------------------------------------

data DeleteUnits = DeleteUnits
        {   du_division_template :: Maybe Text
        ,   du_disband :: Bool
        ,   du_state :: Maybe Text
        }

newDU :: DeleteUnits
newDU = DeleteUnits Nothing False Nothing

deleteUnits :: forall g m. (HOI4Info g, Monad m) =>
    (Bool -> Text -> Text -> ScriptMessage) -> StatementHandler g m
deleteUnits msg stmt@[pdx| %_ = @scr |]
    = msgToPP =<< ppDU =<< foldM addLine newDU scr
    where
        addLine :: DeleteUnits -> GenericStatement -> PPT g m DeleteUnits
        addLine du [pdx| division_template = ?txt |] = return du { du_division_template = Just txt }
        addLine du [pdx| disband = %rhs |]
            | GenericRhs "yes" [] <- rhs = return du { du_disband = True }
            | otherwise = return du
        addLine du [pdx| state = !num |] = do
            stateloc <- getStateLoc num
            return du { du_division_template = Just stateloc }
        addLine du [pdx| $other = %_ |] = trace ("unknown section in deleteUnits: " ++ show other) $ return du
        addLine du stmt = trace ("unknown form in deleteUnits: " ++ show stmt) $ return du
        ppDU :: DeleteUnits -> PPT g m ScriptMessage
        ppDU du = do
            return $ msg (du_disband du) (fromMaybe "" (du_division_template du)) (fromMaybe "" (du_state du))
deleteUnits _ stmt = preStatement stmt

----------------------------------
-- handler for start_border_war --
----------------------------------

data StartBorderWar = StartBorderWar
        {   sbw_change_state_after_war :: Bool
        ,   sbw_state_attacker :: Text
        ,   sbw_state_defender :: Text
        ,   sbw_on_win_attacker :: Text
        ,   sbw_on_win_defender :: Text
        ,   sbw_on_loss_attacker :: Text
        ,   sbw_on_loss_defender :: Text
        ,   sbw_on_cancel_attacker :: Text
        ,   sbw_on_cancel_defender :: Text
        }

newSBW :: StartBorderWar
newSBW = StartBorderWar False "<!--CHECK SCRIPT-->" "<!--CHECK SCRIPT-->" "<!--CHECK SCRIPT-->" "<!--CHECK SCRIPT-->" "<!--CHECK SCRIPT-->" "<!--CHECK SCRIPT-->" "<!--CHECK SCRIPT-->" "<!--CHECK SCRIPT-->"

startBorderWar :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
startBorderWar stmt@[pdx| %_ = @scr |]
    = ppSBW =<< foldM addLine newSBW scr
    where
        addLine :: StartBorderWar -> GenericStatement -> PPT g m StartBorderWar
        addLine sbw [pdx| change_state_after_war = %rhs |]
            | GenericRhs "yes" [] <- rhs = return sbw { sbw_change_state_after_war = True }
            | otherwise = return sbw
        addLine sbw [pdx| attacker = @scr |] = foldM (addLine' True) sbw scr
        addLine sbw [pdx| defender = @scr |] = foldM (addLine' False) sbw scr
        addLine sbw [pdx| $other = %_ |] = trace ("unknown section in startBorderWar: " ++ show other) $ return sbw
        addLine sbw stmt = trace ("unknown form in startBorderWar: " ++ show stmt) $ return sbw

        addLine' :: Bool -> StartBorderWar -> GenericStatement -> PPT g m StartBorderWar
        addLine' atde sbw [pdx| state = !num |] = do
            stateloc <- getStateLoc num
            if atde
            then return  sbw { sbw_state_attacker = stateloc }
            else return sbw { sbw_state_defender = stateloc }
        addLine' atde sbw [pdx| state = $txt |] = do
            if atde
            then return  sbw { sbw_state_attacker = txt }
            else return sbw { sbw_state_defender = txt }
        addLine' atde sbw [pdx| state = $vartag:$var |] = do
            if atde
            then return  sbw { sbw_state_attacker = var }
            else return sbw { sbw_state_defender = var }
        addLine' atde sbw [pdx| on_win = $eid |] = do
            if atde
            then return  sbw { sbw_on_win_attacker = eid }
            else return sbw { sbw_on_win_defender = eid }
        addLine' atde sbw [pdx| on_lose = $eid |] = do
            if atde
            then return  sbw { sbw_on_loss_attacker = eid }
            else return sbw { sbw_on_loss_defender = eid }
        addLine' atde sbw [pdx| on_cancel = $eid |] = do
            if atde
            then return  sbw { sbw_on_cancel_attacker = eid }
            else return sbw { sbw_on_cancel_defender = eid }
        addLine' atde sbw [pdx| num_provinces = %_ |] = return sbw
        addLine' _ sbw [pdx| $other = %_ |] = trace ("unknown section in startBorderWar@attdef: " ++ show other) $ return sbw
        addLine' _ sbw stmt = trace ("unknown form in startBorderWar@attdef: " ++ show stmt) $ return sbw
        ppSBW :: StartBorderWar -> PPT g m IndentedMessages
        ppSBW sbw = do
            headMsg <- msgToPP $ MsgStartBorderWar (sbw_state_attacker sbw) (sbw_state_defender sbw) (sbw_change_state_after_war sbw)
            bordEventMsgs <- do
                onwinmsg <- messageText MsgBorderWin
                onlossmsg <- messageText MsgBorderLoss
                oncancelmsg <- messageText MsgBorderCancel
                defmsg <- messageText MsgBorderDefender
                attmsg <- messageText MsgBorderAttacker
                let getevntloc eid = do
                        mloc <- getEventTitle eid
                        return $ fromMaybe eid mloc
                winattevt <- getevntloc (sbw_on_win_attacker sbw)
                windefevt <- getevntloc (sbw_on_win_defender sbw)
                lossattevt <- getevntloc (sbw_on_loss_attacker sbw)
                lossdefevt <- getevntloc (sbw_on_loss_defender sbw)
                cancattevt <- getevntloc (sbw_on_cancel_attacker sbw)
                cancdefevt <- getevntloc (sbw_on_cancel_defender sbw)
                msgwinatt <- indentUp $ msgToPP $ MsgTriggerBorderEvent onwinmsg (sbw_on_win_attacker sbw) winattevt attmsg
                msgwindeff <- indentUp $ msgToPP $ MsgTriggerBorderEvent onwinmsg (sbw_on_win_defender sbw) windefevt defmsg
                msglossatt <- indentUp $ msgToPP $ MsgTriggerBorderEvent onlossmsg (sbw_on_loss_attacker sbw) lossattevt attmsg
                msglossdef <- indentUp $ msgToPP $ MsgTriggerBorderEvent onlossmsg (sbw_on_loss_defender sbw) lossdefevt defmsg
                msgcancatt <- indentUp $ msgToPP $ MsgTriggerBorderEvent oncancelmsg (sbw_on_cancel_attacker sbw) cancattevt attmsg
                msgcancdef <- indentUp $ msgToPP $ MsgTriggerBorderEvent oncancelmsg (sbw_on_cancel_defender sbw) cancdefevt defmsg
                return $ msgwinatt ++ msgwindeff ++ msglossatt ++ msglossdef ++ msgcancatt ++ msgcancdef
            return $ headMsg ++ bordEventMsgs
startBorderWar stmt = preStatement stmt

---------------------------------------
-- handler for add_province_modifier --
---------------------------------------

data AddProvMod = AddProvMod{
      apm_modifier :: [Text]
    , apm_province :: Maybe [Double]
    , apm_province_all :: Bool
    , apm_province_coastal :: Bool
    , apm_province_naval :: Bool
    , apm_province_border :: Bool
    , apm_limit_to_victory_point :: Bool
    , apm_limit_to_victory_point_num :: Maybe Double
    , apm_limit_to_victory_point_comp :: Text
    } deriving Show

newAPM :: AddProvMod
newAPM = AddProvMod [] Nothing False False False False False Nothing ""

addProvinceModifier :: forall g m. (HOI4Info g, Monad m) => Bool -> StatementHandler g m
addProvinceModifier addrem stmt@[pdx| %_ = @scr |] =
    msgToPP =<< pp_apm (foldl' addLine newAPM scr)
    where
        addLine :: AddProvMod -> GenericStatement -> AddProvMod
        addLine apm [pdx| static_modifiers = @scr |] =
            let mods = mapMaybe getbaremods scr in
            apm { apm_modifier = mods }
        addLine apm [pdx| province = !num |] = apm { apm_province = Just [num] }
        addLine apm [pdx| province = @scr |] = foldl' addLine' apm scr
        addLine apm [pdx| $other = %_ |] = trace ("unknown section in add_province_modifier: " ++ show other) apm
        addLine apm stmt = trace ("Unknown in add_province_modifier: " ++ show stmt) apm

        addLine' :: AddProvMod -> GenericStatement -> AddProvMod
        addLine' apm [pdx| all_provinces = %rhs |]
            | GenericRhs "yes" [] <- rhs = apm { apm_province_all = True }
            | otherwise = apm
        addLine' apm [pdx| limit_to_coastal = %rhs |]
            | GenericRhs "yes" [] <- rhs = apm { apm_province_coastal = True }
            | otherwise = apm
        addLine' apm [pdx| limit_to_naval_base = %rhs |]
            | GenericRhs "yes" [] <- rhs = apm { apm_province_naval = True }
            | otherwise = apm
        addLine' apm [pdx| limit_to_border = %rhs |]
            | GenericRhs "yes" [] <- rhs = apm { apm_province_border = True }
            | otherwise = apm
        addLine' apm [pdx| id = !num |] =
            let oldprov = fromMaybe [] (apm_province apm) in
            apm { apm_province = Just (oldprov ++ [num :: Double]) }
        addLine' apm [pdx| limit_to_victory_point > !num |] =
            apm { apm_limit_to_victory_point_comp = "higher than", apm_limit_to_victory_point_num = Just num }
        addLine' apm [pdx| limit_to_victory_point < !num |] =
            apm {apm_limit_to_victory_point_comp = "lower than", apm_limit_to_victory_point_num = Just num }
        addLine' apm [pdx| limit_to_victory_point = %rhs |]
            | GenericRhs "yes" [] <- rhs = apm { apm_limit_to_victory_point = True }
            | otherwise = apm
        addLine' apm [pdx| $other = %_ |] = trace ("unknown section in add_province_modifier@province: " ++ show other) apm
        addLine' apm stmt = trace ("Unknown form in add_province_modifier@province: " ++ show stmt) apm

        getbaremods (StatementBare (GenericLhs e [])) = Just e
        getbaremods stmt = trace ("Unknown in static_modifier array statement: " ++ show stmt) Nothing

        pp_apm :: AddProvMod -> PPT g m ScriptMessage
        pp_apm apm = do
            modlocs <- mapM (\m -> do
                loc <- getGameL10n m
                return $ "<!--" <> m <> "-->" <> Doc.doc2text (iquotes loc))
                (apm_modifier apm)
            let modloc
                    | length modlocs > 1 = "modifiers " <> T.intercalate ", " modlocs
                    | length modlocs == 1 = "modifier " <> T.concat modlocs
                    | otherwise = "<!--CHECK SCRIPT-->"
            prov <- do
                allmsg <- if apm_province_all apm then messageText MsgAllProvinces else return ""
                bordmsg <- if apm_province_border apm then messageText MsgLimitToBorder else return ""
                coastmsg <- if apm_province_coastal apm then messageText MsgLimitToCoastal else return ""
                navmsg <- if apm_province_naval apm then messageText MsgLimitToNavalBase else return ""
                let provmsg = case apm_province apm of
                        Just id -> if length id > 1
                            then T.pack $ concat [", on the provinces (" , intercalate "), (" (map (show . round) id),")"]
                            else T.pack $ concat [", on the province (" , concatMap (show . round) id,")"]
                        _-> ""
                victmsg <- case ( apm_limit_to_victory_point apm
                                , apm_limit_to_victory_point_num apm) of
                    (False, Just num) -> messageText $ MsgLimitToVictoryPoint False (apm_limit_to_victory_point_comp apm) num
                    (True, Nothing) -> messageText $ MsgLimitToVictoryPoint True "" 0
                    _ -> return ""
                return $ allmsg <> bordmsg <> coastmsg <> navmsg <> victmsg <> provmsg
            return $ MsgAddProvinceModifier addrem modloc prov
addProvinceModifier _ stmt = trace ("Not handled in addProvinceModifier: " ++ show stmt) $ preStatement stmt

-------------------------------------------
-- handler for is_power_balance_in_range --
-------------------------------------------

data PowerBalanceRange = PowerBalanceRange
        {   pbr_id :: Text
        ,   pbr_range :: Text
        ,   pbr_comp :: Double
        }

newPBR :: PowerBalanceRange
newPBR = PowerBalanceRange "<!--Check Script-->" "<!--Check Script-->" 0

powerBalanceRange :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
powerBalanceRange stmt@[pdx| %_ = @scr |]
    = msgToPP =<< ppPBR =<< foldM addLine newPBR scr
    where
        addLine :: PowerBalanceRange -> GenericStatement -> PPT g m PowerBalanceRange
        addLine pbr [pdx| id = ?txt |] = return pbr { pbr_id = txt }
        addLine pbr [pdx| range = ?txt |] = return pbr { pbr_range = txt }
        addLine pbr [pdx| range > ?txt |] = return pbr { pbr_range = txt, pbr_comp = 1 }--right
        addLine pbr [pdx| range < ?txt |] = return pbr { pbr_range = txt, pbr_comp = -1 }--left
        addLine pbr [pdx| $other = %_ |] = trace ("unknown section in powerBalanceRange: " ++ show other) $ return pbr
        addLine pbr stmt = trace ("unknown form in powerBalanceRange: " ++ show stmt) $ return pbr
        ppPBR :: PowerBalanceRange -> PPT g m ScriptMessage
        ppPBR pbr = do
            idloc <- getGameL10n (pbr_id pbr)
            rangeloc <- getGameL10n (pbr_range pbr)
            return $ MsgIsPowerBalanceInRange idloc rangeloc (pbr_id pbr) (pbr_range pbr) (pbr_comp pbr)
powerBalanceRange stmt = preStatement stmt

-------------------------------------------
-- handler for is_power_balance_in_range --
-------------------------------------------

data NavalStrengthComparison = NavalStrengthComparison
        {   nsc_other :: Text
        ,   nsc_ratio :: Double
        ,   nsc_comp :: Text
        ,   nsc_sub_unit_def_weights :: [(Text,Double)]
        }

newNSC :: NavalStrengthComparison
newNSC = NavalStrengthComparison "<!--Check Script-->" 0 "<!--Check Script-->" []

navalStrengthComparison :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
navalStrengthComparison stmt@[pdx| %_ = @scr |]
    = msgToPP =<< ppNSC =<< foldM addLine newNSC scr
    where
        addLine :: NavalStrengthComparison -> GenericStatement -> PPT g m NavalStrengthComparison
        addLine nsc [pdx| other = ?txt |] = return nsc { nsc_other = txt }
        addLine nsc [pdx| ratio > !amt |] = return nsc { nsc_ratio = amt, nsc_comp = "more" }--right
        addLine nsc [pdx| ratio < !amt |] = return nsc { nsc_ratio = amt, nsc_comp = "less" }--left
        addLine nsc [pdx| sub_unit_def_weights = @scr |] = return $ foldl' addLine' nsc scr
        addLine nsc [pdx| $other = %_ |] = trace ("unknown section in navalStrengthComparison: " ++ show other) $ return nsc
        addLine nsc stmt = trace ("unknown form in navalStrengthComparison: " ++ show stmt) $ return nsc
        addLine' :: NavalStrengthComparison -> GenericStatement -> NavalStrengthComparison
        addLine' nsc [pdx| $shiptype = !weight |] = do
            let oldweight = nsc_sub_unit_def_weights nsc
            nsc { nsc_sub_unit_def_weights = oldweight ++ [(shiptype, weight)]}
        addLine' nsc [pdx| $other = %_ |] = trace ("unknown section in navalStrengthComparison weights: " ++ show other) nsc
        addLine' nsc stmt = trace ("unknown form in navalStrengthComparison weights: " ++ show stmt) nsc

        ppNSC :: NavalStrengthComparison -> PPT g m ScriptMessage
        ppNSC nsc = do
            otherflag <- flagText (Just HOI4Country) (nsc_other nsc)
            weighttext <- case nsc_sub_unit_def_weights nsc of
                [] -> return ""
                weights -> do
                    weightype <- mapM (\wt -> do
                        let (shiptype, weight) = wt
                        shiploc <- getGameL10n shiptype
                        let weighttxt = Doc.doc2text (plainNum weight)
                        return $ weighttxt <> " for " <> shiploc)
                        weights
                    return $ " with weight " <> T.intercalate ", " weightype
            return $ MsgavalStrengthComparison (nsc_ratio nsc) (nsc_comp nsc) otherflag weighttext
navalStrengthComparison stmt = preStatement stmt

-- unlock decision tooltip

unlockDecisionTooltip :: forall g m. (HOI4Info g, Monad m) => StatementHandler g m
unlockDecisionTooltip stmt@[pdx| %_ = $_ |] = locandid MsgUnlockDecisionTooltip stmt
unlockDecisionTooltip stmt@[pdx| %_ = @scr |] = do
    let (mname, _) = extractStmt (matchLhsText "decision") scr
    case mname of
        Just stmt@[pdx| %_ = ?txt |] -> locandid MsgUnlockDecisionTooltip stmt
        _ -> preStatement stmt
unlockDecisionTooltip stmt = preStatement stmt