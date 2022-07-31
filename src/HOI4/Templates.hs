module HOI4.Templates (
        Param (..)
    ,   CompField (..)
    ,   foldCompound
    ) where

import Language.Haskell.TH -- everything

import HOI4.Types (HOI4Info) -- HACK :/

import Data.Text (Text)

import Data.List (unzip5)
import Data.Maybe (isJust, fromMaybe)

import Abstract
import HOI4.Messages
import QQ
import SettingsTypes

import Debug.Trace

data CompField = CompField {
        fieldName :: String
    ,   fieldType :: Q Type
    ,   fieldDefault :: Maybe (Q Exp)
    ,   fieldCompulsory :: Bool
    }


class Param t where
    toParam :: GenericRhs -> Maybe t
instance Param Double where
    toParam = floatRhs
instance Param Text where
    toParam = textRhs

{- | Pattern for accumulating fields from a compound statement then analyzing them.
 -
 - Usage:
 - @
 -  foldCompound [function name] [data type name] [field prefix] [additional arguments] [field specs] [processing expression]
 - @
 -
 - where
 -
 - [@[function name]@] Name of the function to be generated.
 -
 - [@[data type name]@] Name of the intermediate data type and its constructor.
 -
 - [@[field prefix]@] Prefix for the intermediate data type's field labels (an
 -      additional underscore is added). This is purely to avoid name clashes.
 -
 - [@[additional arguments]@] List of pairs @([variable name], [type])@. The
 -      function is given a number of additional arguments of these names and
 -      types.
 -
 - [@field specs@] is a list of 'CompField' values:
 -
 -      @
 -          CompField [field name] [field type] [default value] [required?]
 -      @
 -
 -      where
 -
 -      [@[field name]@] Name of the field.
 -      [@[type]@] Type of the field.
 -      [@[default value]@] Default value for the field if not present (type
 -          @Q Exp@). This expression is closed (has no free variables).
 -      [@[required?]@] Boolean value indicating whether the field is required.
 -
 -  [@[processing expression]@] The expression used to bring the value
 -      together. This should have type PPT g m @ScriptMessage@, and has a
 -      number of free variables: one for each additional argument, and one
 -      bound to each field's value, prefixed with an underscore. The field
 -      variables have their declared types if mandatory, and @Maybe@ those
 -      types otherwise.
 -
 - The resulting function has only the given additional arguments, and has
 - return type @(IsGameState (GameState g), Monad m) => StatementHandler g m@.
 -
-}
foldCompound :: String -> String -> String -> [(String, Q Type)] -> [CompField] -> Q Exp -> Q [Dec]
foldCompound funname s_tyname prefix extraArgs fieldspecs eval = do
    let -- Missing TH library function
        funT :: TypeQ -> TypeQ -> TypeQ
        funT t1 t2 = [t| $t1 -> $t2 |]
        -- Variable names
        name_acc = mkName "acc"
        name_addLine = mkName "addLine"
        name_fun = mkName funname
        name_pp = mkName "pp"
        name_scr = mkName "scr"
        name_stmt = mkName "stmt"
        name_x = mkName "x"
        tyname = mkName s_tyname
        defaultsName = mkName ("new" ++ s_tyname)
    -- Variables. These are evaluated and immediately put back in Q to make
    -- sure every instance is the same.
    [tvar_g, tvar_m] <- mapM (fmap varT . newName) ["g","m"]
    [var_acc, var_addLine, var_defaults, var_pp, var_scr, var_stmt, var_x]
        <- mapM (return . varE) [name_acc, name_addLine, defaultsName
                                ,name_pp, name_scr, name_stmt, name_x]

    -- Iterate through fields generating relevant code for each
    let (recFields, defs, lineclauses, caseheads, casebodies) =
            unzip5 . flip map fieldspecs $ \fieldspec ->
                let ftype = fieldType fieldspec
                    fname = fieldName fieldspec
                    varname = '_' : fieldName fieldspec
                    rfname = mkName (prefix ++ varname)
                    def = fieldDefault fieldspec
                    hasDefault = isJust def
                    patvar = varP (mkName varname)
                in ( -- Record field declaration
                    do  thetype <- ftype
                        thedefault <- case fieldDefault fieldspec of
                            Nothing -> return Nothing
                            Just def -> Just <$> def
                        varBangType rfname
                            (bangType (bang noSourceUnpackedness noSourceStrictness)
                                (if hasDefault
                                    then ftype -- guaranteed to exist
                                    else appT (conT ''Maybe) ftype
                                )
                            )
                    -- Initial value for accumulator
                    ,fromMaybe [| Nothing |] def
                    -- Clause for addLine
                    ,clause [varP name_acc
                            ,[p| Statement (GenericLhs $(litP (stringL (fieldName fieldspec))) [])
                                          OpEq
                                          $(viewP (varE 'toParam) (conP 'Just [varP name_x])) |]]
                            (normalB $ recUpdE (varE name_acc) [fieldExp rfname
                                (if hasDefault
                                    then varE name_x
                                    else appE (conE 'Just) (varE name_x))])
                            []
                    -- Case head for this field
                    ,appE (varE rfname) var_acc
                    -- Case body, exposing a variable for this field
                    ,if fieldCompulsory fieldspec
                        then [p| Just $patvar |] -- :: <fieldtype>
                        else [p| $patvar |]) -- :: Maybe <fieldtype>
    sequence $ [
        -- Accumulator type
        -- data <AccType> = AccType
        --  { <prefix>_<field1Name> :: {Maybe} <field1Type>
        --  , ...
        --  }
            dataD (cxt []) tyname [] Nothing
                  [recC tyname recFields
                  ]
                  [DerivClause Nothing <$> cxt []]
        -- Initial accumulator
        -- new<AccType> :: <AccType>
        -- new<AccType> = AccType <default1> <default2> ...
        ,   sigD defaultsName (conT tyname)
        ,   flip (valD (varP defaultsName)) [] . normalB $
                appsE (conE tyname : defs)
        -- Unpacking code
        -- HACK: Templates used to be generic, but I'm lazy :(
        -- <funName> :: (HOI4Info g, Monad m) => <ExtraArg1Type> -> ... -> StatementHandler g m
        -- <funName> <extraArg1> ... stmt@[pdx| %_ = @scr |]
        --      = msgToPP . pp $ foldl' addLine new<AccType> scr where
        --          addLine :: <AccType> -> GenericStatement -> <AccType>
        --          addLine [pdx| <tag1> = $(toParam -> Just _<paramName> |] = acc { prefix_<paramName> = {Just} _<paramName> }
        --          ...
        --          pp :: <AccType> -> PPT g m ScriptMessage
        --          pp acc = case (requiredPat1, ..., optionalPat1, ...) of
        --              (Just _<requiredParamName1>, ..., _<optionalParamName1>, ...) -> <eval>
        --              _ -> preStatement stmt
        -- <funName> _1 ... stmt = preStatement stmt
        ,   sigD name_fun
                (forallT [] (sequence [[t|HOI4Info $tvar_g |], [t|Monad $tvar_m |]]) $
                    foldr (funT . snd) [t| StatementHandler $tvar_g $tvar_m |] extraArgs)
        ,   funD name_fun [
                    clause (map (varP . mkName . fst) extraArgs
                                ++ [asP name_stmt [p| [pdx| %_ = @scr |] |]])
                           (normalB [| msgToPP =<< ($var_pp $ foldl' $var_addLine $var_defaults $var_scr) |])
                           -- where
                           [sigD name_addLine [t| $(conT tyname) -> GenericStatement -> $(conT tyname) |]
                           ,funD name_addLine (lineclauses ++
                                [clause [varP name_acc, wildP]
                                        -- TODO: Print actual line that doesn't match
                                        (normalB [| trace (funname ++ ": Unhandled line found in " ++ show stmt) $ $var_acc |])
                                        []
                                ])
                           ,funD name_pp
                                [flip (clause [varP name_acc]) [] . normalB $
                                    caseE (tupE caseheads)
                                        [match (tupP casebodies) (normalB eval) []
                                        ,match wildP (normalB
                                            [| return $ trace (funname ++ ": one or more required fields not present") $
                                                preMessage stmt |]) []
                                        ]
                                ]
                           ]
                ,   clause (map (const wildP) extraArgs ++ [varP name_stmt])
                           (normalB [| preStatement stmt |])
                           []
            ]
        ]
