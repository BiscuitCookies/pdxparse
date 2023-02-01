{-|
Module      : Doc
Description : Front end to Wadler/Leijen pretty printer
-}
module Doc
    ( strictText
    , ppString
    , doc2text
    , ppSigned, ppNosigned
    , ppFloat
    , ppFloatT
    , nl2br
    , Doc
    , (PP.<++>)
    ) where

import Data.List (unfoldr)

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL

import Text.PrettyPrint.Leijen.Text (Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP

import Numeric (showFFloat)

-- | Embed a strict Text value into a Doc.
strictText :: Text -> Doc
strictText = PP.text . TL.fromStrict

-- | Embed a String value into a Doc.
ppString :: String -> Doc
ppString = PP.text . TL.pack

-- | Convert a Doc to Text by compactly displaying it. Since this defeats the
-- point of using the pretty-printer, it should be used sparingly and only when
-- necessary.
doc2text :: Doc -> Text
doc2text = TL.toStrict . PP.displayT . PP.renderCompact

-- | Pretty-print a number, putting a + sign in front if it's positive.
-- Assumes the passed-in formatting function does add a minus sign.
ppSigned :: (Ord n, Num n) => (n -> Doc) -> n -> Doc
ppSigned pp_num n = (if signum n > 0 then "+" else mempty) <> pp_num n

-- | Pretty-print a number, removing the - sign in front if it's negative.
-- Assumes the passed-in formatting function does add a minus sign.
ppNosigned :: (Ord n, Num n) => (n -> Doc) -> n -> Doc
ppNosigned pp_num n =
    (if signum n < 0
        then strictText . T.drop 1 . doc2text
        else id) $ pp_num n

-- | Pretty-print a Double. If it's a whole number, display it without a
-- decimal.
ppFloat :: Double -> Doc
ppFloat n
    | fromIntegral trunc == n =
        PP.int (fromIntegral trunc)
    | otherwise =
        PP.text . TL.pack $ showFFloat Nothing n ""
    where
    trunc :: Int
    trunc = floor n

-- | Pretty-print a Double, as Text.
ppFloatT :: Double -> Text
ppFloatT = TL.toStrict . PP.displayT . PP.renderCompact . ppFloat

-- | Convert newlines to <br/> tags.
nl2br :: Text -> Text
nl2br = mconcat . unfoldr replaceNextBreak . Just where
    replaceNextBreak :: Maybe Text -> Maybe (Text, Maybe Text)
    replaceNextBreak Nothing = Nothing
    replaceNextBreak (Just t)
        = let (left, right) = T.breakOn "\n" t
              right' = T.drop 1 right
          in if T.null right -- no newlines found
                then Just (left, Nothing)
                else Just (left <> "<br/>", Just right')
