-- Copyright 2020-2021 Google LLC
-- Copyright 2022 Andrew Pritchard
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--      http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

-- | Provides a compatibility layer of Haskell-like terms for pretty-printers.

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Portray
         ( -- * Syntax Tree
           Portrayal
             ( Name
             , LitInt, LitIntBase
             , LitRat, LitFloat, SpecialFloat
             , LitStr, LitChar, Opaque
             , Apply, Binop, Tuple, List
             , LambdaCase, Record, TyApp, TySig
             , Quot, Unlines, Nest
             , ..
             )
         , FactorPortrayal(..)
         , IdentKind(..), Ident(..)
           -- ** Numeric Literals
           -- *** Integral Literals
         , Base(..), baseToInt, basePrefix, formatIntLit
           -- *** Floating-Point Literals
         , FloatLiteral(..), floatToLiteral, fixedToLiteral
         , floatLiteralToRational, shouldUseScientific
         , normalizeFloatLit, trimFloatLit, formatFloatLit
         , SpecialFloatVal(..), formatSpecialFloat
           -- ** Operator Fixity
         , Assoc(..), Infixity(..), infix_, infixl_, infixr_
           -- ** Base Functor
         , PortrayalF(.., LitIntF, LitRatF)
           -- * Class
         , Portray(..)
           -- ** Via Generic
         , GPortray(..), GPortrayProduct(..)
           -- ** Via Show, Integral, Real, and RealFrac
         , PortrayIntLit(..), PortrayRatLit(..), PortrayFloatLit(..)
         , ShowAtom(..)
           -- * Convenience
         , showAtom, strAtom, strQuot, strBinop
           -- * Miscellaneous
         , Fix(..), cata, portrayCallStack, portrayType
         , showIntInBase
         ) where

import Data.Bifunctor (second)
import Data.Char (digitToInt, intToDigit, isAlpha, isDigit, isUpper)
import Data.Coerce (Coercible, coerce)
import Data.Fixed (Fixed(..), HasResolution(..))
import Data.Functor.Identity (Identity(..))
import Data.Functor.Const (Const(..))
import Data.Int (Int8, Int16, Int32, Int64)
import Data.IntMap (IntMap)
import Data.Kind (Type)
import Data.List (foldl')
import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import Data.Proxy (Proxy(..))
import Data.Ratio (Ratio, (%), numerator, denominator)
import Data.Semigroup (Sum(..), Product(..))
import Data.Sequence (Seq)
import Data.Set (Set)
import Data.String (IsString)
import Data.Text (Text)
import Data.Type.Coercion (Coercion(..))
import Data.Type.Equality ((:~:)(..))
import Data.Void (Void)
import Data.Word (Word8, Word16, Word32, Word64)
import qualified Data.Text as T
import GHC.Exts (IsList, proxy#)
import qualified GHC.Exts as Exts
import GHC.Float (floatToDigits)
import GHC.Generics
         ( (:*:)(..), (:+:)(..)
         , Generic(..), Rep
         , U1(..), K1(..), M1(..), V1
         , Meta(..), D1, C1, S1
         , Constructor, conName, conFixity
         , Selector, selName
         , Fixity(..), Associativity(..)
         )
import GHC.Real (infinity, notANumber)
import GHC.Stack (CallStack, SrcLoc, getCallStack, prettySrcLoc)
import GHC.TypeLits (KnownSymbol, symbolVal')
import Numeric
         ( showOct, showInt, showHex
#if MIN_VERSION_base(4, 16, 0)
         , showBin
#else
         , showIntAtBase
#endif
         )
import Numeric.Natural (Natural)
import Type.Reflection
         ( TyCon, TypeRep, SomeTypeRep(..)
         , pattern App, pattern Con', pattern Fun
         , tyConName, typeRep
         )

import Data.Wrapped (Wrapped(..))

-- | Associativity of an infix operator.
data Assoc = AssocL | AssocR | AssocNope
  deriving (Read, Show, Eq, Ord, Generic)
  deriving Portray via Wrapped Generic Assoc

-- | Associativity and binding precedence of an infix operator.
data Infixity = Infixity !Assoc !Rational
  deriving (Read, Show, Eq, Ord, Generic)
  deriving Portray via Wrapped Generic Infixity

-- | Construct the 'Infixity' corresponding to e.g. @infix 6 +&&+*@
infix_ :: Rational -> Infixity
infix_ = Infixity AssocNope

-- | Construct the 'Infixity' corresponding to e.g. @infixl 6 +&&+*@
infixl_ :: Rational -> Infixity
infixl_ = Infixity AssocL

-- | Construct the 'Infixity' corresponding to e.g. @infixr 6 +&&+*@
infixr_ :: Rational -> Infixity
infixr_ = Infixity AssocR

-- | The kind of identifier a particular 'Ident' represents.
data IdentKind = VarIdent | ConIdent | OpIdent | OpConIdent
  deriving (Eq, Ord, Read, Show, Generic)
  deriving Portray via Wrapped Generic IdentKind

-- | An identifier or operator name.
data Ident = Ident !IdentKind !Text
  deriving (Eq, Ord, Read, Show, Generic)
  deriving Portray via Wrapped Generic Ident

instance IsString Ident where
  fromString nm = Ident k (T.pack nm)
   where
    k = case nm of
      (':':_) -> OpConIdent
      ('_':_) -> VarIdent
      (c:_)
        | isUpper c -> ConIdent
        | isAlpha c -> VarIdent
        | otherwise -> OpIdent
      "" -> VarIdent -- /shrug/

-- The (supported) base used for an integral literal.
--
-- @since 0.3.0
data Base = Binary | Octal | Decimal | Hex
  deriving (Eq, Ord, Read, Show, Generic)
  deriving Portray via Wrapped Generic Base

-- | Convert the given base to its numerical value.
--
-- @since 0.3.0
baseToInt :: Base -> Int
baseToInt = \case { Binary -> 2; Octal -> 8; Decimal -> 10; Hex -> 16 }

#if !MIN_VERSION_base(4, 16, 0)
showBin :: (Show a, Integral a) => a -> ShowS
showBin = showIntAtBase 2 (\case 0 -> '0'; _ -> '1')
#endif

-- | Show /non-negative/ 'Integral' numbers in the given conventional base.
--
-- @since 0.3.0
showIntInBase :: (Show a, Integral a) => Base -> a -> ShowS
showIntInBase =
  \case
    Binary -> showBin
    Octal -> showOct
    Decimal -> showInt
    Hex -> showHex

chunksR :: [Int] -> Text -> [Text]
chunksR ns0 x0 = go ns0 x0 []
 where
  go _ "" tl = tl
  go [] x tl = x:tl
  go (n:ns) x tl =
    let (rest, chunk) = T.splitAt (T.length x - n) x
    in  go ns rest (chunk : tl)

insertSeparators :: [Int] -> Text -> Text
insertSeparators seps = T.intercalate "_" . chunksR seps

-- | Format an integral literal in the given base.
--
-- @since 0.3.0
formatIntLit :: (Show a, Integral a) => Base -> [Int] -> a -> Text
formatIntLit b seps x =
  sign <> basePrefix b <>
  insertSeparators seps (T.pack (showIntInBase b (abs x) ""))
 where
  sign
   | x < 0 = "-"
   | otherwise = ""

-- | The syntactic marker prefix for the given base, e.g. "0x" for hex.
--
-- @since 0.3.0
basePrefix :: Base -> Text
basePrefix =
  \case { Binary -> "0b"; Octal -> "0o"; Decimal -> ""; Hex -> "0x" }

-- [Note: Rational literals]
--
-- Rational literals are a bit of an interesting case.  It might appear to be
-- simple: just represent them as a 'Rational' like the AST does, and format
-- them as needed.  Unfortunately, that doesn't behave well: different
-- 'Fractional' types have differing amounts of precision and different ways of
-- placing that precision w.r.t. the radix point; so the number of digits that
-- should be shown for a given exact 'Rational' can vary between types.  That
-- functionality in "base" is behind an API that gets info about the type's
-- precision via a typeclass, so type-erasing it for the AST and continuing to
-- use that API in the backends isn't particularly feasible.  Additionally,
-- conversion to 'Rational' erases the distinction between signed zeros.
--
-- To get around these issues, we have 'Portray' instances do the conversion to
-- digits themselves, so each instance can call the appropriate instance of
-- 'floatToDigits', and then let the backends decide what to do with those
-- digits.  In addition to the raw digits themselves, we need the sign and
-- exponent.  It's left up to the backends to decide whether to use scientific
-- notation, include a trailing decimal point, numeric underscores, etc.
--
-- On top of this, many floating-point types include infinite and non-numeric
-- values.  Although Haskell syntax does not include these, the values do
-- exist, and we need some way to represent them.  As a compromise to
-- pragmatism and aesthetics, we'll augment the Haskell syntax with native
-- syntax for positive and negative infinities and a NaN constant, to give
-- backends the opportunity to decide what to do with these exotic values,
-- rather than expecting instances to produce something unwieldy like
-- @fromRational (negate infinity)@.

-- | A representation of a float literal as its digits, sign, and exponent.
--
-- The choice of whether to represent a literal with leading zeros or a smaller
-- exponent is assumed not to be meaningful.  Trailing zeros may be included to
-- imply that the value is given with additional precision beyond the last
-- nonzero digit; backends may choose to include these or trim them.
--
-- The value represented by @FloatLiteral sign digits e@ is
-- @sign * 0.<digits> * 10^e@, which is to say the radix point falls before
-- index @e@ of @digits@.
--
-- @since 0.3.0
data FloatLiteral = FloatLiteral
  { flNegate :: !Bool
  , flDigits :: !Text -- ^ Expected to be ASCII digits.
  , flExponent :: !Int
  }
  deriving (Eq, Ord, Read, Show, Generic)
  deriving Portray via Wrapped Generic FloatLiteral

-- | Extract a 'Rational' value representation of the 'FloatLiteral'.
--
-- @since 0.3.0
floatLiteralToRational :: FloatLiteral -> Rational
floatLiteralToRational x = num % denom
 where
  applySign
    | flNegate x = negate
    | otherwise = id

  mantissa =
    foldl'
      (\d acc -> 10*acc + d)
      0
      (map (toInteger . digitToInt) $ T.unpack $ flDigits x)
  e = toInteger $ flExponent x
  num = applySign mantissa * 10 ^ max 0 e
  denom = 10 ^ max 0 (negate e)

negativeZero :: FloatLiteral
negativeZero = FloatLiteral True "0" 0

-- | Convert a finite 'RealFloat' value to a 'FloatLiteral'.
--
-- @since 0.3.0
floatToLiteral :: RealFloat a => a -> FloatLiteral
floatToLiteral x
  | isNegativeZero x = negativeZero
  | otherwise =
      let (digits, e) = floatToDigits 10 x
      in  FloatLiteral (x < 0) (T.pack (map intToDigit digits)) e

-- | Normalize a float literal to have no leading zero digits, if nonzero.
--
-- @since 0.3.0
normalizeFloatLit :: FloatLiteral -> FloatLiteral
normalizeFloatLit (FloatLiteral n d e)
  -- Leave all-zero digit strings alone: we can't identify any of the zeros as
  -- meaningless "leading" zeros vs. precision-implying "trailing" zeros.
  | T.null rest = FloatLiteral n d e
  | otherwise = FloatLiteral n rest (e - T.length zeros)
 where
  (zeros, rest) = T.span (=='0') d

-- This isn't in "text" for some reason.
spanEnd :: (Char -> Bool) -> Text -> (Text, Text)
#if MIN_VERSION_text(2, 0, 1)
spanEnd f = runIdentity . T.spanEndM (Identity . f)
#else
spanEnd f x =
  let (r, l) = T.span f (T.reverse x)
  in  (T.reverse l, T.reverse r)
#endif

-- | Trim trailing zeros of a float literal.
--
-- These trailing zeros are presumed to mean that the value is given to a
-- particular level of precision, so trimming them before output means the
-- output no longer includes this implied precision information.
--
-- @since 0.3.0
trimFloatLit :: FloatLiteral -> FloatLiteral
trimFloatLit (FloatLiteral n d e)
  | T.null rest = FloatLiteral n "0" 1  -- "0.", not ".0"
  | otherwise = FloatLiteral n rest e
 where
  (rest, _) = spanEnd (=='0') d

-- | A default heuristic for whether a literal should use scientific notation.
--
-- This returns 'True' when using scientific notation would let us avoid
-- padding the digits with more than one extra zero.
--
-- @since 0.3.0
shouldUseScientific :: FloatLiteral -> Bool
shouldUseScientific (FloatLiteral _ d e) = e < -1 || e > T.length d + 1

-- | Format a 'FloatLiteral' to 'Text' in the conventional way.
--
-- @since 0.3.0
formatFloatLit :: Bool -> [Int] -> FloatLiteral -> Text
formatFloatLit scientific seps (FloatLiteral neg digits e) =
  sign <> insertSeparators seps whole <> frac <> ex
 where
  sign = if neg then "-" else ""

  radixPoint
    | scientific = 1
    | otherwise = e

  n = T.length digits
  (whole, frac)
    | radixPoint <= 0 = ("0", "." <> T.replicate (-radixPoint) "0" <> digits)
    | radixPoint >= n = (digits <> T.replicate (radixPoint - n) "0", "")
    | otherwise = second ("." <>) $ T.splitAt radixPoint digits

  ex
    | scientific = "e" <> T.pack (show (e - 1))
    | otherwise = ""


-- | Special floating-point values including NaNs and infinities.
--
-- @since 0.3.0
data SpecialFloatVal = NaN | Infinity { infNegate :: Bool }
  deriving (Eq, Ord, Read, Show, Generic)
  deriving Portray via Wrapped Generic SpecialFloatVal

-- | Format a 'SpecialFloatVal' to 'Text' in the conventional way.
--
-- @since 0.3.0
formatSpecialFloat :: SpecialFloatVal -> Text
formatSpecialFloat = \case
  NaN -> "NaN"
  Infinity neg -> (if neg then "-" else "") <> "Infinity"

-- | A single level of pseudo-Haskell expression; used to define 'Portrayal'.
data PortrayalF a
  = NameF {-# UNPACK #-} !Ident
    -- ^ An identifier, including variable, constructor and operator names.
  | LitIntBaseF !Base !Integer
    -- ^ An integral literal with a particular base.  e.g. @42@, @0o777@
    --
    -- For example, a POSIX file mode type might wish to be printed as
    -- specifically octal integral literals.
    --
    -- @since 0.3.0
  | LitFloatF {-# UNPACK #-} !FloatLiteral
    -- ^ A rational / floating-point literal.  e.g. @42.002@
    --
    -- @since 0.3.0
  | SpecialFloatF !SpecialFloatVal
    -- ^ A "special" floating-point value.  e.g. @NaN@ or @-Infinity@
    --
    -- @since 0.3.0
  | LitStrF !Text
    -- ^ A string literal, stored without escaping or quotes.  e.g. @"hi"@
  | LitCharF !Char
    -- ^ A character literal.  e.g. @\'a\'@
  | OpaqueF !Text
    -- ^ A chunk of opaque text.  e.g. @abc"]def@
  | ApplyF !a [a]
    -- ^ A function application to several arguments.
  | BinopF !Ident !Infixity !a !a
    -- ^ A binary infix operator application to two arguments.
  | TupleF [a]
    -- ^ A tuple of sub-values.
  | ListF [a]
    -- ^ A list of sub-values.
  | LambdaCaseF [(a, a)]
    -- ^ A lambda-case expression.
  | RecordF !a [FactorPortrayal a]
    -- ^ A record construction/update syntax.
  | TyAppF !a !a
    -- ^ A TypeApplication.
  | TySigF !a !a
    -- ^ A term with explicit type signature.
  | QuotF !Text !a
    -- ^ A quasiquoter term with the given name.
  | UnlinesF [a]
    -- ^ A collection of vertically-aligned lines
  | NestF !Int !a
    -- ^ A subdocument indented by the given number of columns.
  deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable, Generic)
  deriving Portray via Wrapped Generic (PortrayalF a)

-- | Backwards compat: 'LitIntBaseF' without the base.
--
-- When matching, this ignores the base; when constructing, it chooses decimal.
pattern LitIntF :: Integer -> PortrayalF a
pattern LitIntF x <- LitIntBaseF _ x
 where LitIntF x = LitIntBaseF Decimal x

matchLitRat :: PortrayalF a -> Maybe Rational
matchLitRat (LitFloatF x) = Just (floatLiteralToRational x)
matchLitRat (SpecialFloatF x) = Just $ case x of
  NaN -> notANumber
  Infinity neg -> (if neg then negate else id) infinity
matchLitRat _ = Nothing

buildLitRat :: Rational -> PortrayalF a
buildLitRat x
  | x == infinity = SpecialFloatF (Infinity False)
  | x == -infinity = SpecialFloatF (Infinity True)
  | x == notANumber = SpecialFloatF NaN
  | otherwise = LitFloatF $ floatToLiteral (fromRational x :: Double)

-- | Backwards compat: rational values including NaNs and infinities.
--
-- When matching, this ignores the format; when constructing, it chooses
-- according to the same criteria as 'showGFloat'.
pattern LitRatF :: Rational -> PortrayalF a
pattern LitRatF x <- (matchLitRat -> Just x)
 where LitRatF x = buildLitRat x

-- Backwards compat: matching on all the constructor names of PortrayalF in
-- 0.2.0 is still complete.
--
-- For whatever reason, this pragma doesn't seem to be honored downstream in at
-- least some cases, but we may as well have it.
{-# COMPLETE
      NameF, LitIntF, LitRatF, LitStrF, LitCharF,
      OpaqueF, ApplyF, BinopF, TupleF, ListF,
      LambdaCaseF, RecordF, TyAppF, TySigF, QuotF,
      UnlinesF, NestF
  #-}

-- | A 'Portrayal' along with a field name; one piece of a record literal.
data FactorPortrayal a = FactorPortrayal
  { _fpFieldName :: !Ident
  , _fpPortrayal :: !a
  }
  deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable, Generic)
  deriving Portray via Wrapped Generic (FactorPortrayal a)


-- | Fixed-point of a functor.
--
-- There are many packages that provide equivalent things, but we need almost
-- nothing but the type itself, so we may as well just define one locally.
newtype Fix f = Fix (f (Fix f))
  deriving Generic

deriving newtype
  instance (forall a. Portray a => Portray (f a)) => Portray (Fix f)

deriving stock
  instance (forall a. Read a => Read (f a)) => Read (Fix f)

deriving stock
  instance (forall a. Show a => Show (f a)) => Show (Fix f)

deriving stock
  instance (forall a. Eq a => Eq (f a)) => Eq (Fix f)

-- | The portrayal of a Haskell runtime value as a pseudo-Haskell syntax tree.
--
-- This can be rendered to various pretty-printing libraries' document types
-- relatively easily; as such, it provides a /lingua franca/ for integrating
-- with pretty-printers, without incurring heavyweight dependencies.
newtype Portrayal = Portrayal { unPortrayal :: Fix PortrayalF }
  deriving stock (Eq, Generic)
  deriving newtype (Portray, Show, Read)

-- Matching the full set of 0.2.0 patterns still covers all cases.
{-# COMPLETE
      Name, LitInt, LitRat, LitStr, LitChar, Opaque, Apply, Binop, Tuple,
      List, LambdaCase, Record, TyApp, TySig, Quot, Unlines, Nest
  #-}

-- Or, match all of the up-to-date constructors.  I'll not go out of the way to
-- permit mixing new and old by making combinatorially many COMPLETE pragmas.
{-# COMPLETE
      Name, LitIntBase, LitFloat, SpecialFloat, LitStr, LitChar,
      Opaque, Apply, Binop, Tuple, List,
      LambdaCase, Record, TyApp, TySig, Quot, Unlines, Nest
  #-}

-- An explicitly-bidirectional pattern synonym that makes it possible to write
-- simply-bidirectional pattern synonyms involving coercions.
--
-- N.B.: lol, I did not expect this to work.
pattern Coerced :: Coercible a b => a -> b
pattern Coerced x <- (coerce -> x)
 where
  Coerced x = coerce x

-- A collection of pattern synonyms to hide the fact that we're using Fix
-- internally.

-- | An identifier, including variable, constructor, and operator names.
--
-- The 'IdentKind' distinguishes constructors, operators, etc. to enable
-- backends to do things like syntax highlighting, without needing to engage in
-- text manipulation to figure out syntax classes.
pattern Name :: Ident -> Portrayal
pattern Name nm = Portrayal (Fix (NameF nm))

-- | An integral literal.
--
-- This pattern does not round-trip, as it ignores the base when matching and
-- provides base 10 when constructing.  Prefer 'LitIntBase' when matching if
-- the base is relevant, but it should be fine to construct by this pattern if
-- base 10 is desired.
pattern LitInt :: Integer -> Portrayal
pattern LitInt x = Portrayal (Fix (LitIntF x))

-- | An integral literal in the given base.
--
-- @since 0.3.0
pattern LitIntBase :: Base -> Integer -> Portrayal
pattern LitIntBase b x = Portrayal (Fix (LitIntBaseF b x))

-- | A rational / floating-point literal.
--
-- Discouraged for new uses; use 'LitFloat' instead if possible.
pattern LitRat :: Rational -> Portrayal
pattern LitRat x = Portrayal (Fix (LitRatF x))

-- | A rational / floating-point literal.
--
-- @since 0.3.0
pattern LitFloat :: FloatLiteral -> Portrayal
pattern LitFloat x = Portrayal (Fix (LitFloatF x))

-- | A special (infinite or NaN) floating-point value.
--
-- @since 0.3.0
pattern SpecialFloat :: SpecialFloatVal -> Portrayal
pattern SpecialFloat x = Portrayal (Fix (SpecialFloatF x))

-- | A string literal.
--
-- Some backends may be capable of flowing these onto multiple lines
-- automatically, which they wouldn't be able to do with opaque text.
pattern LitStr :: Text -> Portrayal
pattern LitStr x = Portrayal (Fix (LitStrF x))

-- | A character literal.
pattern LitChar :: Char -> Portrayal
pattern LitChar x = Portrayal (Fix (LitCharF x))

-- | An opaque chunk of text included directly in the pretty-printed output.
--
-- This is used by things like 'strAtom' that don't understand their contents,
-- and will miss out on any syntax-aware features provided by backends.
pattern Opaque :: Text -> Portrayal
pattern Opaque txt = Portrayal (Fix (OpaqueF txt))

-- | A function or constructor application of arbitrary arity.
--
-- Although we could have just unary function application, this gives backends
-- a hint about how to format the result: for example, the "pretty" backend
-- prints the function (parenthesized if non-atomic) followed by the arguments
-- indented by two spaces; a chain of unary applications would be needlessly
-- parenthesized.
--
-- Given:
--
-- @
-- Apply (Name \"These\") [LitInt 2, LitInt 4]
-- @
--
-- We render something like @These 2 4@, or if line-wrapped:
--
-- @
-- These
--   2
--   4
-- @
pattern Apply :: Portrayal -> [Portrayal] -> Portrayal
pattern Apply f xs = Portrayal (Fix (ApplyF (Coerced f) (Coerced xs)))

-- | A binary operator application.
--
-- The fixity is used to avoid unnecessary parentheses, even in chains of
-- operators of the same precedence.
--
-- Given:
--
-- @
-- Binop (Name "+") (infixl_ 6)
--   [ Binop (Name "+") (infixl_ 6) [LitInt 2, LitInt 4]
--   , "6"
--   ]
-- @
--
-- We render something like: @2 + 4 + 6@
pattern Binop
  :: Ident -> Infixity -> Portrayal -> Portrayal -> Portrayal
pattern Binop nm inf x y =
  Portrayal (Fix (BinopF nm inf (Coerced x) (Coerced y)))

-- | A list literal.
--
-- Given:
--
-- @
-- List
--   [ Apply (Name \"These\") [LitInt 2, LitInt 4]
--   , Apply (Name \"That\") [LitInt 6]
--   ]
-- @
--
-- We render something like:
--
-- @
-- [ These 2 4
-- , That 6
-- ]
-- @
pattern List :: [Portrayal] -> Portrayal
pattern List xs = Portrayal (Fix (ListF (Coerced xs)))

-- | A tuple.
--
-- Given @Tuple [LitInt 2, LitInt 4]@, we render something like @(2, 4)@
pattern Tuple :: [Portrayal] -> Portrayal
pattern Tuple xs = Portrayal (Fix (TupleF (Coerced xs)))

-- | A lambda-case.
--
-- Given @LambdaCase [(LitInt 0, LitStr "hi"), (LitInt 1, LitStr "hello")]@, we
-- render something like @\\case 0 -> "hi"; 1 -> "hello"@.
--
-- This can be useful in cases where meaningful values effectively appear in
-- negative position in a type, like in a total map or table with non-integral
-- indices.
pattern LambdaCase :: [(Portrayal, Portrayal)] -> Portrayal
pattern LambdaCase xs = Portrayal (Fix (LambdaCaseF (Coerced xs)))

-- | A record literal.
--
-- Given:
--
-- @
-- Record
--   (Name \"Identity\")
--   [FactorPortrayal (Name "runIdentity") (LitInt 2)]
-- @
--
-- We render something like:
--
-- @
-- Identity
--   { runIdentity = 2
--   }
-- @
pattern Record :: Portrayal -> [FactorPortrayal Portrayal] -> Portrayal
pattern Record x xs = Portrayal (Fix (RecordF (Coerced x) (Coerced xs)))

-- | A type application.
--
-- Given @TyApp (Name \"Proxy\") (Name \"Int\")@, we render @Proxy \@Int@
pattern TyApp :: Portrayal -> Portrayal -> Portrayal
pattern TyApp x t = Portrayal (Fix (TyAppF (Coerced x) (Coerced t)))

-- | An explicit type signature.
--
-- Given @TySig (Name \"Proxy\") [Apply (Name \"Proxy\") [Name \"Int\"]]@, we
-- render @Proxy :: Proxy Int@
pattern TySig :: Portrayal -> Portrayal -> Portrayal
pattern TySig x t = Portrayal (Fix (TySigF (Coerced x) (Coerced t)))

-- | A quasiquoter expression.
--
-- Given:
--
-- @
-- Quot (Opaque \"expr\") (Binop (Opaque "+") _ [Opaque "x", Opaque "!y"])
-- @
--
-- We render something like @[expr| x + !y |]@
pattern Quot :: Text -> Portrayal -> Portrayal
pattern Quot t x = Portrayal (Fix (QuotF t (Coerced x)))

-- | A series of lines arranged vertically, if supported.
--
-- This is meant for use inside 'Quot', where it makes sense to use non-Haskell
-- syntax.
pattern Unlines :: [Portrayal] -> Portrayal
pattern Unlines xs = Portrayal (Fix (UnlinesF (Coerced xs)))

-- | Indent a sub-expression by the given number of spaces.
--
-- This is meant for use inside 'Quot', where it makes sense to use non-Haskell
-- syntax.
pattern Nest :: Int -> Portrayal -> Portrayal
pattern Nest n x = Portrayal (Fix (NestF n (Coerced x)))

-- | A class providing rendering to pseudo-Haskell syntax.
--
-- Instances should guarantee that they produce output that could, in
-- principle, be parsed as Haskell source that evaluates to a value equal to
-- the one being printed, provided the right functions, quasiquoters, plugins,
-- extensions, etc. are available.  Note this doesn't require you to /actually
-- implement/ these functions, quasiquoters, etc; just that it would be
-- feasible to do so.
--
-- Most of the time, this requirement is dispatched simply by portraying the
-- datum as its actual tree of data constructors.  However, since this can
-- sometimes be unwieldy, you might wish to have more stylized portrayals.
--
-- The most basic form of stylized portrayal is to retract the datum through a
-- function, e.g. portraying @4 :| [2] :: NonEmpty a@ as @fromList [4, 2]@.
--
-- For cases where you actually want to escape the Haskell syntax, you can use
-- (or pretend to use) quasiquoter syntax, e.g. portray
-- @EAdd (ELit 2) (EVar a)@ as @[expr| 2 + a |]@.
class Portray a where
  portray :: a -> Portrayal

  -- | Portray a list of the given element type
  --
  -- This is part of a Haskell98 mechanism for special-casing 'String' to print
  -- differently from other lists; clients of the library can largely ignore
  -- it.
  portrayList :: [a] -> Portrayal
  portrayList = List . map portray

-- | Convenience for using 'show' and wrapping the result in 'Opaque'.
--
-- Note this will be excluded from syntax highlighting and layout; see the
-- cautionary text on 'ShowAtom'.
showAtom :: Show a => a -> Portrayal
showAtom = strAtom . show

-- | Convenience for building an 'Opaque' from a 'String'.
--
-- Note this will be excluded from syntax highlighting for lack of semantic
-- information; consider using 'Name' instead.
strAtom :: String -> Portrayal
strAtom = Opaque . T.pack

-- | Convenience for building a 'Quot' from a 'String'.
strQuot :: String -> Portrayal -> Portrayal
strQuot = Quot . T.pack

-- | Convenience for building a 'Binop' with a 'String' operator name.
strBinop
  :: IdentKind -> String -> Infixity -> Portrayal -> Portrayal -> Portrayal
strBinop k = Binop . Ident k . T.pack

-- | Generics-based deriving of 'Portray' for product types.
--
-- Exported mostly to give Haddock something to link to; use
-- @deriving Portray via Wrapped Generic MyType@.
class GPortrayProduct f where
  gportrayProduct
    :: f a -> [FactorPortrayal Portrayal] -> [FactorPortrayal Portrayal]

instance GPortrayProduct U1 where
  gportrayProduct U1 = id

-- | Turn a field selector name into an 'Ident'.
selIdent :: String -> Ident
selIdent nm = Ident k (T.pack nm)
 where
  k = case nm of
    (c:_) | isAlpha c || c == '_' -> VarIdent
    _                             -> OpIdent

instance (Selector s, Portray a) => GPortrayProduct (S1 s (K1 i a)) where
  gportrayProduct (M1 (K1 x)) =
    (FactorPortrayal (selIdent $ selName @s undefined) (portray x) :)

instance (GPortrayProduct f, GPortrayProduct g)
      => GPortrayProduct (f :*: g) where
  gportrayProduct (f :*: g) = gportrayProduct f . gportrayProduct g

-- | Generics-based deriving of 'Portray'.
--
-- Exported mostly to give Haddock something to link to; use
-- @deriving Portray via Wrapped Generic MyType@.
class GPortray f where
  gportray :: f a -> Portrayal

instance GPortray f => GPortray (D1 d f) where
  gportray (M1 x) = gportray x

instance GPortray V1 where
  gportray x = case x of {}

instance (GPortray f, GPortray g) => GPortray (f :+: g) where
  gportray (L1 f) = gportray f
  gportray (R1 g) = gportray g

-- Detect operator constructor names (which must start with a colon) vs.
-- alphanumeric constructor names.
--
-- Operator constructor names in prefix application context arise in four
-- scenarios:
--
-- - The constructor has fewer than two arguments: @(:%) :: Int -> Thing@ gives
-- e.g. "(:%) 42".
-- - The constructor has more than two arguments:
-- @(:%) :: Int -> Int -> Int -> Thing@ gives e.g. "(:%) 2 4 6".
-- - The constructor is declared in prefix form or GADT syntax and has no
-- fixity declaration: @data Thing = (:%) Int Int@ gives e.g. "(:%) 2 4".
-- - The constructor is declared in record notation:
-- @data Thing = (:%) { _x :: Int, _y :: Int }@ gives e.g.
-- "(:%) { _x = 2, _y = 4 }".
--
-- Alphanumeric constructor names in infix application context only arise from
-- datatypes with alphanumeric constructors declared in infix syntax, e.g.
-- "data Thing = Int `Thing` Int".
detectConKind :: String -> IdentKind
detectConKind = \case (':':_) -> OpConIdent; _ -> ConIdent

conIdent :: String -> Ident
conIdent con = Ident (detectConKind con) (T.pack con)

prefixCon :: String -> Portrayal
prefixCon = Name . conIdent

toAssoc :: Associativity -> Assoc
toAssoc = \case
  LeftAssociative -> AssocL
  RightAssociative -> AssocR
  NotAssociative -> AssocNope

instance (KnownSymbol n, GPortrayProduct f)
      => GPortray (C1 ('MetaCons n fx 'True) f) where
  gportray (M1 x) = Record
    (prefixCon $ symbolVal' @n proxy#)
    (gportrayProduct x [])

instance (Constructor ('MetaCons n fx 'False), GPortrayProduct f)
      => GPortray (C1 ('MetaCons n fx 'False) f) where
  gportray (M1 x0) =
    case (nm, conFixity @('MetaCons n fx 'False) undefined, args) of
      ('(' : ',' : _, _, _) -> Tuple args
      (_, Infix lr p, [x, y]) -> Binop
        (conIdent nm)
        (Infixity (toAssoc lr) (toRational p))
        x
        y
      (_, _, []) -> prefixCon nm
      _ -> Apply (prefixCon nm) args
   where
    args = _fpPortrayal <$> gportrayProduct x0 []
    nm = conName @('MetaCons n fx 'False) undefined

instance (Generic a, GPortray (Rep a)) => Portray (Wrapped Generic a) where
  portray (Wrapped x) = gportray (from x)

-- | A newtype wrapper providing a 'Portray' instance via 'Integral'.
newtype PortrayIntLit a = PortrayIntLit a

instance Integral a => Portray (PortrayIntLit a) where
  portray (PortrayIntLit x) = LitInt (toInteger x)

deriving via PortrayIntLit Int       instance Portray Int
deriving via PortrayIntLit Int8      instance Portray Int8
deriving via PortrayIntLit Int16     instance Portray Int16
deriving via PortrayIntLit Int32     instance Portray Int32
deriving via PortrayIntLit Int64     instance Portray Int64
deriving via PortrayIntLit Integer   instance Portray Integer

deriving via PortrayIntLit Word      instance Portray Word
deriving via PortrayIntLit Word8     instance Portray Word8
deriving via PortrayIntLit Word16    instance Portray Word16
deriving via PortrayIntLit Word32    instance Portray Word32
deriving via PortrayIntLit Word64    instance Portray Word64
deriving via PortrayIntLit Natural   instance Portray Natural

-- | A newtype wrapper providing a 'Portray' instance via 'Real'.
--
-- Discouraged for new uses: use 'PortrayFloatLit' instead if possible.
newtype PortrayRatLit a = PortrayRatLit a

instance Real a => Portray (PortrayRatLit a) where
  portray (PortrayRatLit x) = LitRat (toRational x)

-- | A newtype wrapper providing a 'Portray' instance via 'RealFloat'.
--
-- @since 0.3.0
newtype PortrayFloatLit a = PortrayFloatLit a

instance RealFloat a => Portray (PortrayFloatLit a) where
  portray (PortrayFloatLit x)
    | isInfinite x = SpecialFloat (Infinity (x < 0))
    | isNaN x = SpecialFloat NaN
    | otherwise = LitFloat (floatToLiteral x)

deriving via PortrayFloatLit Float     instance Portray Float
deriving via PortrayFloatLit Double    instance Portray Double

-- | Convert a 'Fixed' to a 'FloatLiteral' representing its full precision.
--
-- @since 0.3.0
fixedToLiteral :: forall a. HasResolution a => Fixed a -> FloatLiteral
fixedToLiteral it@(MkFixed x) =
  FloatLiteral
    (x < 0)
    (T.pack $ wholePart ++ take fracDigits (fracPart ++ repeat '0'))
    (length wholePart)
 where
  denom = resolution it
  (whole, frac) = divMod (abs x) denom
  wholePart = show whole
  fracDigits :: Int
  fracDigits = ceiling $ (logBase 10 (fromIntegral denom) :: Double)
  fracPart = show $ (frac * 10 ^ fracDigits + denom - 1) `div` denom

instance HasResolution a => Portray (Fixed a) where
  portray = LitFloat . fixedToLiteral

-- | A newtype wrapper providing a 'Portray' instance via 'showAtom'.
--
-- Beware that instances made this way will not be subject to syntax
-- highlighting or layout, and will be shown as plain text all on one line.
-- It's recommended to derive instances via @'Wrapped' 'Generic'@ or hand-write
-- more detailed instances instead.
newtype ShowAtom a = ShowAtom { unShowAtom :: a }

instance Show a => Portray (ShowAtom a) where
  portray = showAtom . unShowAtom

instance Portray Char where
  portray = LitChar
  portrayList = LitStr . T.pack

instance Portray () where portray () = Tuple []
instance Portray Text where portray = LitStr

instance Portray a => Portray (Ratio a) where
  portray x = Binop (Ident OpIdent "%") (infixl_ 7)
    (portray $ numerator x)
    (portray $ denominator x)

deriving via Wrapped Generic (a, b)
  instance (Portray a, Portray b) => Portray (a, b)
deriving via Wrapped Generic (a, b, c)
  instance (Portray a, Portray b, Portray c) => Portray (a, b, c)
deriving via Wrapped Generic (a, b, c, d)
  instance (Portray a, Portray b, Portray c, Portray d) => Portray (a, b, c, d)
deriving via Wrapped Generic (a, b, c, d, e)
  instance (Portray a, Portray b, Portray c, Portray d, Portray e)
        => Portray (a, b, c, d, e)
deriving via Wrapped Generic (Maybe a)
  instance Portray a => Portray (Maybe a)
deriving via Wrapped Generic (Either a b)
  instance (Portray a, Portray b) => Portray (Either a b)
deriving via Wrapped Generic Void instance Portray Void
deriving via Wrapped Generic Bool instance Portray Bool

-- Aesthetic choice: I'd rather pretend Identity and Const are not records, so
-- don't derive them via Generic.
instance Portray a => Portray (Identity a) where
  portray (Identity x) = Apply (Name $ Ident ConIdent "Identity") [portray x]
instance Portray a => Portray (Const a b) where
  portray (Const x) = Apply (Name $ Ident ConIdent "Const") [portray x]

instance Portray a => Portray [a] where
  portray = portrayList

deriving via Wrapped Generic (Proxy a) instance Portray (Proxy a)

-- A few newtypes in 'base' propagate syntax-carrying instances like 'Num' and
-- 'Fractional' that some 'Portray' instances use as their output format.  For
-- these, we peek at the inner value's 'Portrayal' and, if it's syntax that
-- would be supported by the newtype, omit the constructor.

instance Portray a => Portray (Sum a) where
  portray (Sum x) = case portray x of
    LitInt n -> LitInt n
    p -> Apply (Name $ Ident ConIdent "Sum") [p]

instance Portray a => Portray (Product a) where
  portray (Product x) = case portray x of
    LitInt n -> LitInt n
    p -> Apply (Name $ Ident ConIdent "Product") [p]

instance Portray TyCon where
  portray tc = case nm of
    -- For now, don't try to parse DataKinds embedded in fake constructor
    -- names; just stick them in Opaque.
    (c:_) | isDigit c || c `elem` ['\'', '"'] -> Opaque (T.pack nm)
    _ -> prefixCon nm
   where
    nm = tyConName tc

portraySomeType :: SomeTypeRep -> Portrayal
portraySomeType (SomeTypeRep ty) = portrayType ty

-- | Portray the type described by the given 'TypeRep'.
--
-- This gives the type-level syntax for the type, as opposed to value-level
-- syntax that would construct the `TypeRep`.
portrayType :: TypeRep a -> Portrayal
portrayType = \case
  special | SomeTypeRep special == SomeTypeRep (typeRep @Type) ->
    Name $ Ident ConIdent "Type"
  Fun a b ->
    Binop (Ident OpIdent "->") (infixr_ (-1)) (portrayType a) (portrayType b)
  -- TODO(awpr); it'd be nice to coalesce the resulting nested 'Apply's.
  App f x -> Apply (portrayType f) [portrayType x]
  Con' con tys -> foldl (\x -> TyApp x . portraySomeType) (portray con) tys

instance Portray (TypeRep a) where
  portray = TyApp (Name $ Ident VarIdent "typeRep") . portrayType

instance Portray SomeTypeRep where
  portray (SomeTypeRep ty) = Apply
    (TyApp (Name $ Ident ConIdent "SomeTypeRep") (portrayType ty))
    [Name $ Ident VarIdent "typeRep"]

instance Portray (a :~: b) where portray Refl = Name $ Ident ConIdent "Refl"
instance Portray (Coercion a b) where
  portray Coercion = Name $ Ident ConIdent "Coercion"

-- | Portray a list-like type as "fromList [...]".
instance (IsList a, Portray (Exts.Item a)) => Portray (Wrapped IsList a) where
  portray =
    Apply (Name $ Ident VarIdent "fromList") . pure . portray . Exts.toList

deriving via Wrapped IsList (IntMap a)
  instance Portray a => Portray (IntMap a)
deriving via Wrapped IsList (Map k a)
  instance (Ord k, Portray k, Portray a) => Portray (Map k a)
deriving via Wrapped IsList (Set a)
  instance (Ord a, Portray a) => Portray (Set a)
deriving via Wrapped IsList (Seq a)
  instance Portray a => Portray (Seq a)
deriving via Wrapped IsList (NonEmpty a)
  instance Portray a => Portray (NonEmpty a)

-- Note: intentionally no instance for @'Wrapped1' 'Foldable'@, since that
-- doesn't ensure that 'fromList' is actually a valid way to construct @f a@.

-- | Construct a 'Portrayal' of a 'CallStack' without the "callStack" prefix.
portrayCallStack :: [(String, SrcLoc)] -> Portrayal
portrayCallStack xs = Unlines
  [ Opaque "GHC.Stack.CallStack:"
  , Nest 2 $ Unlines
      [ strAtom (func ++ ", called at " ++ prettySrcLoc loc)
      | (func, loc) <- xs
      ]
  ]

instance Portray CallStack where
  portray cs = case getCallStack cs of
    [] -> Name $ Ident VarIdent "emptyCallStack"
    xs -> strQuot "callStack" $ portrayCallStack xs

-- | Fold a @Fix f@ to @a@ given a function to collapse each layer.
cata :: Functor f => (f a -> a) -> Fix f -> a
cata f = go
 where
  go (Fix fa) = f $ go <$> fa
