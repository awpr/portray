-- Copyright 2020-2021 Google LLC
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

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

#if __GLASGOW_HASKELL__ == 900
{-# OPTIONS_GHC -Wno-deprecations #-}  -- Want an instance for Option on 9.0.
#endif

-- | Provides a typeclass for rendering values to pseudo-Haskell syntax.

module Data.Portray.Class
         ( -- * Portray
           Portray(..)
           -- ** Via Generic
         , GPortray(..), GPortrayProduct(..)
           -- ** Via Show, Integral, and Real
         , PortrayIntLit(..), PortrayRatLit(..), ShowAtom(..)
         ) where

import Control.Applicative (ZipList)
import Data.Char (GeneralCategory, isAlpha)
import Data.Complex (Complex)
import Data.Fixed (Fixed, HasResolution)
import Data.Functor.Identity (Identity(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import qualified Data.Functor.Sum as F (Sum(..))
import qualified Data.Functor.Product as F (Product(..))
import Data.Int (Int8, Int16, Int32, Int64)
import Data.IntMap (IntMap)
import Data.IntSet (IntSet)
import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import Data.Monoid (All, Any, Product, Sum, Dual, Last, First, Ap, Alt)
import Data.Proxy (Proxy)
import Data.Ratio (Ratio, numerator, denominator)
import Data.Semigroup
         ( WrappedMonoid, Max, Min, Arg
#if !MIN_VERSION_base(4, 16, 0)
         , Option
#endif
         )
import qualified Data.Semigroup as SG
import Data.Sequence (Seq)
import Data.Set (Set)
import Data.Text (Text)
import Data.Tree (Tree)
import Data.Type.Coercion (Coercion(..))
import Data.Type.Equality ((:~:)(..))
import Data.Void (Void)
import Data.Word (Word8, Word16, Word32, Word64)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import GHC.Arr (Array)
import qualified GHC.Arr as Arr
import GHC.Exts
         ( IsList, RuntimeRep(..), VecCount(..), VecElem(..)
         , fromString, proxy#
         )
import qualified GHC.Exts as Exts
import GHC.Fingerprint (Fingerprint(..))
import GHC.Generics
         ( (:*:)(..), (:+:)(..)
         , Generic(..), Rep
         , U1(..), K1(..), M1(..), V1
         , Meta(..), D1, C1, S1
         , Constructor, conName, conFixity
         , Selector, selName
         , Fixity(..), Associativity(..)
         )
import GHC.Stack (CallStack, getCallStack)
import GHC.TypeLits (KnownSymbol, SomeSymbol(..), symbolVal, symbolVal')
import GHC.TypeNats (SomeNat(..), natVal)
import Numeric.Natural (Natural)
import System.IO (IOMode)
import Type.Reflection
         ( TyCon, TypeRep, Module, SomeTypeRep(..)
         , modulePackage, moduleName
         )

import Data.Wrapped (Wrapped(..))

import Data.Portray.Portrayal

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
newtype PortrayRatLit a = PortrayRatLit a

instance Real a => Portray (PortrayRatLit a) where
  portray (PortrayRatLit x) = LitRat (toRational x)

deriving via PortrayRatLit Float     instance Portray Float
deriving via PortrayRatLit Double    instance Portray Double
deriving via PortrayRatLit (Fixed a)
  instance HasResolution a => Portray (Fixed a)

-- | A newtype wrapper providing a 'Portray' instance via 'showAtom'.
--
-- Beware that instances made this way will not be subject to syntax
-- highlighting or layout, and will be shown as plain text all on one line.
-- It's recommended to derive instances via @'Wrapped' 'Generic'@ or hand-write
-- more detailed instances instead.
newtype ShowAtom a = ShowAtom { unShowAtom :: a }

-- | 'Portray' via 'show' followed by detecting the kind of 'Name' it returned.
instance Show a => Portray (ShowAtom a) where
  portray = showAtom . unShowAtom

-- DerivingVia instance carrier for 'show'ing an enum-style sum type and
-- detecting its name from the result.  This is used for a few types from base
-- with Show but no Generic.
newtype ShowName a = ShowName { unShowName :: a }

#if __GLASGOW_HASKELL__ < 810
-- Older GHCs don't understand that DerivingVia / GND can make a data
-- constructor necessary even without mentioning it.
_unused :: a -> ShowName a
_unused = ShowName
#endif

instance Show a => Portray (ShowName a) where
  portray = Name . fromString . show . unShowName

instance Portray Char where
  portray = LitChar
  portrayList = LitStr . T.pack

instance Portray () where portray () = Tuple []
instance Portray Text where portray = LitStr

-- | Lazily test whether the length of a Text is more than a given number.
--
-- 'textLengthGT' never forces more than @n@ characters plus the remainder of
-- the present chunk, nor even looks to see whether there are further chunks.
textLengthGT :: Int -> TL.Text -> Bool
textLengthGT n0 = go n0 . TL.toChunks
 where
  go _ [] = False
  go n (ch:chs) =
    let !n' = n - T.length ch
    in  n' < 0 || go n' chs

-- | Formats long 'TL.Text's as @fromChunks@ to avoid massive allocations.
instance Portray TL.Text where
  portray txt
    | textLengthGT 4096 txt =
        Apply (Name "fromChunks") [List $ portray <$> TL.toChunks txt]
    | otherwise = LitStr (TL.toStrict txt)

instance Portray a => Portray (Ratio a) where
  portray x = Binop (Ident OpIdent "%") (infixl_ 7)
    (portray $ numerator x)
    (portray $ denominator x)

deriving via Wrapped Generic Ident
  instance Portray Ident
deriving via Wrapped Generic IdentKind
  instance Portray IdentKind
deriving via Wrapped Generic Assoc
  instance Portray Assoc
deriving via Wrapped Generic Infixity
  instance Portray Infixity
deriving via Wrapped Generic (PortrayalF a)
  instance Portray a => Portray (PortrayalF a)
deriving via Wrapped Generic (FactorPortrayal a)
  instance Portray a => Portray (FactorPortrayal a)

deriving newtype
  instance (forall a. Portray a => Portray (f a)) => Portray (Fix f)
deriving newtype instance Portray Portrayal

deriving via Wrapped Generic Void instance Portray Void
deriving via Wrapped Generic Bool instance Portray Bool
deriving via Wrapped Generic Any instance Portray Any
deriving via Wrapped Generic All instance Portray All
deriving via Wrapped Generic Ordering instance Portray Ordering
deriving via Wrapped Generic (Sum a) instance Portray a => Portray (Sum a)
deriving via Wrapped Generic (Product a)
  instance Portray a => Portray (Product a)
deriving via Wrapped Generic (Dual a) instance Portray a => Portray (Dual a)
deriving via Wrapped Generic (Last a) instance Portray a => Portray (Last a)
deriving via Wrapped Generic (First a) instance Portray a => Portray (First a)
deriving via Wrapped Generic (ZipList a)
  instance Portray a => Portray (ZipList a)
deriving via Wrapped Generic (WrappedMonoid a)
  instance Portray a => Portray (WrappedMonoid a)
deriving via Wrapped Generic (SG.Last a)
  instance Portray a => Portray (SG.Last a)
deriving via Wrapped Generic (SG.First a)
  instance Portray a => Portray (SG.First a)
deriving via Wrapped Generic (Max a) instance Portray a => Portray (Max a)
deriving via Wrapped Generic (Min a) instance Portray a => Portray (Min a)
deriving via Wrapped Generic (Arg a b)
  instance (Portray a, Portray b) => Portray (Arg a b)
deriving via Wrapped Generic (Complex a)
  instance Portray a => Portray (Complex a)
deriving via Wrapped Generic (Proxy a) instance Portray (Proxy a)
deriving via Wrapped Generic (Ap f a)
  instance Portray (f a) => Portray (Ap f a)
deriving via Wrapped Generic (Alt f a)
  instance Portray (f a) => Portray (Alt f a)

-- 4.15 is released already, and Option is removed at HEAD.  It seems a pretty
-- safe bet to be forwards-compatible by removing the instance for 4.16 and
-- later.
#if !MIN_VERSION_base(4, 16, 0)
deriving via Wrapped Generic (Option a)
  instance Portray a => Portray (Option a)
#endif

#if MIN_VERSION_base(4, 15, 0)
deriving via Wrapped Generic GeneralCategory instance Portray GeneralCategory
deriving via Wrapped Generic Fingerprint instance Portray Fingerprint
#else
-- These have no Generic instance before 4.15.
instance Portray GeneralCategory where
  portray = Name . fromString . show

instance Portray Fingerprint where
  portray (Fingerprint x y) = Apply (Name "Fingerprint") [portray x, portray y]
#endif

instance Portray RuntimeRep where
  portray = \case
    VecRep c e -> Apply (Name "VecRep") [portray c, portray e]
    TupleRep reps -> Apply (Name "TupleRep") [portray reps]
    SumRep reps -> Apply (Name "SumRep") [portray reps]
    rep -> Name $ fromString $ show rep

deriving via ShowName VecCount instance Portray VecCount
deriving via ShowName VecElem instance Portray VecElem
deriving via ShowName IOMode instance Portray IOMode

deriving via Wrapped Generic (a, b)
  instance (Portray a, Portray b) => Portray (a, b)
deriving via Wrapped Generic (a, b, c)
  instance (Portray a, Portray b, Portray c) => Portray (a, b, c)
deriving via Wrapped Generic (a, b, c, d)
  instance (Portray a, Portray b, Portray c, Portray d) => Portray (a, b, c, d)
deriving via Wrapped Generic (a, b, c, d, e)
  instance (Portray a, Portray b, Portray c, Portray d, Portray e)
        => Portray (a, b, c, d, e)
deriving via Wrapped Generic (a, b, c, d, e, f)
  instance (Portray a, Portray b, Portray c, Portray d, Portray e, Portray f)
        => Portray (a, b, c, d, e, f)
deriving via Wrapped Generic (a, b, c, d, e, f, g)
  instance ( Portray a, Portray b, Portray c, Portray d, Portray e, Portray f
           , Portray g
           )
        => Portray (a, b, c, d, e, f, g)
deriving via Wrapped Generic (Maybe a)
  instance Portray a => Portray (Maybe a)
deriving via Wrapped Generic (Either a b)
  instance (Portray a, Portray b) => Portray (Either a b)
deriving via Wrapped Generic (F.Sum f g a)
  instance (Portray (f a), Portray (g a)) => Portray (F.Sum f g a)
deriving via Wrapped Generic (F.Product f g a)
  instance (Portray (f a), Portray (g a)) => Portray (F.Product f g a)
deriving via Wrapped Generic (Compose f g a)
  instance (Portray (f (g a))) => Portray (Compose f g a)

-- Aesthetic choice: I'd rather pretend Identity and Const are not records, so
-- don't derive them via Generic.
instance Portray a => Portray (Identity a) where
  portray (Identity x) = Apply (Name $ Ident ConIdent "Identity") [portray x]
instance Portray a => Portray (Const a b) where
  portray (Const x) = Apply (Name $ Ident ConIdent "Const") [portray x]

instance Portray a => Portray [a] where
  portray = portrayList

instance Portray TyCon where
  -- typeRepTyCon @TheTyCon typeRep
  portray con = Apply
    (TyApp (Name "typeRepTyCon") (portrayTyCon con))
    [Name "typeRep"]

instance Portray Module where
  portray m = Apply
    (Name "Module")
    [portray (modulePackage m), portray (moduleName m)]

instance Portray (TypeRep a) where
  portray = TyApp (Name $ Ident VarIdent "typeRep") . portrayType

instance Portray SomeTypeRep where
  portray (SomeTypeRep ty) = Apply
    (TyApp (Name $ Ident ConIdent "SomeTypeRep") (portrayType ty))
    [Name $ Ident VarIdent "typeRep"]

instance Portray SomeNat where
  portray (SomeNat p) = Apply
    (TyApp (Name "SomeNat") (portray (natVal p)))
    [Name "Proxy"]

instance Portray SomeSymbol where
  portray (SomeSymbol p) = Apply
    (TyApp (Name "SomeSymbol") (portray (symbolVal p)))
    [Name "Proxy"]

instance Portray (a :~: b) where portray Refl = Name $ Ident ConIdent "Refl"
instance Portray (Coercion a b) where
  portray Coercion = Name $ Ident ConIdent "Coercion"

instance (Arr.Ix i, Portray i, Portray a) => Portray (Array i a) where
  portray x =
    Apply (Name "array") [portray (Arr.bounds x), portray (Arr.assocs x)]

-- | Portray a list-like type as "fromList [...]".
instance (IsList a, Portray (Exts.Item a)) => Portray (Wrapped IsList a) where
  portray =
    Apply (Name $ Ident VarIdent "fromList") . pure . portray . Exts.toList

deriving via Wrapped IsList IntSet instance Portray IntSet
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
deriving via Wrapped Generic (Tree a)
  instance Portray a => Portray (Tree a)

-- Note: intentionally no instance for @'Wrapped1' 'Foldable'@, since that
-- doesn't ensure that 'fromList' is actually a valid way to construct @f a@.

instance Portray CallStack where
  portray cs = case getCallStack cs of
    [] -> Name $ Ident VarIdent "emptyCallStack"
    xs -> strQuot "callStack" $ portrayCallStack xs
