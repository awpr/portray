-- Copyright 2018-2021 Google LLC
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

-- | Typeclass for pretty-printed diffs between two instances of a type.
--
-- Derive it for arbitrary sum-of-products types as follows:
--
-- @
--     data Foo = Foo Int | Bar Bool
--       deriving Generic
--       deriving (Portray, Diff) via Wrapped Generic Foo
-- @
--
-- If the type of the compared values has a custom Eq instance, the equality
-- comparison used by the Generic derived Diff instance *will differ* from the
-- custom one implemented for the type. It will only check to make sure that
-- the representations of the two types are the same. If you still want the diff
-- algorithm to look into the type, you will need to implement a custom Diff
-- instance alongside the custom Eq instance. If you don't want the diff
-- algorithm to look inside a type, and instead use the custom Eq instance, use:
--
-- @
--     data Foo = ...
--     instance Diff Foo where diff = diffAtom
-- @

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Portray.Diff
         ( -- * Structural Diffs
           Diff(..), diffAtom
           -- * Atomic Diff
         , DiffAtom(..), diffVs
           -- * Generic
         , GDiff(..), GDiffRecord(..), GDiffCtor(..)
         ) where

import Prelude hiding (zipWith)

import qualified Data.Foldable as F (toList)
import Data.Function (on)
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Int (Int8, Int16, Int32, Int64)
import qualified Data.IntMap.Strict as IM
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (fromMaybe, isNothing)
import Data.Ratio (Ratio)
import Data.Semigroup (Any(..))
import Data.Sequence (Seq)
import Data.Text (Text)
import Data.Type.Equality ((:~:)(..))
import Data.Word (Word8, Word16, Word32, Word64)
import GHC.Exts (IsList(..), fromString, proxy#)
import qualified GHC.Exts as Exts (toList)
import GHC.Generics
import GHC.TypeLits (KnownSymbol, symbolVal')
import Type.Reflection (TypeRep, SomeTypeRep(..))

import Data.Portray
         ( Portray(..), Portrayal(..), PortrayalF(..), Fix(..)
         , IdentKind(..), Ident(..), Base(..)
         , FloatLiteral(..), SpecialFloatVal(..)
         , Infixity(..), Assoc(..), FactorPortrayal(..)
         , showAtom, portrayType
         )
import qualified Data.DList as D
import Data.Wrapped (Wrapped(..), Wrapped1(..))

-- | Structural comparison between values giving a description of differences.
class Diff a where
  -- | Returns 'Nothing' when equal; or a 'Portrayal' showing the differences.
  diff :: a -> a -> Maybe Portrayal
  default diff :: (Generic a, GDiff a (Rep a)) => a -> a -> Maybe Portrayal
  diff = diff `on` Wrapped @Generic

instance (Generic a, GDiff a (Rep a)) => Diff (Wrapped Generic a) where
  diff (Wrapped x) (Wrapped y) = gdiff x y (from x) (from y)

-- | Produce a 'Portrayal' describing a single atomic difference.
vs, diffVs :: Portrayal -> Portrayal -> Portrayal
vs a b = Binop (Ident OpIdent "/=") (Infixity AssocNope 4) a b
diffVs = vs

-- | Diff on an atomic type, just by using the Eq and Portray instances without
-- using any internal structure of the type.
diffAtom :: (Eq a, Portray a) => a -> a -> Maybe Portrayal
diffAtom a b
  | a == b = Nothing
  | otherwise = Just (portray a `vs` portray b)

-- | Diff record fields, creating docs only for fields that differ.
class GDiffRecord f where
  gdiffRecord :: f x -> f x -> D.DList (FactorPortrayal Portrayal)

-- Note: no instance GDiffRecord U1 because empty "records" like
-- @data Rec = Rec {}@ are not considered to be records by Generic; they'll go
-- through GDiffCtor instead.

instance (Selector s, Diff a) => GDiffRecord (S1 s (K1 i a)) where
  gdiffRecord (M1 (K1 a)) (M1 (K1 b)) =
    foldMap D.singleton $  -- Maybe diff to DList of (zero or one) diffs.
      FactorPortrayal (fromString $ selName @s undefined) <$>
      diff a b

instance (GDiffRecord f, GDiffRecord g) => GDiffRecord (f :*: g) where
  gdiffRecord (fa :*: ga) (fb :*: gb) = gdiffRecord fa fb <> gdiffRecord ga gb

-- | Diff constructor fields, filling equal fields with "_" and reporting
-- whether any diffs were detected.
--
-- N.B. this works fine on record constructors, too, in case we want to support
-- configuring whether to use record syntax or constructor application syntax.
--
-- This is a separate class from GDiffRecord because it'd be wasteful to
-- accumulate tons of "_" docs for records with lots of fields and then discard
-- them.
class GDiffCtor f where
  gdiffCtor :: f x -> f x -> (Any, D.DList Portrayal)

-- Nullary constructors have no diffs compared against themselves.
instance GDiffCtor U1 where
  gdiffCtor U1 U1 = mempty

instance Diff a => GDiffCtor (S1 s (K1 i a)) where
  gdiffCtor (M1 (K1 a)) (M1 (K1 b)) = case diff a b of
    Nothing -> (mempty, D.singleton (Opaque "_"))
    Just d -> (Any True, D.singleton d)

instance (GDiffCtor f, GDiffCtor g) => GDiffCtor (f :*: g) where
  gdiffCtor (fa :*: ga) (fb :*: gb) = gdiffCtor fa fb <> gdiffCtor ga gb

-- | Generic implementation of 'Diff'.
--
-- This is primarily exported to appease Haddock; use @via Wrapped Generic T@
-- to access this functionality.
class GDiff a f where
  gdiff :: a -> a -> f x -> f x -> Maybe Portrayal

instance (KnownSymbol n, GDiffRecord f)
      => GDiff a (C1 ('MetaCons n fx 'True) f) where
  gdiff _ _ (M1 a) (M1 b) = case D.toList (gdiffRecord a b) of
    [] -> Nothing
    ds -> Just $ Record (Name $ fromString $ symbolVal' @n proxy#) ds

instance (KnownSymbol n, GDiffCtor f)
      => GDiff a (C1 ('MetaCons n fx 'False) f) where
  gdiff _ _ (M1 a) (M1 b) = case gdiffCtor a b of
    (Any False, _ ) -> Nothing
    (Any True , ds) -> Just $ case nm of
      -- Print tuple constructors with tuple syntax.  Ignore infix
      -- constructors, since they'd make for pretty hard-to-read diffs.
      '(':',':_ -> Tuple (D.toList ds)
      _ -> Apply (Name $ fromString nm) (D.toList ds)
   where
    nm = symbolVal' @n proxy#

instance (Portray a, GDiff a f, GDiff a g) => GDiff a (f :+: g) where
  gdiff origA origB a b = case (a, b) of
    (L1 fa, L1 fb) -> gdiff origA origB fa fb
    (R1 ga, R1 gb) -> gdiff origA origB ga gb
    _              -> Just (portray origA `vs` portray origB)

instance GDiff a f => GDiff a (D1 d f) where
  gdiff origA origB (M1 a) (M1 b) = gdiff origA origB a b

instance Diff ()
instance (Portray a, Portray b, Diff a, Diff b) => Diff (a, b)
instance (Portray a, Portray b, Portray c, Diff a, Diff b, Diff c)
       => Diff (a, b, c)
instance ( Portray a, Portray b, Portray c, Portray d
         , Diff a, Diff b, Diff c, Diff d
         )
      => Diff (a, b, c, d)
instance ( Portray a, Portray b, Portray c, Portray d, Portray e
         , Diff a, Diff b, Diff c, Diff d, Diff e
         )
      => Diff (a, b, c, d, e)
instance (Portray a, Portray b, Diff a, Diff b) => Diff (Either a b)
instance (Portray a, Diff a) => Diff (Maybe a)

instance Diff Bool
instance Diff Int where diff = diffAtom
instance Diff Int8 where diff = diffAtom
instance Diff Int16 where diff = diffAtom
instance Diff Int32 where diff = diffAtom
instance Diff Int64 where diff = diffAtom
instance Diff Word where diff = diffAtom
instance Diff Word8 where diff = diffAtom
instance Diff Word16 where diff = diffAtom
instance Diff Word32 where diff = diffAtom
instance Diff Word64 where diff = diffAtom
instance Diff Char where diff = diffAtom
instance Diff Integer where diff = diffAtom
instance Diff Float where diff = diffAtom
instance Diff Double where diff = diffAtom
instance Diff Text where diff = diffAtom
instance (Eq a, Portray a) => Diff (Ratio a) where diff = diffAtom

-- | A @DerivingVia@ wrapper for providing 'Diff' by 'Eq' and 'Portray'.
newtype DiffAtom a = DiffAtom a
  deriving newtype (Eq, Portray)

instance (Eq a, Portray a) => Diff (DiffAtom a) where diff = diffAtom

-- | Diff on lists does a diff on the zip, plus special handling for the
-- mismatched lengths.
instance (Portray a, Diff a) => Diff [a] where
  diff as0 bs0 =
    if all isNothing d
      then Nothing
      else Just $ List $ fromMaybe (Opaque "_") <$> d
   where
    -- Extended @zipWith diff@ which doesn't drop on mismatched lengths.
    go :: [a] -> [a] -> [Maybe Portrayal]
    go [] [] = []
    go (a:as) [] =
      Just (portray a `vs` Opaque "_") : go as []
    go [] (b:bs) =
      Just (Opaque "_" `vs` portray b) : go [] bs
    go (a:as) (b:bs) = diff a b : go as bs

    d = go as0 bs0

-- | Diff as if the type were a list, via 'Exts.toList'.
instance (IsList a, Portray (Item a), Diff (Item a))
      => Diff (Wrapped IsList a) where
  diff = diff `on` Exts.toList

-- | Diff as if the type were a list, via 'F.toList'.
instance (Portray a, Foldable f, Diff a)
      => Diff (Wrapped1 Foldable f a) where
  diff = diff `on` F.toList

deriving via Wrapped IsList (NonEmpty a)
  instance (Portray a, Diff a) => Diff (NonEmpty a)
deriving via Wrapped IsList (Seq a)
  instance (Portray a, Diff a) => Diff (Seq a)

instance (Portray a, Diff a) => Diff (IM.IntMap a) where
  diff as bs =
    if IM.null allDiffs
      then Nothing
      else Just $ List [Tuple [showAtom k, v] | (k, v) <- IM.toList allDiffs]
   where
    -- Note: we could have used 'align', but "these" has a ton of dependencies
    -- and it'd only save a few lines of code.
    aOnly, bOnly, valDiffs, allDiffs :: IM.IntMap Portrayal
    aOnly = IM.map (\a -> portray a `vs` Opaque "_") $ IM.difference as bs
    bOnly = IM.map (\b -> Opaque "_" `vs` portray b) $ IM.difference bs as
    valDiffs = IM.mapMaybe id $ IM.intersectionWith diff as bs
    allDiffs = IM.unions [aOnly, bOnly, valDiffs]

deriving via Wrapped Generic Assoc instance Diff Assoc
deriving via Wrapped Generic IdentKind instance Diff IdentKind
deriving via Wrapped Generic Ident instance Diff Ident
deriving via Wrapped Generic Infixity instance Diff Infixity
deriving via Wrapped Generic Base instance Diff Base
deriving via Wrapped Generic FloatLiteral instance Diff FloatLiteral
deriving via Wrapped Generic SpecialFloatVal instance Diff SpecialFloatVal
deriving via Wrapped Generic (FactorPortrayal a)
  instance Diff a => Diff (FactorPortrayal a)
deriving via Wrapped Generic (PortrayalF a)
  instance (Portray a, Diff a) => Diff (PortrayalF a)
deriving newtype
  instance ( forall a. (Portray a, Diff a) => Diff (f a)
           , forall a. Portray a => Portray (f a)
           )
        => Diff (Fix f)
deriving newtype instance Diff Portrayal

deriving via Wrapped Generic (Identity a) instance Diff a => Diff (Identity a)
deriving via Wrapped Generic (Const a b) instance Diff a => Diff (Const a b)

instance Diff (TypeRep a) where
  diff x y
    | x == y    = Nothing
    | otherwise = Just $ portray x `diffVs` portray y

instance Diff SomeTypeRep where
  diff x@(SomeTypeRep tx) y@(SomeTypeRep ty)
    | x == y = Nothing
    | otherwise =
        Just $ Apply
          (TyApp
            (Name $ Ident ConIdent "SomeTypeRep")
            (portrayType tx `diffVs` portrayType ty))
          [Name $ Ident VarIdent "typeRep"]

instance Diff (a :~: b) where diff Refl Refl = Nothing
