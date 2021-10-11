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

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- | Provides a pseudo-Haskell syntax tree type for rendering arbitrary values.

module Data.Portray.Portrayal
         ( -- * Syntax Tree
           Portrayal
             ( Name, LitInt, LitRat, LitStr, LitChar, Opaque
             , Apply, Binop, Tuple, List
             , LambdaCase, Record, TyApp, TySig
             , Quot, Unlines, Nest
             , ..
             )
         , FactorPortrayal(..)
         , IdentKind(..), Ident(..)
           -- ** Operator Fixity
         , Assoc(..), Infixity(..), infix_, infixl_, infixr_
           -- ** Base Functor
         , PortrayalF(..)
           -- * Convenience
         , showAtom, strAtom, strQuot, strBinop
           -- * Miscellaneous
         , Fix(..), cata, portrayCallStack, portrayType, portrayTyCon
         ) where

import Data.Char (isAlpha, isDigit, isUpper)
import Data.Coerce (Coercible, coerce)
import Data.Kind (Type)
import Data.String (IsString(fromString))
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import GHC.Stack (SrcLoc, prettySrcLoc)
import Type.Reflection
         ( TyCon, TypeRep, SomeTypeRep(..)
         , pattern App, pattern Con', pattern Fun
         , tyConName, typeRep
         )

-- | Associativity of an infix operator.
data Assoc = AssocL | AssocR | AssocNope
  deriving (Read, Show, Eq, Ord, Generic)

-- | Associativity and binding precedence of an infix operator.
data Infixity = Infixity !Assoc !Rational
  deriving (Read, Show, Eq, Ord, Generic)

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

-- | An identifier or operator name.
data Ident = Ident !IdentKind !Text
  deriving (Eq, Ord, Read, Show, Generic)

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

-- | A single level of pseudo-Haskell expression; used to define 'Portrayal'.
data PortrayalF a
  = NameF {-# UNPACK #-} !Ident
    -- ^ An identifier, including variable, constructor and operator names.
  | LitIntF !Integer
    -- ^ An integral literal.  e.g. @42@
  | LitRatF {-# UNPACK #-} !Rational
    -- ^ A rational / floating-point literal.  e.g. @42.002@
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

-- | A 'Portrayal' along with a field name; one piece of a record literal.
data FactorPortrayal a = FactorPortrayal
  { _fpFieldName :: !Ident
  , _fpPortrayal :: !a
  }
  deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable, Generic)


-- | Fixed-point of a functor.
--
-- There are many packages that provide equivalent things, but we need almost
-- nothing but the type itself, so we may as well just define one locally.
newtype Fix f = Fix (f (Fix f))
  deriving Generic

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
  deriving newtype (Show, Read)

{-# COMPLETE
      Name, LitInt, LitRat, LitStr, LitChar, Opaque, Apply, Binop, Tuple,
      List, LambdaCase, Record, TyApp, TySig, Quot, Unlines, Nest
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
pattern LitInt :: Integer -> Portrayal
pattern LitInt x = Portrayal (Fix (LitIntF x))


-- | A rational / floating-point literal.
pattern LitRat :: Rational -> Portrayal
pattern LitRat x = Portrayal (Fix (LitRatF x))

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

-- | Convenience for using 'show' and wrapping the result in 'Opaque'.
--
-- Note this will be excluded from syntax highlighting and layout, and the
-- contents will be shown as plain text all on one line.  It's recommended to
-- derive instances via @'Data.Wrapped.Wrapped' 'Generic'@ or hand-write more
-- detailed instances instead.
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

portraySomeType :: SomeTypeRep -> Portrayal
portraySomeType (SomeTypeRep ty) = portrayType ty

-- | Portray a 'TyCon' without any extra surrounding text.
portrayTyCon :: TyCon -> Portrayal
portrayTyCon tc = case nm of
    -- For now, don't try to parse DataKinds embedded in fake constructor
    -- names; just stick them in Opaque.
    (c:_) | isDigit c || c `elem` ['\'', '"'] -> Opaque (T.pack nm)
    _ -> Name $ fromString nm
   where
    nm = tyConName tc

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
  Con' con tys -> foldl (\x -> TyApp x . portraySomeType) (portrayTyCon con) tys

-- | Construct a 'Portrayal' of a 'GHC.Stack.CallStack' without extra text.
portrayCallStack :: [(String, SrcLoc)] -> Portrayal
portrayCallStack xs = Unlines
  [ Opaque "GHC.Stack.CallStack:"
  , Nest 2 $ Unlines
      [ strAtom (func ++ ", called at " ++ prettySrcLoc loc)
      | (func, loc) <- xs
      ]
  ]

-- | Fold a @Fix f@ to @a@ given a function to collapse each layer.
cata :: Functor f => (f a -> a) -> Fix f -> a
cata f = go
 where
  go (Fix fa) = f $ go <$> fa
