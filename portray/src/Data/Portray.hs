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

{-# LANGUAGE PatternSynonyms #-}

-- | Provides a compatibility layer of Haskell-like terms for pretty-printers.

module Data.Portray
         ( -- * Syntax Tree
           Portrayal(..)
         , FactorPortrayal(..)
         , IdentKind(..), Ident(..)
           -- ** Operator Fixity
         , Assoc(..), Infixity(..), infix_, infixl_, infixr_
           -- ** Base Functor
         , PortrayalF(..)
           -- * Class
         , Portray(..)
           -- ** Via Generic
         , GPortray(..), GPortrayProduct(..)
           -- ** Via Show, Integral, and Real
         , PortrayIntLit(..), PortrayRatLit(..), ShowAtom(..)
           -- * Convenience
         , showAtom, strAtom, strQuot, strBinop
           -- * Miscellaneous
         , Fix(..), cata, portrayCallStack, portrayType
         ) where

import Data.Portray.Class
import Data.Portray.Portrayal
