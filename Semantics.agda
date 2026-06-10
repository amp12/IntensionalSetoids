module Semantics where

{- Semantics of ETT using intensional setoids -}

-- The graphs of the semantic functions for terms, variables, types
-- and contexts
open import Semantics.Relation public

-- The semantics of terms-in-context contains that for contexts
open import Semantics.Ok public

-- The semantic relations are well-scoped
open import Semantics.WellScoped public

-- The semantic relations are single-valued
open import Semantics.SingleValued public

-- Semantics of weakening
open import Semantics.Weakening public

-- Semantics of substitution
open import Semantics.Substitution public

-- "Exists fresh" properties of the semantic relations
open import Semantics.ExistsFresh

-- The semantic relations are total
open import Semantics.Total public

-- Functional semantics of ETT contexts, types and terms.  Proof that
-- they are proof-irrelevant and sound for the provable judgements of
-- ETT
open import Semantics.Soundness public
