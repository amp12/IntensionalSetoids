module Semantics where

{- Semantics of ETU using intensional setoids -}

-- The setoid-enriched category-with-familes given by the universes
open import Semantics.CwF public

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

-- Functional semantics of ETU contexts, types and terms, together
-- with proofs of soundness and proof-irrelevance with respect to the
-- valid judgements of ETU
open import Semantics.Function public

-- Consistency of extensional type theory relative to intensional
-- Martin-Löf Type Theory with inductive-recursive definitions (safe
-- Agda)
open import Semantics.Consistency public
