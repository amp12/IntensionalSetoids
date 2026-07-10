module ETU.Semantics where

{- Semantics of ETU using intensional setoids -}

-- The graphs of the semantic functions for terms, variables, types
-- and contexts
open import ETU.Semantics.Relation public

-- The semantics of terms-in-context contains that for contexts
open import ETU.Semantics.Ok public

-- The semantic relations are well-scoped
open import ETU.Semantics.WellScoped public

-- The semantic relations are single-valued
open import ETU.Semantics.SingleValued public

-- Semantics of weakening
open import ETU.Semantics.Weakening public

-- Semantics of substitution
open import ETU.Semantics.Substitution public

-- "Exists fresh" properties of the semantic relations
open import ETU.Semantics.ExistsFresh

-- The semantic relations are total
open import ETU.Semantics.Total public

-- Functional semantics of ETU contexts, types and terms, together
-- with proofs of soundness and proof-irrelevance with respect to the
-- valid judgements of ETU
open import ETU.Semantics.Soundness public

-- Consistency of extensional type theory relative to intensional
-- Martin-Löf Type Theory with inductive-recursive definitions (safe
-- Agda)
open import ETU.Semantics.Consistency public
