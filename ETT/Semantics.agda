module ETT.Semantics where

{- Semantics of ETT using intensional setoids -}

-- The graphs of the semantic functions for terms, variables, types
-- and contexts
open import ETT.Semantics.Relation public

-- The semantics of terms-in-context contains that for contexts
open import ETT.Semantics.Ok public

-- The semantic relations are well-scoped
open import ETT.Semantics.WellScoped public

-- The semantic relations are single-valued
open import ETT.Semantics.SingleValued public

-- Semantics of weakening
open import ETT.Semantics.Weakening public

-- Semantics of substitution
open import ETT.Semantics.Substitution public

-- "Exists fresh" properties of the semantic relations
open import ETT.Semantics.ExistsFresh

-- The semantic relations are total
open import ETT.Semantics.Total public

-- Functional semantics of ETT contexts, types and terms, together
-- with a proof of soundness and proof-irrelevance for the valid
-- judgements of ETT
open import ETT.Semantics.Soundness public
