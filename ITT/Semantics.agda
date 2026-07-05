module ITT.Semantics where

{- Semantics of ITT using intensional setoids -}

-- The graphs of the semantic functions for terms, variables, types
-- and contexts
open import ITT.Semantics.Relation public

-- The semantics of terms-in-context contains that for contexts
open import ITT.Semantics.Ok public

-- The semantic relations are well-scoped
open import ITT.Semantics.WellScoped public

-- The semantic relations are single-valued
open import ITT.Semantics.SingleValued public

-- Semantics of weakening
open import ITT.Semantics.Weakening public

-- Semantics of substitution
open import ITT.Semantics.Substitution public

-- "Exists fresh" properties of the semantic relations
open import ITT.Semantics.ExistsFresh

-- The semantic relations are total
open import ITT.Semantics.Total public

-- Functional semantics of ITT contexts, types and terms.  Proof that
-- they are proof-irrelevant and sound for the provable judgements of
-- ITT
open import ITT.Semantics.Soundness public
