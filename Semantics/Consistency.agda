module Semantics.Consistency where

open import Prelude
open import Setoid
open import WSLN
open import ETU

open import Semantics.CwF
open import Semantics.Relation
open import Semantics.Ok
open import Semantics.WellScoped
open import Semantics.SingleValued
open import Semantics.Weakening
open import Semantics.Substitution
open import Semantics.Total
open import Semantics.Function

{- Consistency of extensional type theory relative to intensional
Martin-Löf Type Theory with inductive-recursive definitions (safe
Agda) -}

consistent : ¬(∃[ a ] (◇ ⊢ a ∶[ 0 ] 𝐄𝐦𝐩))

consistent (a , q) = ∥ ⟦ ◇ ⊢[ 0 ] a ⟧tm ok◇ (⊢𝐄𝐦𝐩 ok◇) q ∥ tt
