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

{- Consistency of extensional type theory relative to intensional
Martin-Löf Type Theory with inductive-recursive definitions (safe
Agda) -}

consistent : ¬(∃[ a ] (◇ ⊢ a ∶[ 0 ] 𝐄𝐦𝐩))

consistent (_ , q) =
  let (t , _) = tot⟦tm⟧' q (⟦𝐄𝐦𝐩⟧ ⟦◇⟧)
  in Øelim (∥ t ∥ tt)
