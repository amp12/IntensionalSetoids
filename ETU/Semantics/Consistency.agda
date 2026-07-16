module ETU.Semantics.Consistency where

open import Prelude
open import Setoid
open import WSLN

open import ETU.Syntax
open import ETU.Judgement
open import ETU.Rules
open import ETU.Ok
open import ETU.WellScoped
open import ETU.Weakening
open import ETU.Substitution
open import ETU.Admissible
open import ETU.ExistsFresh
open import ETU.Uniqueness

open import ETU.Semantics.Relation
open import ETU.Semantics.Ok
open import ETU.Semantics.WellScoped
open import ETU.Semantics.SingleValued
open import ETU.Semantics.Weakening
open import ETU.Semantics.Substitution
open import ETU.Semantics.Total

{- Consistency of extensional type theory relative to intensional
Martin-Löf Type Theory with inductive-recursive definitions (safe
Agda) -}

consistent : ¬(∃[ a ] (◇ ⊢ a ∶ 𝐄𝐦𝐩 ⦂ 0))

consistent (_ , q) =
  let (t , _) = tot⟦tm⟧' q (⟦𝐄𝐦𝐩⟧ ⟦◇⟧)
  in Øelim (∥ t ∥ tt)
