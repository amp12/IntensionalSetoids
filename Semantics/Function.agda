module Semantics.Function where

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

{- Functional semantics derived from the relational semantics. -}

----------------------------------------------------------------------
-- Semantics of contexts
----------------------------------------------------------------------
infix 3 ⟦_⟧
⟦_⟧ :
  (Γ : Cx)
  (_ : Ok Γ)
  → --------
  ∣ 𝒞 ∣

⟦ Γ ⟧ q = π₁ (tot⟦cx⟧ q)

-- Proof irrelevance
⟦cx⟧irrel :
  {Γ : Cx}
  (p p' : Ok Γ)
  → --------------------
  𝒞 ∋ ⟦ Γ ⟧ p ~ ⟦ Γ ⟧ p'

⟦cx⟧irrel p p' = sv⟦cx⟧
  (π₂ (tot⟦cx⟧ p))
  (π₂ (tot⟦cx⟧ p'))

----------------------------------------------------------------------
-- Semantics of types
----------------------------------------------------------------------
infix 3 ⟦_⊢[_]_⟧ty
⟦_⊢[_]_⟧ty :
  (Γ : Cx)
  (l : ℕ)
  (A : Ty)
  (p : Ok Γ)
  (_ : Γ ⊢ A ⦂ l)
  → -------------------
  ∥ ℱ𝒶𝓂 l ∥ (⟦ Γ ⟧ p)

⟦ Γ ⊢[ l ] A ⟧ty p q = π₁ (tot⟦ty⟧' q (π₂ (tot⟦cx⟧ p)))

-- Proof irrelevance
⟦ty⟧irrel :
  {l : ℕ}
  {Γ : Cx}
  {A : Ty}
  (p p' : Ok Γ)
  (q q' : Γ ⊢ A ⦂ l)
  → -----------------------------------
  ℱ𝒶𝓂 l ∋
  ⟦ Γ ⟧ p  , ⟦ Γ ⊢[ l ] A ⟧ty p  q  ≈
  ⟦ Γ ⟧ p' , ⟦ Γ ⊢[ l ] A ⟧ty p' q'

⟦ty⟧irrel p p' q q' =
  let (_ , p₀)  = tot⟦cx⟧ p
      (_ , q₀)  = tot⟦ty⟧' q p₀
      (_ , p₀') = tot⟦cx⟧ p'
      (_ , q₀') = tot⟦ty⟧' q' p₀'
  in π₂ (sv⟦ty⟧ q₀ q₀')

----------------------------------------------------------------------
-- Semantics of terms
----------------------------------------------------------------------
infix 3 ⟦_⊢[_]_⟧tm
⟦_⊢[_]_⟧tm :
  (Γ : Cx)
  (l : ℕ)
  (a : Tm)
  (p : Ok Γ)
  {A : Ty}
  (q : Γ ⊢ A ⦂ l)
  (_ : Γ ⊢ a ∶ A ⦂ l)
  → -------------------------------------------
  ∥ ℰ𝓁ℯ𝓂 l ∥ (⟦ Γ ⟧ p , ⟦ Γ ⊢[ l ] A ⟧ty p q)

⟦ Γ ⊢[ l ] a ⟧tm p q r =
  π₁ (tot⟦tm⟧' r (π₂ (tot⟦ty⟧' q (π₂ (tot⟦cx⟧ p)))))

-- Proof irrelevance
⟦tm⟧irrel :
  {l : ℕ}
  {A : Ty}
  {Γ : Cx}
  {a : Tm}
  (p p' : Ok Γ)
  (q q' : Γ ⊢ A ⦂ l)
  (r r' : Γ ⊢ a ∶ A ⦂ l)
  → -----------------------------------------------------------------
  ℰ𝓁ℯ𝓂 l ∋
  (⟦ Γ ⟧ p  , ⟦ Γ ⊢[ l ] A ⟧ty p  q ) , ⟦ Γ ⊢[ l ] a ⟧tm p  q  r  ≈
  (⟦ Γ ⟧ p' , ⟦ Γ ⊢[ l ] A ⟧ty p' q') , ⟦ Γ ⊢[ l ] a ⟧tm p' q' r'

⟦tm⟧irrel p p' q q' r r' =
  let
    (_ , p₀) = tot⟦cx⟧ p
    (_ , q₀) = tot⟦ty⟧' q p₀
    (_ , r₀) = tot⟦tm⟧' r q₀
    (_ , p₀') = tot⟦cx⟧ p'
    (_ , q₀') = tot⟦ty⟧' q' p₀'
    (_ , r₀') = tot⟦tm⟧' r' q₀'
  in π₂ (sv⟦tm⟧ r₀ r₀')

-- Soundness
sound :
  {l : ℕ}
  {Γ : Cx}
  {A : Ty}
  {a a' : Tm}
  (p : Ok Γ)
  (q : Γ ⊢ A ⦂ l)
  (r : Γ ⊢ a ∶ A ⦂ l)
  (r' : Γ ⊢ a' ∶ A ⦂ l)
  (_ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
  → ------------------------------------------------
  ℰ𝓁ℯ𝓂 l ′ (⟦ Γ ⟧ p  , ⟦ Γ ⊢[ l ] A ⟧ty p  q ) ∋
  ⟦ Γ ⊢[ l ] a ⟧tm p  q r ~ ⟦ Γ ⊢[ l ] a' ⟧tm p q r'

sound{l} p q r r' s =
  let
    (C , p₀) = tot⟦cx⟧ p
    (T , q₀) = tot⟦ty⟧' q p₀
    (t , r₀) = tot⟦tm⟧' r q₀
    (t' , r₀') = tot⟦tm⟧' r' q₀
    (t'' , r₁ , r₁') = conv⟦tm⟧' s q₀
  in trs (ℰ𝓁ℯ𝓂 l ′ (C , T))
    {t}
    {t''}
    {t'}
    (π₂ (sv⟦tm⟧ r₀ r₁))
    (π₂ (sv⟦tm⟧ r₁' r₀'))
