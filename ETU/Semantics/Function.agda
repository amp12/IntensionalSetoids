module ETU.Semantics.Function where

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

{- Functional semantics derived from the relational semantics. -}

----------------------------------------------------------------------
-- Semantics of contexts
----------------------------------------------------------------------
infix 3 ⟦_cx⟧
⟦_cx⟧ :
  (Γ : Cx)
  (_ : Ok Γ)
  → ---------
  ∣ 𝒞 ∣

⟦ Γ cx⟧ q = π₁ (tot⟦cx⟧ q)

-- Proof irrelevance
⟦cx⟧irrel :
  {Γ : Cx}
  (p p' : Ok Γ)
  → ------------------------
  𝒞 ∋ ⟦ Γ cx⟧ p ~ ⟦ Γ cx⟧ p'

⟦cx⟧irrel p p' = sv⟦cx⟧
  (π₂ (tot⟦cx⟧ p))
  (π₂ (tot⟦cx⟧ p'))

-- Soundness
⟦cx⟧sound :
  {Γ Γ' : Cx}
  (p : Ok Γ)
  (p' : Ok Γ')
  (_ : ⊢ Γ ＝ Γ')
  → -------------------------
  𝒞 ∋ ⟦ Γ cx⟧ p ~ ⟦ Γ' cx⟧ p'

⟦cx⟧sound p p' q =
  let
    (C , q) = tot⟦cx⟧ p
    (C' , q') = tot⟦cx⟧ p'
  in {!!}




-- ----------------------------------------------------------------------
-- -- Semantics of types
-- ----------------------------------------------------------------------
-- infix 3 ty_⟦_⊢_⟧
-- ty_⟦_⊢_⟧ :
--   (l : ℕ)
--   (Γ : Cx)
--   (A : Ty)
--   (p : Ok Γ)
--   (_ : Γ ⊢ A ⦂ l)
--   → -------------------
--   ∥ ℱ𝒶𝓂 l ∥ (cx⟦ Γ ⟧ p)

-- ty l ⟦ Γ ⊢ A ⟧ p q = π₁ (tot⟦ty⟧' q (π₂ (tot⟦cx⟧ p)))

-- -- Proof irrelevance
-- ty⟦⟧irrel :
--   {l : ℕ}
--   {Γ : Cx}
--   {A : Ty}
--   (p p' : Ok Γ)
--   (q q' : Γ ⊢ A ⦂ l)
--   → ----------------------------------
--   ℱ𝒶𝓂 l ∋
--   cx⟦ Γ ⟧ p  , ty l ⟦ Γ ⊢ A ⟧ p  q  ≈
--   cx⟦ Γ ⟧ p' , ty l ⟦ Γ ⊢ A ⟧ p' q'

-- ty⟦⟧irrel p p' q q' =
--   let (_ , p₀)  = tot⟦cx⟧ p
--       (_ , q₀)  = tot⟦ty⟧' q p₀
--       (_ , p₀') = tot⟦cx⟧ p'
--       (_ , q₀') = tot⟦ty⟧' q' p₀'
--   in π₂ (sv⟦ty⟧ q₀ q₀')

-- ----------------------------------------------------------------------
-- -- Semantics of terms
-- ----------------------------------------------------------------------
-- infix 3 tm⟦_⊢_⟧
-- tm⟦_⊢_⟧ :
--   {l : ℕ}
--   {A : Ty}
--   (Γ : Cx)
--   (a : Tm)
--   (p : Ok Γ)
--   (q : Γ ⊢ A ⦂ l)
--   (_ : Γ ⊢ a ∶ A ⦂ l)
--   → ----------------------------------------
--   ∥ ℰ𝓁𝓉 l ∥ (cx⟦ Γ ⟧ p , ty l ⟦ Γ ⊢ A ⟧ p q)

-- tm⟦ Γ ⊢ a ⟧ p q r =
--   π₁ (tot⟦tm⟧' r (π₂ (tot⟦ty⟧' q (π₂ (tot⟦cx⟧ p)))))

-- -- Proof irrelevance
-- tm⟦⟧irrel :
--   {l : ℕ}
--   {A : Ty}
--   {Γ : Cx}
--   {a : Tm}
--   (p p' : Ok Γ)
--   (q q' : Γ ⊢ A ⦂ l)
--   (r r' : Γ ⊢ a ∶ A ⦂ l)

--   → -----------------------------------------------------------
--   ℰ𝓁𝓉 l ∋
--   (cx⟦ Γ ⟧ p  , ty l ⟦ Γ ⊢ A ⟧ p  q ) , tm⟦ Γ ⊢ a ⟧ p  q  r  ≈
--   (cx⟦ Γ ⟧ p' , ty l ⟦ Γ ⊢ A ⟧ p' q') , tm⟦ Γ ⊢ a ⟧ p' q' r'

-- tm⟦⟧irrel p p' q q' r r' =
--   let
--     (_ , p₀) = tot⟦cx⟧ p
--     (_ , q₀) = tot⟦ty⟧' q p₀
--     (_ , r₀) = tot⟦tm⟧' r q₀
--     (_ , p₀') = tot⟦cx⟧ p'
--     (_ , q₀') = tot⟦ty⟧' q' p₀'
--     (_ , r₀') = tot⟦tm⟧' r' q₀'
--   in π₂ (π₂ (sv⟦tm⟧ r₀ r₀'))

-- -- Soundness
-- sound :
--   {l : ℕ}
--   {Γ : Cx}
--   {A : Ty}
--   {a a' : Tm}
--   (p : Ok Γ)
--   (q : Γ ⊢ A ⦂ l)
--   (r : Γ ⊢ a ∶ A ⦂ l)
--   (r' : Γ ⊢ a' ∶ A ⦂ l)
--   (_ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
--   → -------------------------------------------
--   ℰ𝓁𝓉 l ′ (cx⟦ Γ ⟧ p  , ty l ⟦ Γ ⊢ A ⟧ p  q ) ∋
--   tm⟦ Γ ⊢ a ⟧ p  q r ~ tm⟦ Γ ⊢ a' ⟧ p q r'

-- sound{l} p q r r' s =
--   let
--     (C , p₀) = tot⟦cx⟧ p
--     (T , q₀) = tot⟦ty⟧' q p₀
--     (t , r₀) = tot⟦tm⟧' r q₀
--     (t' , r₀') = tot⟦tm⟧' r' q₀
--     (t'' , r₁ , r₁') = conv⟦tm⟧' s q₀
--   in trs (ℰ𝓁𝓉 l ′ (C , T))
--     {t}
--     {t''}
--     {t'}
--     (π₂ (π₂ (sv⟦tm⟧ r₀ r₁)))
--     (π₂ (π₂ (sv⟦tm⟧ r₁' r₀')))
