module ETU.Setoids where

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

----------------------------------------------------------------------
-- Setoid of contexts modulo definitional equality
----------------------------------------------------------------------
Cxt : Setd

∣ Cxt ∣ = ∑[ Γ ∈ Cx ] (Ok Γ)
Cxt ∋ (Γ , _) ~ (Γ' , _) = ⊢ Γ ＝ Γ'
rfl Cxt (_ , q) = CxRefl q
sym Cxt = CxSymm
trs Cxt = CxTrans

----------------------------------------------------------------------
-- Displayed setoid of types modulo definitional equality
----------------------------------------------------------------------
Type : ℕ → Setd[ Cxt ]

∥ Type l ∥ (Γ , _) = ∑[ A ∈ Ty ] (Γ ⊢ A ⦂ l)
Type l ∋ (Γ , _ ) , A , _ ≈ _ , A' , _ =
  Γ ⊢ A ＝ A' ⦂ l
hrfl (Type _) _ (_ , q) = Refl q
hsym (Type _) p q = ＝⊢ (Symm q) (CxSymm p)
htrs (Type _) p _ q q' = Trans q (＝⊢ q' p)
coe (Type _) p (A , q) = (A , ＝⊢ q (CxSymm p))
coh (Type _) _ (_ , q) = Refl q

----------------------------------------------------------------------
-- Displayed setoid of terms modulo definitional equality
----------------------------------------------------------------------
Term : (l : ℕ) → Setd[ Cxt ⋉ Type l ]

∥ Term l ∥ ((Γ , _) , A , _) = ∑[ a ∈ Tm ] (Γ ⊢ a ∶[ l ] A)
Term l ∋ ((Γ , _) , A , _) , a , _ ≈ _ , a' , _ =
  Γ ⊢ a ＝ a' ∶[ l ] A
hrfl (Term _) _ (_ , q) = Refl q
hsym (Term _) (p , p') q =
  ＝⊢ (＝conv (Symm q) p') (CxSymm p)
htrs (Term _) (p₁ , p₁') _ q₁ q₂ =
  Trans q₁ (＝conv (＝⊢ q₂ p₁) (Symm p₁'))
coe (Term _) (p , p') (a , q) =
  (a , ＝⊢ (⊢conv q p') (CxSymm p))
coh (Term _) _ (_ , q) = Refl q

----------------------------------------------------------------------
-- Displayed setoid of substitutions modulo definitional equality
----------------------------------------------------------------------
-- TO DO
-- Subst : Setd[ Cxt ⊗ Cxt ]

-- ∥ Subst ∥ ((Γ' , _) , Γ , _) = ∑[ σ ∈ Sb ] (Γ' ⊢ˢ σ ∶ Γ)
-- Subst ∋ ((Γ' , _) , Γ , _) , σ , _ ≈ _ , σ' , _ =
--   Γ' ⊢ˢ σ ＝ σ' ∶ Γ
-- hrfl Subst _ (_ , q) = sb＝Refl q
-- hsym Subst (p , p') q = {!sb＝Symm q!}
-- htrs Subst = {!!}
-- coe Subst = {!!}
-- coh Subst = {!!}
