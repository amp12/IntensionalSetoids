module Setoid.CwF where

open import Prelude

open import Setoid.Definition
open import Setoid.Universes
open import Setoid.Lift
open import Setoid.PiType
open import Setoid.EqualityType
open import Setoid.NatType

{- A setoid enriched category-with-families whose objects are semantic
contexts (elements of the universe 𝒰ω). -}

----------------------------------------------------------------------
-- Objects are given by universe 𝒰ω
----------------------------------------------------------------------

----------------------------------------------------------------------
-- Morphisms
----------------------------------------------------------------------
record Hom (C D : Uω) : Set where
  constructor mkHom
  infix 8 ∣_∣
  field
    ∣_∣ : Elω C → Elω D
    cng :
      (c c' : Elω C)
      (_ : C ⸴ c ≈ω C ⸴ c')
      → ---------------------
      D ⸴ ∣_∣ c ≈ω D ⸴ ∣_∣ c'

open Hom public

ℋℴ𝓂 : Setd[ 𝒰ω ⊗ 𝒰ω ]

∥ ℋℴ𝓂 ∥ (C , D) = Hom C D
ℋℴ𝓂 ∋ (C , D) ⸴ f ≈ (C' , D') ⸴ f' =
  (c : Elω C)
  (c' : Elω C')
  (_ : C ⸴ c ≈ω C' ⸴ c')
  → ---------------------------
  D ⸴ ∣ f ∣ c ≈ω D' ⸴ ∣ f' ∣ c'
hrfl ℋℴ𝓂 (C , D) f _ _ e = cng f _ _ e
hsym ℋℴ𝓂 (e , e') f c c' e'' =
  hsymω e' (f c' c (hsymω (symω e) e''))
htrs ℋℴ𝓂 (e₁ , e₁') (e₂ , e₂') f₁ f₂ c c' e =
  htrsω e₁' e₂'
    (f₁ c (coeω e₁ c) (cohω e₁ c))
    (f₂ (coeω e₁ c) c'
      ((htrsω (symω e₁) (trsω e₁ e₂) (hsymω e₁ (cohω e₁ c)) e)))
∣ coe ℋℴ𝓂 (e₁ , e₂) f ∣ c = coeω e₂ (∣ f ∣ (coeω (symω e₁) c))
cng (coe ℋℴ𝓂 (e₁ , e₂) f) c c' e =  htrsω (symω e₂) e₂
  (hsymω e₂ (cohω e₂ (∣ f ∣(coeω (symω e₁) c))))
  (htrsω (rflω _) e₂
    (cng f _ _ (htrsω e₁ (symω e₁)
      (hsymω (symω e₁) (cohω (symω e₁) c))
      (htrsω (rflω _) (symω e₁) e (cohω (symω e₁) c'))))
    (cohω e₂ (∣ f ∣(coeω (symω e₁) c'))))
coh ℋℴ𝓂 (e₁ , e₂) f c c' e = htrsω (rflω _) e₂
  (cng f _ _ (htrsω e₁ (symω e₁) e (cohω (symω e₁) c')))
  (cohω e₂ (∣ f ∣(coeω (symω e₁) c')))

-- Identity morphism
instance
  HomIdentity : ∀{C} → Identity (Hom C C)
  ∣ id ⦃ HomIdentity ⦄ ∣ x = x
  cng (id ⦃ HomIdentity ⦄) _ _ = id

-- Composition of morphisms
instance
  HomComp : ∀{C D E} →
    Composition (Hom D E) (Hom C D) (Hom C E)
  ∣ _∘_ ⦃ HomComp ⦄ g f ∣ x = ∣ g ∣ (∣ f ∣ x)
  cng (_∘_ ⦃ HomComp ⦄ g f) _ _ = cng g _ _ ∘ cng f _ _

compCng :
  {C C' D D' E E' : Uω}
  {f : Hom C D}
  {f' : Hom C' D'}
  {g : Hom D E}
  {g' : Hom D' E'}
  (_ : ℋℴ𝓂 ∋ (C , D) ⸴ f ≈ (C' , D') ⸴ f')
  (_ : ℋℴ𝓂 ∋ (D , E) ⸴ g ≈ (D' , E') ⸴ g')
  → ---------------------------------------------
  ℋℴ𝓂 ∋ (C , E) ⸴ (g ∘ f) ≈ (C' , E') ⸴ (g' ∘ f')

compCng {f = f}{f'} u v c c' w = v (∣ f ∣ c) (∣ f' ∣ c') (u c c' w)

-- Terminal morphism
unit : (C : Uω) → Hom C Unit

∣ unit C ∣ _ = tt
cng (unit C) _ _ _ = tt

----------------------------------------------------------------------
-- Families and their elements
----------------------------------------------------------------------

{- Since we wish to ensure that, up to definitional equality, families
are elements of universes, we begin with the definition of elements
and then define families in terms of them. The use of a record type
rather than a Σ-type helps with inferring universe levels. -}

record Elt₁
  (n : ℕ)
  (C : Uω)
  (X : Elω C → U n)
  -- The next argument is not used, but including it enables the
  -- element re-indexing function *ω to only depend implicitly upon
  -- its family argument
  (q : ∀ c c' → C ⸴ c ≈ω C ⸴ c' → 𝒰 n ∋ X c ~ X c')
  : -----------------------------------------------
  Set
  where
  constructor mkElt₁
  infix 8 ∥_∥
  field
    ∥_∥ : (c : Elω C) → El n (X c)
    hcng :
      (c c' : Elω C)
      (_ : C ⸴ c ≈ω C ⸴ c')
      → --------------------------------
      ℰ𝓁 n ∋ X c ⸴ ∥_∥ c ≈ X c' ⸴ ∥_∥ c'

open Elt₁ public

-- Families
Fam : ℕ → Uω → Set
Fam n C =
  -- we rely on the fact that El (1+ n) Univ ≡ U l
  Elt₁ (1+ n) C (λ _ → Univ) (λ _ _ _ → rfl (𝒰 (1+ n)) Univ)

ℱ𝒶𝓂 : ℕ → Setd[ 𝒰ω ]
∥ ℱ𝒶𝓂 n ∥ = Fam n
ℱ𝒶𝓂 n ∋ C ⸴ T ≈ C' ⸴ T' =
  ∀ c c' → (C ⸴ c ≈ω C' ⸴ c') → 𝒰 n ∋ ∥ T ∥ c ~ ∥ T' ∥ c'
hrfl (ℱ𝒶𝓂 n) C T = hcng T
hsym (ℱ𝒶𝓂 n) e f c c' e' =
  sym (𝒰 n) (f c' c (hsymω (symω e) e'))
htrs (ℱ𝒶𝓂 n) e₁ e₂ f₁ f₂ c c'' e = trs (𝒰 n)
  (f₁ c (coeω e₁ c) (cohω e₁ c))
  (f₂ (coeω e₁ c) c'' (htrsω (symω e₁) (trsω e₁ e₂)
    (hsymω e₁ (cohω e₁ c)) e))
∥ coe (ℱ𝒶𝓂 n) e T ∥ c = ∥ T ∥ (coeω (symω e) c)
hcng (coe (ℱ𝒶𝓂 n) e T) c c' e' =
  hcng T _ _ (htrsω e (symω e)
    (hsymω (symω e) (cohω (symω e) c))
    (htrsω (rflω _) (symω e) e' (cohω (symω e) c')))
coh (ℱ𝒶𝓂 n) e T c c' e' =
  hcng T _ _ (htrsω e (symω e) e' (cohω (symω e) c'))

-- Elements of families
Elt : (n : ℕ)(C : Uω) → Fam n C → Set
Elt n C T = Elt₁ n C (∥_∥ T) (hcng T)

ℰ𝓁𝓉 : (n : ℕ) → Setd[ 𝒰ω ⋉ ℱ𝒶𝓂 n ]
∥ ℰ𝓁𝓉 n ∥ (C , T) = Elt n C T
ℰ𝓁𝓉 n ∋ (C , T) ⸴ t ≈ (C' , T') ⸴ t' =
  (c : Elω C)
  (c' : Elω C')
  (_ : C ⸴ c ≈ω C' ⸴ c')
  → ----------------------------------------------
  ℰ𝓁 n ∋ ∥ T ∥ c ⸴ ∥ t ∥ c ≈ ∥ T' ∥ c' ⸴ ∥ t' ∥ c'
hrfl (ℰ𝓁𝓉 n) _ T _ _ e = hcng T _ _ e
hsym (ℰ𝓁𝓉 n) (e , f) g c c' e' = hsym (ℰ𝓁 n)
  (f c' c (hsymω (symω e) e'))
  (g c' c (hsymω (symω e) e'))
htrs (ℰ𝓁𝓉 n) (e₁ , f₁) (e₂ , f₂) g₁ g₂ c c'' e =
  let
    c'  = coeω e₁ c
    e'  = cohω e₁ c
    e₁' = symω e₁
  in htrs (ℰ𝓁 n)
    (f₁ c c' e')
    (f₂ c' c'' (htrsω e₁' (trsω e₁ e₂) (hsymω e₁ e') e))
    (g₁ c c' e')
    (g₂ c' c'' (htrsω e₁' (trsω e₁ e₂) (hsymω e₁ e') e))
∥ coe (ℰ𝓁𝓉 n) (e , f) t ∥ c' =
  let
    c  = coeω (symω e) c'
    e' = cohω (symω e) c'
  in
  coe (ℰ𝓁 n) (f c c' (hsymω (symω e) e')) (∥ t ∥ c)
hcng (coe (ℰ𝓁𝓉 n) {y = _ , T'} (e , f) t) c₁ c₂ e' =
  let
    c₁'  = coeω (symω e) c₁
    e₁'  = cohω (symω e) c₁
    c₂'  = coeω (symω e) c₂
    e₂'  = cohω (symω e) c₂
    e₁'' = f c₁' c₁ (hsymω (symω e) e₁')
    e₂'' = f c₂' c₂ (hsymω (symω e) e₂')
  in  htrs (ℰ𝓁 n)
    (sym (𝒰 n) e₁'')
    (f c₁' c₂ (htrsω e (rflω _) (hsymω (symω e) e₁') e'))
    (hsym (ℰ𝓁 n) e₁'' (coh (ℰ𝓁 n) e₁'' (∥ t ∥ c₁')))
    (htrs (ℰ𝓁 n)
    (trs (𝒰 n) e₁'' (trs (𝒰 n) (hcng T' _ _ e') (sym (𝒰 n) e₂'')))
      e₂''
      (hcng t _ _ (htrsω e (symω e) (hsymω (symω e) e₁')
        (htrsω (rflω _) (symω e) e' e₂')))
      (coh (ℰ𝓁 n) e₂'' (∥ t ∥ c₂')))
coh (ℰ𝓁𝓉 n) {_ , T'} (e , f) t c c' e' =
  let
    c₁  = coeω (symω e) c'
    e₁' = cohω (symω e) c'
  in htrs (ℰ𝓁 n)
    (hcng T' _ _ (htrsω e (symω e) e' e₁'))
    (f c₁ c' (hsymω (symω e) e₁'))
    (hcng t _ _ (htrsω e (symω e) e' e₁'))
    (coh (ℰ𝓁 n) (f c₁ c' (hsymω (symω e) e₁')) (∥ t ∥ c₁))

----------------------------------------------------------------------
-- Re-indexing
----------------------------------------------------------------------
infixr 6 _*ₒ_
_*ₒ_ :
  {n : ℕ}
  {C D : Uω}
  (f : Hom D C)
  (T : Fam n C)
  → -----------
  Fam n D

∥ f *ₒ T ∥ d = ∥ T ∥ (∣ f ∣ d)
hcng (f *ₒ T) d d' e = hcng T (∣ f ∣ d) (∣ f ∣ d') (cng f d d' e)

-- Notation
instance
  Apply*ₒ : ∀{n C D} → Apply (Hom D C) (Fam n C) (Fam n D)
  _*_ ⦃ Apply*ₒ ⦄ = _*ₒ_

infixr 6 _*₁_
_*₁_ :
  {n : ℕ}
  {C D : Uω}
  {T : Fam n C}
  (f : Hom D C)
  (t : Elt n C T)
  → -------------
  Elt n D (f * T)

∥ f *₁ t ∥ d = ∥ t ∥ (∣ f ∣ d)
hcng (f *₁ t) _ _ e = hcng t _ _ (cng f _ _ e)

cng* :
  {n : ℕ}
  {C C' D D' : Uω}
  {T : Fam n C}
  {T' : Fam n C'}
  (f : Hom D C)
  (f' : Hom D' C')
  (_ : ℋℴ𝓂 ∋ (D , C) ⸴ f ≈ (D' , C') ⸴ f')
  (_ : ℱ𝒶𝓂 n ∋ C ⸴ T ≈ C' ⸴ T')
  → --------------------------------------
  ℱ𝒶𝓂 n ∋ D ⸴ f * T ≈ D' ⸴ f' * T'

cng* f f' e e' c c' u = e' (∣ f ∣ c) (∣ f' ∣ c') (e c c' u)

cng*₁ :
  {n : ℕ}
  {C C' D D' : Uω}
  {T : Fam n C}
  {T' : Fam n C'}
  {t : Elt n C T}
  {t' : Elt n C' T'}
  (f : Hom D C)
  (f' : Hom D' C')
  (_ : ℋℴ𝓂 ∋ (D , C) ⸴ f ≈ (D' , C') ⸴ f')
  (_ : ℰ𝓁𝓉 n ∋ (C , T) ⸴ t ≈ (C' , T') ⸴ t')
  → -------------------------------------------------------
  ℰ𝓁𝓉 n ∋ (D , f * T) ⸴ f *₁ t  ≈ (D' , f' * T') ⸴ f' *₁ t'

cng*₁ f f' e e' c c' u = e' (∣ f ∣ c) (∣ f' ∣ c') (e c c' u)

----------------------------------------------------------------------
-- Universes of types
----------------------------------------------------------------------
𝒰𝓃𝒾𝓋 :
  (n : ℕ)
  {C : Uω}
  → ----------
  Fam (1+ n) C

∥ 𝒰𝓃𝒾𝓋 _ ∥ _  = Univ
hcng (𝒰𝓃𝒾𝓋 n) _ _ _ = rfl (𝒰 (1+ n)) Univ

-- Families are elements (of universes) up to definitional equality:
fam-as-elt :
  {n : ℕ}
  {C : Uω}
  → -----------------------------
  Fam n C ≡ Elt (1+ n) C (𝒰𝓃𝒾𝓋 n)

fam-as-elt = refl

----------------------------------------------------------------------
-- Semantic context comprehension
----------------------------------------------------------------------
infixl 8 _⋉[_]_
_⋉[_]_ :
  (C : Uω)
  (n : ℕ)
  (X : Fam n C)
  → -----------
  Uω

C ⋉[ n ] (mkElt₁ X q) = Sigma C n X q

𝓅 :
  {n : ℕ}
  {C : Uω}
  (T : Fam n C)
  → ----------------
  Hom (C ⋉[ n ] T) C

∣ 𝓅 _ ∣ (c , _) = c
cng (𝓅 _) _ _ (e , _) = e

𝓆 :
  {n : ℕ}
  {C : Uω}
  (T : Fam n C)
  → ---------------------------
  Elt n (C ⋉[ n ] T) (𝓅 T * T)

∥ 𝓆 _ ∥ (c , t) = t
hcng (𝓆 _) _ _ (_ , e , e')
  with refl ← ! ⦃ !≡ ⦄ e refl = e'

𝒸ℴ𝓃𝓈 :
  {n : ℕ}
  {C D : Uω}
  {T : Fam n C}
  (f : Hom D C)
  (t : Elt n D (f * T))
  → -------------------
  Hom D (C ⋉[ n ] T)

∣ 𝒸ℴ𝓃𝓈 f t ∣ d = (∣ f ∣ d , ∥ t ∥ d)
cng (𝒸ℴ𝓃𝓈 f t) _ _ e =
  (cng f _ _ e , refl , hcng t _ _ e)

infixl 8 ⟪_⟫
⟪_⟫ :
  {n : ℕ}
  {C : Uω}
  {T : Fam n C}
  (t : Elt n C T)
  → ----------------
  Hom C (C ⋉[ n ] T)

⟪ t ⟫ = 𝒸ℴ𝓃𝓈 id t

infixl 8 _⋉′[_]_
_⋉′[_]_ :
  {C D : Uω}
  (f : Hom D C)
  (n : ℕ)
  (T : Fam n C)
  → ---------------------------------
  Hom (D ⋉[ n ] (f * T)) (C ⋉[ n ] T)

f ⋉′[ n ] T = 𝒸ℴ𝓃𝓈 (f ∘ 𝓅 (f * T)) (𝓆 (f * T))

infixl 8 ⟪_⸴_⟫
⟪_⸴_⟫ :
  {m n : ℕ}
  {C : Uω}
  {S : Fam m C}
  {T : Fam n (C ⋉[ m ] S)}
  (s : Elt m C S)
  (_ : Elt n C (⟪ s ⟫ * T))
  → -------------------------
  Hom C (C ⋉[ m ] S ⋉[ n ] T)

⟪ s ⸴ t ⟫ = 𝒸ℴ𝓃𝓈 ⟪ s ⟫ t

cong⋉[] :
  {C C' : Uω}
  (n : ℕ)
  {T : Fam n C}
  {T' : Fam n C'}
  (_ : 𝒰ω ∋ C ~ C')
  (_ : ℱ𝒶𝓂 n ∋ C ⸴ T ≈ C' ⸴ T')
  → -----------------------------
  𝒰ω ∋ C ⋉[ n ] T ~ C' ⋉[ n ] T'

cong⋉[] n e e' = (e , refl , λ c c' u → e' c c' u)

img⋉[] :
  {C : Uω}
  {n : ℕ}
  {T : Fam n C}
  (C'' : Uω)
  (_ : 𝒰ω ∋ C ⋉[ n ] T ~ C'')
  → ------------------------------
  ∑[ C' ∈ Uω ] ∑[ T' ∈ Fam n C' ]
  (C ~ω C')
  ∧
  (ℱ𝒶𝓂 n ∋ C ⸴ T ≈ C' ⸴ T')

img⋉[] (Sigma C n X q) (e , refl , e') = (C , mkElt₁ X q , e , e')

imgUnit :
  (C : Uω)
  (_ : 𝒰ω ∋ Unit ~ C)
  → -----------------
  Unit ≡ C

imgUnit Unit tt = refl

----------------------------------------------------------------------
-- Pi types
----------------------------------------------------------------------
𝒫𝒾 :
  {C : Uω}
  (m n : ℕ)
  (S : Fam m C)
  (_ : Fam n (C ⋉[ m ] S))
  → -----------------------
  Fam (max m n) C

∥ 𝒫𝒾 m n S T ∥ c = PI.ty (pi m n)
  (∥ S ∥ c)
  (λ c' → ∥ T ∥ (c , c'))
  (λ _ _ e → hcng T _ _ (hrflω _ c , refl , e))
hcng (𝒫𝒾 m n S T) x x' e = PI.tyCong (pi m n) _ _ _ _ _ _
  (hcng S _ _ e)
  (λ _ _ e' → hcng T _ _ (e , refl , e'))

cong𝒫𝒾 :
  {C C' : Uω}
  (m n : ℕ)
  {S : Fam m C}
  {S' : Fam m C'}
  {T : Fam n (C ⋉[ m ] S)}
  {T' : Fam n (C' ⋉[ m ] S')}
  (_ : ℱ𝒶𝓂 m ∋ C ⸴ S ≈ C' ⸴ S')
  (_ : ℱ𝒶𝓂 n ∋ C ⋉[ m ] S ⸴ T ≈ C' ⋉[ m ] S' ⸴ T')
  → ------------------------------------------------
  ℱ𝒶𝓂 (max m n) ∋ C ⸴ 𝒫𝒾 m n S T ≈ C' ⸴ 𝒫𝒾 m n S' T'

cong𝒫𝒾 m n e e' c c' u = PI.tyCong (pi m n) _ _ _ _ _ _
  (e c c' u)
  (λ y y' v → e' (c , y) (c' , y') (u , refl , v))

-- The 𝒫𝒾 operation is natural up to setoid equivalence
ntrl𝒫𝒾 :
  {D C : Uω}
  (m n : ℕ)
  (S : Fam m C)
  (T : Fam n (C ⋉[ m ] S))
  (f : Hom D C)
  → ------------------------------------
  ℱ𝒶𝓂 (max m n) ′ D ∋ f * (𝒫𝒾 m n S T) ~
    𝒫𝒾 m n (f * S) ((f ⋉′[ m ] S) * T)

ntrl𝒫𝒾 m n S T f _ _ e = PI.tyCong (pi m n) _ _ _ _ _ _
  (hcng S _ _ (cng f _ _ e))
  λ y y' e' →
    hcng T _ _ (cng f _ _ e , refl , e')

𝓁𝒶𝓂 :
  {C : Uω}
  (m n : ℕ)
  (S : Fam m C)
  {T : Fam n (C ⋉[ m ] S)}
  (t : Elt n (C ⋉[ m ] S) T)
  → --------------------------
  Elt (max m n) C (𝒫𝒾 m n S T)

∥ 𝓁𝒶𝓂 m n _ t ∥ c = PI.lam (pi m n) _ _ _
  (λ c' → ∥ t ∥ (c , c'))
  (λ _ _ e → hcng t _ _ (hrflω _ c , refl , e))
hcng (𝓁𝒶𝓂 m n _ t) c c' e =
  PI.lamCong (pi m n) _ _ _ _ _ _ _ _ _ _
  λ _ _ e' → hcng t _ _ (e , refl , e')

cong𝓁𝒶𝓂 :
  {C C' : Uω}
  (m n : ℕ)
  {S : Fam m C}
  {S' : Fam m C'}
  {T : Fam n (C ⋉[ m ] S)}
  {T' : Fam n (C' ⋉[ m ] S')}
  {t : Elt n (C ⋉[ m ] S) T}
  {t' : Elt n (C' ⋉[ m ] S') T'}
  (_ : ℰ𝓁𝓉 n ∋ (C ⋉[ m ] S , T) ⸴ t ≈ (C' ⋉[ m ] S' , T') ⸴ t')
  → -----------------------------------------------------------
  ℰ𝓁𝓉 (max m n) ∋
    (C , 𝒫𝒾 m n S T) ⸴ 𝓁𝒶𝓂 m n S t ≈
    (C' , 𝒫𝒾 m n S' T') ⸴ 𝓁𝒶𝓂 m n S' t'

cong𝓁𝒶𝓂 m n e c c' u =
  PI.lamCong (pi m n) _ _ _ _ _ _ _ _ _ _
  λ y y' v → e (c , y) (c' , y') (u , refl , v)

ntrl𝓁𝒶𝓂 :
  {D C : Uω}
  (m n : ℕ)
  {S : Fam m C}
  {T : Fam n (C ⋉[ m ] S)}
  (t : Elt n (C ⋉[ m ] S) T)
  (f : Hom D C)
  → --------------------------------------
  ℰ𝓁𝓉 (max m n) ∋
  (D , f * (𝒫𝒾 m n S T)) ⸴
  f *₁ 𝓁𝒶𝓂 m n S t
  ≈
  (D , 𝒫𝒾 m n (f * S) (f ⋉′[ m ] S * T)) ⸴
  𝓁𝒶𝓂 m n (f * S) (f ⋉′[ m ] S *₁ t)

ntrl𝓁𝒶𝓂 m n t f c c' e =
  PI.lamCong (pi m n) _ _ _ _ _ _ _ _ _ _
  λ y y' e' → hcng t _ _ (cng f _ _ e , refl , e')

𝒶𝓅𝓅 :
  {C : Uω}
  (m n : ℕ)
  (S : Fam m C)
  (T : Fam n (C ⋉[ m ] S))
  (_ : Elt (max m n) C (𝒫𝒾 m n S T))
  (s : Elt m C S)
  → --------------------------------
  Elt n C (⟪ s ⟫ * T)

∥ 𝒶𝓅𝓅 m n _ _ t s ∥ c =
  PI.app (pi m n) _ _ _ (∥ t ∥ c) (∥ s ∥ c)
hcng (𝒶𝓅𝓅 m n _ _ t s) x x' e =
  PI.appCong (pi m n) _ _ _ _ _ _ _ _ _ _
  (hcng t x x' e)
  (hcng s x x' e)

ntrl𝒶𝓅𝓅 :
  {D C : Uω}
  (m n : ℕ)
  (S : Fam m C)
  (T : Fam n (C ⋉[ m ] S))
  (t : Elt (max m n) C (𝒫𝒾 m n S T))
  (s : Elt m C S)
  (f : Hom D C)
  → ----------------------------------------
  ℰ𝓁𝓉 n ∋
  (D , f * ⟪ s ⟫ * T) ⸴ f *₁ 𝒶𝓅𝓅 m n S T t s
  ≈
  (D , ⟪ f *₁ s ⟫ * (f ⋉′[ m ] S) * T) ⸴
  𝒶𝓅𝓅 m n (f * S) (f ⋉′[ m ] S * T)
    (coe (ℰ𝓁𝓉 (max m n))
      (rflω D , ntrl𝒫𝒾 m n S T f) (f *₁ t))
    (f *₁ s)

ntrl𝒶𝓅𝓅 m n S T t s f c c' e =
  PI.appCong (pi m n) _ _ _ _ _ _ _ _ _ _
  (coh (ℰ𝓁𝓉 (max m n))
    {y = _ , 𝒫𝒾 m n (f * S) (f ⋉′[ m ] S * T)}
    (rflω _ , ntrl𝒫𝒾 m n S T f)
    (f *₁ t) c c' e)
  (hcng s (∣ f ∣ c) (∣ f ∣ c') (cng f c c' e))

𝒫𝒾𝒷ℯ𝓉𝒶 :
  {C : Uω}
  (m n : ℕ)
  (S : Fam m C)
  (T : Fam n (C ⋉[ m ] S))
  (t : Elt n (C ⋉[ m ] S) T)
  (s :  Elt m C S)
  → --------------------------------------
  ℰ𝓁𝓉 n ′ (C , ⟪ s ⟫ * T) ∋
  𝒶𝓅𝓅 m n S T (𝓁𝒶𝓂 m n S t) s ~ ⟪ s ⟫ *₁ t

𝒫𝒾𝒷ℯ𝓉𝒶{C} m n S T t s c _ e =  htrs (ℰ𝓁 n)
  (rfl (𝒰 n) (∥ ⟪ s ⟫ * T ∥ c))
  (hcng T _ _ (cng ⟪ s ⟫ _ _ e))
  (PI.beta (pi m n)
    (∥ S ∥ c)
    (λ x → ∥ T ∥ (c , x))
    (λ _ _ e' → hcng T _ _ (hrflω C c , refl , e'))
    (λ x → ∥ t ∥ (c , x))
    (λ _ _ e' → hcng t _ _ (hrflω C c , refl , e'))
    (∥ s ∥ c))
  (hcng t _ _ (cng ⟪ s ⟫ _ _ e))

module 𝒫𝒾ℰ𝓉𝒶
-- The fact that ntrl𝒫𝒾 is not a definitional equality complicates the
-- proof that the semantics is sound for eta conversion.
  (C : Uω)
  (m n : ℕ)
  (S : Fam m C)
  (T : Fam n (C ⋉[ m ] S))
  (t : Elt (max m n) C (𝒫𝒾 m n S T))
  where
  S' : Fam m (C ⋉[ m ] S)
  S' = 𝓅 S * S

  T' : Fam n (C ⋉[ m ] S ⋉[ m ] S')
  T' = (𝓅 S ⋉′[ m ] S) * T

  e : ℱ𝒶𝓂 n ′ (C ⋉[ m ] S) ∋ ⟪ 𝓆 S ⟫ * T' ~ T
  e = hcng T

  t' : Elt (max m n) (C ⋉[ m ] S) (𝒫𝒾 m n S' T')
  t' = coe (ℰ𝓁𝓉 (max m n))
    ((rflω (C ⋉[ m ] S) , ntrl𝒫𝒾 m n S T (𝓅 S)))
    (𝓅 S *₁ t)

  e' : ℰ𝓁𝓉 (max m n) ∋
    (C ⋉[ m ] S , 𝒫𝒾 m n S' T') ⸴ t' ≈
    (C ⋉[ m ] S , 𝓅 S *  𝒫𝒾 m n S T) ⸴ 𝓅 S *₁ t
  e' = coh⁻¹ (ℰ𝓁𝓉 (max m n))
    {C ⋉[ m ] S , 𝓅 S *  𝒫𝒾 m n S T}
    {C ⋉[ m ] S , 𝒫𝒾 m n S' T'}
    ((rflω (C ⋉[ m ] S) , ntrl𝒫𝒾 m n S T (𝓅 S)))
    (𝓅 S *₁ t)

  abstract
    etaPf : ℰ𝓁𝓉 (max m n) ∋
      (C , 𝒫𝒾 m n S (⟪ 𝓆 S ⟫ * T')) ⸴ 𝓁𝒶𝓂 m n S (𝒶𝓅𝓅 m n S' T' t' (𝓆 S))
      ≈ (C , 𝒫𝒾 m n S T) ⸴ t
    etaPf c c' e = htrs (ℰ𝓁 (max m n))
      (PI.tyCong (pi m n) _ _ _ _ _ _ (rfl (𝒰 m) (∥ S ∥ c))
        (λ x x' u → hcng T (c , x) (c , x')
          (hrflω C c , refl , u)))
      (hcng (𝒫𝒾 m n S T) c c' e)
      q
      (hcng t c c' e)
      where
      q : ℰ𝓁 (max m n) ∋
        (PI.ty (pi m n)
          (∥ S ∥ c)
          (λ x → ∥ T ∥ (c , x))
          (λ x x' u →
          hcng (⟪ 𝓆 S ⟫ * T') (c , x) (c , x')
          (hrflω C c , refl , u)
          ))
        ⸴
        PI.lam (pi m n) _ _ _
        (λ c' → PI.app (pi m n) _ _ _ (∥ t' ∥ (c , c')) c')
        (λ x x' u → PI.appCong (pi m n) _ _ _ _ _ _ _ _ _ _
          (hcng t' (c , x) (c , x') (hrflω _ c , refl , u))
          (hcng (𝓆 S) (c , x) (c , x') (hrflω _ c , refl , u)))
        ≈
        (PI.ty (pi m n) (∥ S ∥ c) (λ x → ∥ T ∥ (c , x))
        (λ x x' u → hcng T (c , x) (c , x')
          (hrflω C c , refl , u)))
        ⸴
        ∥ t ∥ c
      q = htrs (ℰ𝓁 (max m n))
        (PI.tyCong (pi m n) _ _ _ _ _ _ (rfl (𝒰 m) (∥ S ∥ c))
          (λ x x' u → hcng T (c , x) (c , x')
            (hrflω _ c , refl , u)))
        (rfl (𝒰 (max m n)) (∥ 𝒫𝒾 m n S T ∥ c))
        (PI.lamCong (pi m n) _ _ _ _ _ _ _ _ _ _
          λ x x' u → PI.appCong (pi m n) _ _ _ _ _ _ _ _ _ _
            (e' (c , x) (c , x)
          (hrflω C c , refl , hrfl (ℰ𝓁 m) (∥ S ∥ c) x)) u)
        (PI.eta (pi m n) _ _ _ (∥ t ∥ c))

----------------------------------------------------------------------
-- Equality types
----------------------------------------------------------------------
ℰ𝓆 :
  {C : Uω}
  (n : ℕ)
  (T : Fam n C)
  (t t' : Elt n C T)
  → ----------------
  Fam n C

∥ ℰ𝓆 n T t t' ∥ c =
  EQ.ty (eq n) (∥ T ∥ c) (∥ t ∥ c) (∥ t' ∥ c)
hcng (ℰ𝓆 n T t t') _ _ e = EQ.tyCong (eq n)
  (hcng T _ _ e)
  (hcng t _ _ e)
  (hcng t' _ _ e)

ntrlℰ𝓆 :
  {D C : Uω}
  (n : ℕ)
  (T : Fam n C)
  (t t' : Elt n C T)
  (f : Hom D C)
  → -------------------------------------------------------------
  ℱ𝒶𝓂 n ′ D ∋ f * (ℰ𝓆 n T t t') ~ ℰ𝓆 n (f * T) (f *₁ t) (f *₁ t')

ntrlℰ𝓆 n T t t' f _ _ e = EQ.tyCong (eq n)
  (hcng T _ _ (cng f _ _ e))
  (hcng t _ _ (cng f _ _ e))
  (hcng t' _ _ (cng f _ _ e))

𝓇𝒻𝓁 :
  {C : Uω}
  (n : ℕ)
  (T : Fam n C)
  (t : Elt n C T)
  → ------------------
  Elt n C (ℰ𝓆 n T t t)

∥ 𝓇𝒻𝓁 n _ t ∥ c = EQ.rfl (eq n) (∥ t ∥ c)
hcng (𝓇𝒻𝓁 n T t) _ _ e =
  EQ.rflCong (eq n) (hcng T _ _ e) (hcng t _ _ e)

ntrl𝓇𝒻𝓁 :
  {D C : Uω}
  (n : ℕ)
  (T : Fam n C)
  (t : Elt n C T)
  (f : Hom D C)
  → -----------------------------------------------------------
  ℰ𝓁𝓉 n ∋
  (D , f * (ℰ𝓆 n T t t)) ⸴ f *₁ (𝓇𝒻𝓁 n T t)
  ≈
  (D , ℰ𝓆 n (f * T) (f *₁ t) (f *₁ t)) ⸴ 𝓇𝒻𝓁 n (f * T) (f *₁ t)

ntrl𝓇𝒻𝓁 n T t f c c' e = EQ.rflCong (eq n)
  (hcng T (∣ f ∣ c) (∣ f ∣ c') (cng f c c' e))
  (hcng t (∣ f ∣ c) (∣ f ∣ c') (cng f c c' e))

𝓇ℯ𝒻𝓁ℯ𝒸𝓉 :
  {C : Uω}
  (n : ℕ)
  (T : Fam n C)
  (t t' : Elt n C T)
  (_ : Elt n C (ℰ𝓆 n T t t'))
  → -------------------------
  ℰ𝓁𝓉 n ′ (C , T) ∋ t ~ t'

𝓇ℯ𝒻𝓁ℯ𝒸𝓉 n T t t' e c c' u = htrs (ℰ𝓁 n)
  (rfl (𝒰 n) (∥ T ∥ c))
  (hcng T c c' u)
  (EQ.reflect (eq n) (∥ e ∥ c))
  (hcng t' c c' u)

𝓊𝒾𝓅 :
  {C : Uω}
  (n : ℕ)
  (T : Fam n C)
  (t t' : Elt n C T)
  (e e' : Elt n C (ℰ𝓆 n T t t'))
  → --------------------------------
  ℰ𝓁𝓉 n ′ (C , ℰ𝓆 n T t t') ∋ e ~ e'

𝓊𝒾𝓅{C} n T t t' e e' c c' u = htrs (ℰ𝓁 n)
  (rfl (𝒰 n) (∥ ℰ𝓆 n T t t' ∥ c))
  (hcng (ℰ𝓆 n T t t') c c' u)
  (EQ.uip (eq n) (∥ e ∥ c) (∥ e' ∥ c))
  (hcng e' c c' u)

----------------------------------------------------------------------
-- Empty type
----------------------------------------------------------------------
ℰ𝓂𝓅 :
 {C : Uω}
 → -------
 Fam 0 C

∥ ℰ𝓂𝓅 ∥ _ = Emp
hcng ℰ𝓂𝓅 _ _ _ = tt

ℯ𝓂𝓅 :
  {C : Uω}
  (n : ℕ)
  (S : Fam n C)
  (e : Elt 0 C ℰ𝓂𝓅)
  → ---------------
  Elt n C S

∥ ℯ𝓂𝓅 _ _ e ∥ c = Øelim (∥ e ∥ c)
hcng (ℯ𝓂𝓅 _ _ e) c _ _ = Øelim (∥ e ∥ c)

-- ntrlℯ𝓂𝓅 :
--   {D C : Uω}
--   (n : ℕ)
--   (S : Fam n C)
--   (e : Elt 0 C ℰ𝓂𝓅)
--   (f : Hom D C)
--   → --------------------------------------
--   ℰ𝓁𝓉 n ∋ (D , f * S) ⸴ f *₁ (ℯ𝓂𝓅 n S e) ≈
--   (D , f * S) ⸴ ℯ𝓂𝓅 n (f * S) (f *₁ e)

-- ntrlℯ𝓂𝓅 _ _ e f c _ _ = Øelim (∥ e ∥ (∣ f ∣ c))

----------------------------------------------------------------------
-- Natural number type
----------------------------------------------------------------------
𝒩𝒶𝓉 :
 {C : Uω}
 → -------
 Fam 0 C

∥ 𝒩𝒶𝓉 ∥ _ = Nat
hcng 𝒩𝒶𝓉 _ _ _ = tt

𝓏ℯ𝓇ℴ :
  {C : Uω}
  → ---------
  Elt 0 C 𝒩𝒶𝓉

∥ 𝓏ℯ𝓇ℴ ∥ _ = 0
hcng 𝓏ℯ𝓇ℴ _ _ _ = refl

𝓈𝓊𝒸𝒸 :
  {C : Uω}
  (t : Elt 0 C 𝒩𝒶𝓉)
  → ---------------
  Elt 0 C 𝒩𝒶𝓉

∥ 𝓈𝓊𝒸𝒸 t ∥ c = 1+ (∥ t ∥ c)
hcng (𝓈𝓊𝒸𝒸 t) _ _ e = cong 1+ (hcng t _ _ e)

ntrl𝓈𝓊𝒸𝒸 :
  {D C : Uω}
  (t : Elt 0 C 𝒩𝒶𝓉)
  (f : Hom D C)
  → --------------------------------
  ℰ𝓁𝓉 0 ∋ (D ,  𝒩𝒶𝓉) ⸴ f *₁ 𝓈𝓊𝒸𝒸 t ≈
  (D ,  𝒩𝒶𝓉) ⸴ 𝓈𝓊𝒸𝒸 (f *₁ t)

ntrl𝓈𝓊𝒸𝒸 t f c c' e =
  cong 1+ (hcng t (∣ f ∣ c) (∣ f ∣ c') (cng f c c' e))

𝓃𝓇ℯ𝒸 :
  {C : Uω}
  (n : ℕ)
  (S : Fam n (C ⋉[ 0 ] 𝒩𝒶𝓉))
  (s₀ : Elt n C (⟪ 𝓏ℯ𝓇ℴ ⟫ * S))
  (s₊ : Elt n (C ⋉[ 0 ] 𝒩𝒶𝓉 ⋉[ n ] S)
    (𝓅 S * 𝒸ℴ𝓃𝓈 (𝓅 𝒩𝒶𝓉) (𝓈𝓊𝒸𝒸 (𝓆 𝒩𝒶𝓉)) * S))
  (s : Elt 0 C 𝒩𝒶𝓉)
  → ----------------------------------------
  Elt n C (⟪ s ⟫ * S)

∥ 𝓃𝓇ℯ𝒸 n S s₀ s₊ s ∥ c = nrec n
  (λ m → ∥ S ∥ (c , m))
  (∥ s₀ ∥ c)
  (λ m y → ∥ s₊ ∥ ((c , m) , y))
  (λ n _ _ e → hcng s₊ _ _
    ((hrflω _ c , refl , refl) , refl , e))
  (∥ s ∥ c)
hcng (𝓃𝓇ℯ𝒸 n S s₀ s₊ s) c c' e = nrecCong{n}
  {λ m → ∥ S ∥ (c , m)}
  {λ m → ∥ S ∥ (c' , m)}
  {∥ s₀ ∥ c}
  {∥ s₀ ∥ c'}
  {λ m y → ∥ s₊ ∥ ((c , m) , y)}
  {λ m y → ∥ s₊ ∥ ((c' , m) , y)}
  {λ n _ _ e → hcng s₊ _ _
    ((hrflω _ c , refl , refl) , refl , e)}
  {λ n _ _ e → hcng s₊ _ _
    ((hrflω _ c' , refl , refl) , refl , e)}
  (∥ s ∥ c)
  (∥ s ∥ c')
  (λ _ → hcng S _ _ (e , refl , refl))
  (hcng s₀ _ _ e)
  (λ _ _ _ e' → hcng s₊ _ _
    ((e , refl , refl) , refl , e'))
  (hcng s _ _ e)

ntrl𝓃𝓇ℯ𝒸 :
  {D C : Uω}
  (n : ℕ)
  (S : Fam n (C ⋉[ 0 ] 𝒩𝒶𝓉))
  (s₀ : Elt n C (⟪ 𝓏ℯ𝓇ℴ ⟫ * S))
  (s₊ : Elt n (C ⋉[ 0 ] 𝒩𝒶𝓉 ⋉[ n ] S)
    (𝓅 S * (𝒸ℴ𝓃𝓈 (𝓅 𝒩𝒶𝓉) (𝓈𝓊𝒸𝒸 (𝓆 𝒩𝒶𝓉))) * S))
  (s : Elt 0 C 𝒩𝒶𝓉)
  (f : Hom D C)
  → -------------------------------------------
  ℰ𝓁𝓉 n ∋
  (D , f * ⟪ s ⟫ * S) ⸴ f *₁ (𝓃𝓇ℯ𝒸 n S s₀ s₊ s)
  ≈
  (D , ⟪ f *₁ s ⟫ * (f ⋉′[ 0 ] 𝒩𝒶𝓉) * S) ⸴
  𝓃𝓇ℯ𝒸 n
    (f ⋉′[ 0 ] 𝒩𝒶𝓉 * S)
    (f *₁ s₀)
    (f ⋉′[ 0 ] 𝒩𝒶𝓉 ⋉′[ n ] S *₁ s₊)
    (f *₁ s)

ntrl𝓃𝓇ℯ𝒸 n S s₀ s₊ s f c c' e = nrecCong{n}
   {λ m → ∥ S ∥ (∣ f ∣ c , m)}
   {λ m → ∥ S ∥ (∣ f ∣ c' , m)}
   {∥ s₀ ∥ (∣ f ∣ c)}
   {∥ s₀ ∥ (∣ f ∣ c')}
   {λ m x' → ∥ s₊ ∥ ((∣ f ∣ c , m) , x')}
   {λ m x' → ∥ s₊ ∥ ((∣ f ∣ c' , m) , x')}
   {λ _ _ _ e' → hcng s₊ _ _
     ((hrflω _ (∣ f ∣ c) , refl , refl) , refl , e')}
   {λ _ _ _ e' → hcng s₊ _ _
     ((hrflω _ (∣ f ∣ c') , refl , refl) , refl , e')}
   (∥ s ∥ (∣ f ∣ c))
   (∥ s ∥ (∣ f ∣ c'))
   (λ _ → hcng S _ _ (cng f c c' e , refl , refl))
   (hcng s₀ (∣ f ∣ c) (∣ f ∣ c') (cng f c c' e))
   (λ _ _ _ e' → hcng s₊ _ _
     ((cng f c c' e , refl , refl) , refl , e'))
   (hcng s (∣ f ∣ c) (∣ f ∣ c') (cng f c c' e))

----------------------------------------------------------------------
-- Displayed morphisms , families and elements
----------------------------------------------------------------------
ℱ𝓊𝓃 : Setd

ℱ𝓊𝓃 = (𝒰ω ⊗ 𝒰ω) ⋉ ℋℴ𝓂

Σℱ𝒶𝓂 : ℕ → Setd

Σℱ𝒶𝓂  l = 𝒰ω ⋉ ℱ𝒶𝓂 l

Σℱ𝒶𝓂ℰ𝓁𝓉 : ℕ → Setd[ 𝒰ω ]

Σℱ𝒶𝓂ℰ𝓁𝓉 l = Σ (ℱ𝒶𝓂 l) (ℰ𝓁𝓉 l)

Σℰ𝓁𝓉 : ℕ → Setd

Σℰ𝓁𝓉 l = 𝒰ω ⋉ Σℱ𝒶𝓂ℰ𝓁𝓉 l
