module Setoid.Display where

open import Prelude
open import Setoid.Definition

{- Although not exactly the same, the following definition is
comparible with Definition 5.3.4 in Martin Hofmann's thesis. -}

----------------------------------------------------------------------
-- Displayed setoids
----------------------------------------------------------------------
infix 5 Setd[_]
record Setd[_] (A : Setd) : Set₁ where
  constructor mkSetd[]
  infix 8 ∥_∥
  infix 3 _∋_≈_
  field
    -- underlying family of sets
    ∥_∥ : ∣ A ∣ → Set
    -- heterogeneous, Set-valued equality relation
    _∋_≈_ : (_ _ : ∑ ∣ A ∣ ∥_∥) → Set
    hrfl :
      (x : ∣ A ∣)
      (y : ∥_∥ x)
      → ------------------
      _∋_≈_ (x , y)(x , y)
    hsym :
      {x x' : ∣ A ∣}
      {y : ∥_∥ x}
      {y' : ∥_∥ x'}
      -- Note the presence of the next argument
      (_ : A ∋ x ~ x')
      (_ : _∋_≈_ (x , y) (x' , y'))
      → ---------------------------
      _∋_≈_ (x' , y') (x , y)
    htrs :
      {x x' x'' : ∣ A ∣}
      {y : ∥_∥ x}
      {y' : ∥_∥ x'}
      {y'' : ∥_∥ x''}
      -- Note the presence of the next two arguments
      (_ : A ∋ x ~ x')
      (_ : A ∋ x' ~ x'')
      (_ : _∋_≈_ (x , y) (x' , y'))
      (_ : _∋_≈_ (x' , y') (x'' , y''))
      → -------------------------------
      _∋_≈_ (x , y) (x'' , y'')
    -- coercion function
    coe :
      {x x' : ∣ A ∣}
      (e : A ∋ x ~ x')
      → -------------
      ∥_∥ x → ∥_∥ x'
    -- coherence property
    coh :
      {x x' : ∣ A ∣}
      (e : A ∋ x ~ x')
      (y : ∥_∥ x)
      → --------------------------
      _∋_≈_ (x , y) (x' , coe e y)

  -- inverse coherence
  coh⁻¹ :
    {x x' : ∣ A ∣}
    (e : A ∋ x ~ x')
    (y : ∥_∥ x)
    → --------------------------
    _∋_≈_ (x' , coe e y) (x , y)
  coh⁻¹ e y = hsym e (coh e y)

open Setd[_] public

-- Re-indexing
infixl 6 _*₀_
_*₀_ :
  {B A : Setd}
  (_ : Setd[ A ])
  (_ : ∣ B ⟶ A ∣)
  → -------------
  Setd[ B ]

∥ C *₀ f ∥ y = ∥ C ∥ (∣ f ∣ y)
(C *₀ f ∋ y , z ≈ y' , z') = C ∋ ∣ f ∣ y , z ≈ ∣ f ∣ y' , z'
hrfl (C *₀ f) x = hrfl C (∣ f ∣ x)
hsym (C *₀ f) x e = hsym C (cng f _ _ x) e
htrs (C *₀ f) x x' e e' = htrs C (cng f _ _ x) (cng f _ _ x') e e'
coe (C *₀ f) e = coe C (cng f _ _ e)
coh (C *₀ f) e = coh C (cng f _ _ e)

instance
  *₀Apply :
    {B A : Setd}
    → ---------------------------------
    Apply Setd[ A ] ∣ B ⟶ A ∣ Setd[ B ]
  _*_ ⦃ *₀Apply ⦄ = _*₀_

-- The fibres of a displayed setoid are setoids
infix 6 _′_
_′_ :
  {A : Setd}
  (B : Setd[ A ])
  (x : ∣ A ∣)
  → -------------
  Setd

∣ B ′ x ∣ = ∥ B ∥ x
(B ′ x ∋ y ~ y') = B ∋ x , y ≈ x , y'
rfl (B ′ x) = hrfl B x
sym (_′_ {A} B x) = hsym B (rfl A x)
trs (_′_ {A} B x) = htrs B (rfl A x) (rfl A x)

-- Constant displayed setoids
K :
  {A : Setd}
  (B : Setd)
  → --------
  Setd[ A ]

∥ K B ∥ _ = ∣ B ∣
K B ∋ _ , y ≈ _ , y' = B ∋ y ~ y'
hrfl (K B) _ a = rfl B a
hsym (K B) _ e = sym B e
htrs (K B) _ _ e e' = trs B e e'
coe (K B) _ y = y
coh (K B) _ y = rfl B y

----------------------------------------------------------------------
-- Section of a displayed setoid
----------------------------------------------------------------------
infix 5 Setd[_⊩_]
record Setd[_⊩_] (A : Setd)(B : Setd[ A ]) : Set where
  constructor mkSetd[⊩]
  infix 8 ∥_∥
  field
    -- underlying dependent function
    ∥_∥ : (x : ∣ A ∣) → ∥ B ∥ x
    -- the function is equality preserving
    hcng :
      (x y : ∣ A ∣)
      (_ : A ∋ x ~ y)
      → -----------------------
      B ∋ x , ∥_∥ x ≈ y , ∥_∥ y

open Setd[_⊩_] public

-- Re-indexing
infixl 6 [_,_]*_
[_,_]*_ :
  {B A : Setd}
  (C : Setd[ A ])
  (_ : Setd[ A ⊩ C ])
  (f : ∣ B ⟶ A ∣)
  → -----------------
  Setd[ B ⊩ C * f ]

∥ [ _ , c ]* f ∥ y = ∥ c ∥ (∣ f ∣ y)
hcng ([ _ , c ]* f) _ _ e = hcng c _ _ (cng f _ _ e)

----------------------------------------------------------------------
-- Comprehension structure
----------------------------------------------------------------------
infixl 5 _⋉_
_⋉_ :
  (A : Setd)
  (_ : Setd[ A ])
  → -------------
  Setd

∣ A ⋉ B ∣ = ∑ ∣ A ∣ ∥ B ∥
A ⋉ B ∋ (x , y) ~ (x' , y') =
  (A ∋ x ~ x') × (B ∋ x , y ≈ x' , y')
rfl (A ⋉ B) (x , y) = (rfl A x , hrfl B x y)
sym (A ⋉ B) (e , e') = (sym A e , hsym B e e')
trs (A ⋉ B) (e₁ , e₁') (e₂ , e₂') =
  (trs A e₁ e₂ , htrs B e₁ e₂ e₁' e₂')

----------------------------------------------------------------------
-- Setoid dependent product type
----------------------------------------------------------------------
Σ :
  {A : Setd}
  (B : Setd[ A ])
  (C : Setd[ A ⋉ B ])
  → -----------------
  Setd[ A ]

∥ Σ B C ∥ x = ∑[ y ∈ ∥ B ∥ x ] ∥ C ∥ (x , y)
Σ B C ∋ x , (y , z) ≈ x' , (y' , z') =
  (B ∋ x , y ≈ x' , y') × (C ∋ (x , y) , z ≈ (x' , y') , z')
hrfl (Σ B C) x (y , z) = (hrfl B x y , hrfl C (x , y) z)
hsym (Σ B C) e (f , g) = (hsym B e f , hsym C (e , f) g)
htrs (Σ {A} B C) e e' (f , g) (f' , g') =
  (htrs B e e' f f' , htrs C (e , f) (e' , f') g g')
coe (Σ B C) e (x , y) = (coe B e x , coe C (e , coh B e x) y)
coh (Σ B C) e (x , y) = (coh B e x , coh C (e , coh B e x) y)

----------------------------------------------------------------------
-- Setoid dependent function type
----------------------------------------------------------------------
Π :
  {A : Setd}
  (B : Setd[ A ])
  (C : Setd[ A ⋉ B ])
  → -----------------
  Setd[ A ]

∥ Π B C ∥ x =
  ∑[ f ∈ ((y : ∥ B ∥ x) → ∥ C ∥ (x , y)) ]
  ((y y' :  ∥ B ∥ x)
   (_ : B ∋ x , y ≈ x , y')
   → ---------------------------------
   C ∋ (x , y) , f y ≈ (x , y') , f y')

Π B C ∋ x , (f , _) ≈ x' , (f' , _) =
  (y :  ∥ B ∥ x)
  (y' :  ∥ B ∥ x')
  (_ : B ∋ x , y ≈ x' , y')
  → -----------------------------------
  C ∋ (x , y) , f y ≈ (x' , y') , f' y'

hrfl (Π B C) _ (_ , e) y y' e' = e y y' e'

hsym (Π{A} B C) xx' fg y y' yy' = hsym C
  (xx' , hsym B (sym A xx') yy')
  (fg y' y (hsym B (sym A xx') yy'))

htrs (Π{A} B C) xx' x'x'' fg gh y y'' yy'' =
  let
    y' = coe B xx' y
    yy' = coh B xx' y
    y'y'' = htrs B
      (sym A xx')
      (trs A xx' x'x'')
      (coh⁻¹ B xx' y)
      yy''
  in htrs C
    (xx' , yy')
    (x'x'' , y'y'')
    (fg y y' yy')
    (gh y' y'' y'y'')

coe (Π{A} B C) xx' (f , e) =
  let x'x = sym A xx' in
  ((λ y →
    coe C (xx' , coh⁻¹ B x'x y) (f (coe B x'x y)))
  ,
  λ y y' yy' →
    let
      e₁ = coh⁻¹ B x'x y
      e₂ = coh⁻¹ B x'x y'
      e₃ = htrs B xx' x'x e₁ (htrs B (rfl A _) x'x
           yy' (hsym B xx' e₂))
    in htrs C
      (x'x , hsym B xx' e₁)
      (xx' , htrs B (rfl A _) xx' e₃ e₂)
      (coh⁻¹ C (xx' , e₁) (f (coe B x'x y)))
      (htrs C
        (rfl A _ , e₃)
        (xx' , e₂)
        (e (coe B x'x y) (coe B x'x y') e₃)
        (coh C (xx' , e₂) (f (coe B x'x y')))))

coh (Π {A} B C) xx' (f , e) y y' yy' =
  let
    x'x = sym A xx'
    e₀ = coh B x'x y'
    e₁ = htrs B xx' x'x yy' e₀
    e₂ = (xx' , hsym B x'x e₀)
  in htrs C
    (rfl A _ , e₁)
    e₂
    (e y (coe B x'x y') e₁)
    (coh C e₂ (f (coe B x'x y')))
