module Setoid.Display where

open import Prelude
open import Setoid.Definition

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
      (x x' : ∣ A ∣)
      (_ : A ∋ x ~ x')
      → -------------------------
      B ∋ x , ∥_∥ x ≈ x' , ∥_∥ x'

open Setd[_⊩_] public

----------------------------------------------------------------------
-- Fibres of a displayed setoid
----------------------------------------------------------------------
module Fibres {A : Setd} where
  infix 6 _′_
  -- the fibres of a displayed setoid
  _′_ : Setd[ A ] → ∣ A ∣ → Setd
  ∣ B ′ x ∣ = ∥ B ∥ x
  (B ′ x ∋ y ~ y') = B ∋ x , y ≈ x , y'
  rfl (B ′ x) = hrfl B x
  sym (_′_ B x) = hsym B (rfl A x)
  trs (_′_ B x) = htrs B (rfl A x) (rfl A x)

  -- induced morphisms between fibres
  infix 6 _′′_
  _′′_  :
    (B : Setd[ A ])
    {x₁ x₂ : ∣ A ∣}
    (_ : A ∋ x₁ ~ x₂)
    → -----------------
    ∣ B ′ x₁ ⟶ B ′ x₂ ∣

  ∣ B ′′ e ∣ = coe B e
  cng (_′′_ B e) y y' e' = htrs B
    (sym A e)
    e
    (coh⁻¹ B e y)
    (htrs B (rfl A _) e e' (coh B e y'))

  -- proof irrelevance for the induced morphisms between fibres
  ′′irrel :
    (B : Setd[ A ])
    {x₁ x₂ : ∣ A ∣}
    (e₁ e₂ : A ∋ x₁ ~ x₂)
    → -----------------------------------
    (B ′ x₁ ⟶ B ′ x₂) ∋ B ′′ e₁ ~ B ′′ e₂

  ′′irrel B e₁ e₂ y = htrs B
    (sym A e₁)
    e₂
    (coh⁻¹ B e₁ y)
    (coh B e₂ y)

open Fibres public

----------------------------------------------------------------------
-- Re-indexing displayed setoids and their sections
----------------------------------------------------------------------
module ReIndex where
  infixl 6 _*₀_
  _*₀_ :
    {A A' : Setd}
    (_ : Setd[ A ])
    (_ : ∣ A' ⟶ A ∣)
    → -------------
    Setd[ A' ]

  ∥ B *₀ f ∥ = ∥ B ∥ ∘ ∣ f ∣
  (B *₀ f ∋ x , y ≈ x' , y') = B ∋ ∣ f ∣ x , y ≈ ∣ f ∣ x' , y'
  hrfl (B *₀ f) x = hrfl B (∣ f ∣ x)
  hsym (B *₀ f) x e = hsym B (cng f _ _ x) e
  htrs (B *₀ f) x x' e e' = htrs B (cng f _ _ x) (cng f _ _ x') e e'
  coe (B *₀ f) e = coe B (cng f _ _ e)
  coh (B *₀ f) e = coh B (cng f _ _ e)

  instance
    *₀Apply :
      {B A : Setd}
      → ---------------------------------
      Apply Setd[ A ] ∣ B ⟶ A ∣ Setd[ B ]
    _*_ ⦃ *₀Apply ⦄ = _*₀_

  *assoc :
    {A A' A'' : Setd}
    (B : Setd[ A ])
    (f : ∣ A' ⟶ A ∣)
    (g : ∣ A'' ⟶ A' ∣)
    → -----------------------
    (B * f) * g ≡ B * (f ∘ g)

  *assoc _ _ _ = refl

  *unit :
    {A : Setd}
    (B : Setd[ A ])
    → -------------
    B ≡ B * id

  *unit _ = refl

  infixl 6 [_,_]*_
  [_,_]*_ :
    {A A' : Setd}
    (B : Setd[ A ])
    (_ : Setd[ A ⊩ B ])
    (f : ∣ A' ⟶ A ∣)
    → -----------------
    Setd[ A' ⊩ B * f ]

  ∥ [ _ , g ]* f ∥ x = ∥ g ∥ (∣ f ∣ x)
  hcng ([ _ , g ]* f) _ _ e = hcng g _ _ (cng f _ _ e)

  [,]*unit :
    {A  : Setd}
    (B : Setd[ A ])
    (f : Setd[ A ⊩ B ])
    → -----------------
    f ≡ [ B , f ]* id

  [,]*unit _ _ = refl

  [,]*assoc :
    {A A' A'' : Setd}
    (B : Setd[ A ])
    (f : Setd[ A ⊩ B ])
    (g : ∣ A' ⟶ A ∣)
    (h : ∣ A'' ⟶ A' ∣)
    → ----------------------------------------------
    [ B * g , [ B , f ]* g ]* h ≡ [ B , f ]* (g ∘ h)

  [,]*assoc _ _ _ _ = refl

open ReIndex public

----------------------------------------------------------------------
-- Comprehension structure
----------------------------------------------------------------------
module Comprehension (A : Setd)(B : Setd[ A ]) where
  infixl 6 _⋉_
  _⋉_ : Setd

  ∣_∣ _⋉_ = ∑ ∣ A ∣ ∥ B ∥
  _⋉_ ∋ (x , y) ~ (x' , y') =
    (A ∋ x ~ x') × (B ∋ x , y ≈ x' , y')
  rfl (_⋉_) (x , y) = (rfl A x , hrfl B x y)
  sym (_⋉_) (e , e') = (sym A e , hsym B e e')
  trs (_⋉_) (e₁ , e₁') (e₂ , e₂') =
    (trs A e₁ e₂ , htrs B e₁ e₂ e₁' e₂')

  𝓅₁ : ∣ _⋉_ ⟶ A ∣

  ∣ 𝓅₁ ∣ = π₁
  cng 𝓅₁ _ _ = π₁

  𝓅₂ : Setd[ _⋉_ ⊩ B * 𝓅₁ ]

  ∥ 𝓅₂ ∥ = π₂
  hcng 𝓅₂ _ _ = π₂

  𝓅𝓇 :
    {A' : Setd}
    (f : ∣ A' ⟶ A ∣)
    (g : Setd[ A' ⊩ B * f ])
    → ----------------------
    ∣ A' ⟶ _⋉_ ∣

  ∣ 𝓅𝓇 f g ∣ x = (∣ f ∣ x , ∥ g ∥ x)
  cng (𝓅𝓇 f g) x x' e = (cng f x x' e , hcng g x x' e)

  𝓅₁∘𝓅𝓇 :
    {A' : Setd}
    (f : ∣ A' ⟶ A ∣)
    (g : Setd[ A' ⊩ B * f ])
    → ----------------------
    𝓅₁ ∘ 𝓅𝓇 f g ≡ f

  𝓅₁∘𝓅𝓇 _ _ = refl

  𝓅₂∘𝓅𝓇 :
    {A' : Setd}
    (f : ∣ A' ⟶ A ∣)
    (g : Setd[ A' ⊩ B * f ])
    → -------------------------
    [ B * 𝓅₁ , 𝓅₂ ]* 𝓅𝓇 f g ≡ g

  𝓅₂∘𝓅𝓇 _ _ = refl

  𝓅𝓇∘ :
    {A' A'' : Setd}
    (f : ∣ A' ⟶ A ∣)
    (g : Setd[ A' ⊩ B * f ])
    (h : ∣ A'' ⟶ A' ∣)
    → ------------------------------------------
    (𝓅𝓇 f g) ∘ h ≡ 𝓅𝓇 (f ∘ h) ([ B * f , g ]* h)

  𝓅𝓇∘ _ _ _ = refl

  𝓅𝓇Eta : 𝓅𝓇 𝓅₁ 𝓅₂ ≡ id

  𝓅𝓇Eta = refl

open Comprehension public

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
