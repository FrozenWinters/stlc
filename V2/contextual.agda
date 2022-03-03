{-# OPTIONS --cubical #-}

module contextual where

open import lists

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

record Category (ℓ₁ ℓ₂ : Level) : Type (lsuc (ℓ₁ ⊔ ℓ₂)) where
  infixl 20 _⊚_
  field
    𝑜𝑏 : Type ℓ₁
    𝑚𝑜𝑟 : 𝑜𝑏 → 𝑜𝑏 → Type ℓ₂
    _⊚_ : {A B C : 𝑜𝑏} → 𝑚𝑜𝑟 B C → 𝑚𝑜𝑟 A B → 𝑚𝑜𝑟 A C
    𝒾𝒹 : (A : 𝑜𝑏) → 𝑚𝑜𝑟 A A
    𝒾𝒹L : {A B : 𝑜𝑏} (f : 𝑚𝑜𝑟 A B) → 𝒾𝒹 B ⊚ f ≡ f
    𝒾𝒹R : {A B : 𝑜𝑏} (f : 𝑚𝑜𝑟 A B) → f ⊚ 𝒾𝒹 A ≡ f
    ⊚Assoc : {A B C D : 𝑜𝑏} → (f : 𝑚𝑜𝑟 C D) (g : 𝑚𝑜𝑟 B C) (h : 𝑚𝑜𝑟 A B) →
      (f ⊚ g) ⊚ h ≡ f ⊚ (g ⊚ h)
    isSetMor : {A B : 𝑜𝑏} → isSet (𝑚𝑜𝑟 A B)

record Contextual (ℓ₁ ℓ₂ : Level) : Type (lsuc (ℓ₁ ⊔ ℓ₂))

𝑎𝑚𝑏Cat : Contextual ℓ₁ ℓ₂ → Category ℓ₁ (ℓ₁ ⊔ ℓ₂)

record Contextual ℓ₁ ℓ₂ where

  field
    ty : Type ℓ₁

  ctx = 𝐶𝑡𝑥 ty

  field
    tm : ctx → ty → Type ℓ₂

  tms = 𝑇𝑚𝑠 tm

  infixl 30 _⟦_⟧
  field
    _⟦_⟧ : {Γ Δ : ctx} {A : ty} → tm Δ A → tms Γ Δ → tm Γ A

  infixl 20 _⊚_
  _⊚_ : {Γ Δ Σ : ctx} → tms Δ Σ → tms Γ Δ → tms Γ Σ
  σ ⊚ τ = map𝐸𝑙𝑠 _⟦ τ ⟧ σ

  field
    𝒾𝒹 : (Γ : ctx) → tms Γ Γ
    𝒾𝒹L : {Γ Δ : ctx} (σ : tms Γ Δ) → 𝒾𝒹 Δ ⊚ σ ≡ σ
    𝒾𝒹⟦⟧ : {Γ : ctx} {A : ty} (t : tm Γ A) → t ⟦ 𝒾𝒹 Γ ⟧ ≡ t
    ⟦⟧⟦⟧ : {Γ Δ Σ : ctx} {A : ty} (t : tm Σ A) (σ : tms Δ Σ) (τ : tms Γ Δ) →
      t ⟦ σ ⟧ ⟦ τ ⟧ ≡ t ⟦ σ ⊚ τ ⟧
    isSetTm : {Γ : ctx} {A : ty} → isSet (tm Γ A)

  𝒾𝒹R : {Γ Δ : ctx} (σ : tms Γ Δ) → σ ⊚ 𝒾𝒹 Γ ≡ σ
  𝒾𝒹R ! = refl
  𝒾𝒹R (σ ⊕ t) i = 𝒾𝒹R σ i ⊕ 𝒾𝒹⟦⟧ t i

  ⊚Assoc : {Γ Δ Σ Ω : ctx} (σ : tms Σ Ω) (τ : tms Δ Σ) (μ : tms Γ Δ) →
    (σ ⊚ τ) ⊚ μ ≡ σ ⊚ (τ ⊚ μ)
  ⊚Assoc ! τ μ = refl
  ⊚Assoc (σ ⊕ t) τ μ i = ⊚Assoc σ τ μ i ⊕ ⟦⟧⟦⟧ t τ μ i

  private
    module P = 𝑇𝑚𝑠Path tm isSetTm

  isSetTms = P.isSet𝑇𝑚𝑠

  ambCat : Category ℓ₁ (ℓ₁ ⊔ ℓ₂)
  Category.𝑜𝑏 ambCat = ctx
  Category.𝑚𝑜𝑟 ambCat = tms
  Category._⊚_ ambCat = _⊚_
  Category.𝒾𝒹 ambCat = 𝒾𝒹
  Category.𝒾𝒹L ambCat = 𝒾𝒹L
  Category.𝒾𝒹R ambCat = 𝒾𝒹R
  Category.⊚Assoc ambCat = ⊚Assoc
  Category.isSetMor ambCat = isSetTms

  !η : {Γ : ctx} (σ : tms Γ ∅) → ! ≡ σ
  !η ! = refl

  -- Weakening theory

  𝑧 : {Γ : ctx} {A : ty} → tm (Γ ⊹ A) A
  𝑧 {Γ} {A} = 𝑧𝐸𝑙𝑠 (𝒾𝒹 (Γ ⊹ A))

  π : {Γ : ctx} {A : ty} → tms (Γ ⊹ A) Γ
  π {Γ} {A} = π𝐸𝑙𝑠 (𝒾𝒹 (Γ ⊹ A))

  𝒾𝒹η₁ : {Γ : ctx} {A : ty} → π ⊕ 𝑧 ≡ 𝒾𝒹 (Γ ⊹ A)
  𝒾𝒹η₁ {Γ} {A} = π𝑧η𝐸𝑙𝑠 (𝒾𝒹 (Γ ⊹ A))

  π𝑧η : {Γ Δ : ctx} {A : ty} (σ : tms Γ (Δ ⊹ A)) →
    (π ⊚ σ) ⊕ (𝑧 ⟦ σ ⟧) ≡ σ
  π𝑧η {Γ} {Δ} {A} σ =
    π ⊚ σ ⊕ 𝑧 ⟦ σ ⟧
      ≡⟨ ap (_⊚ σ) 𝒾𝒹η₁ ⟩
    𝒾𝒹 (Δ ⊹ A) ⊚ σ
      ≡⟨ 𝒾𝒹L σ ⟩
    σ
      ∎

  π⟦⟧ : {Γ Δ : ctx} {A : ty} (σ : tms Γ (Δ ⊹ A)) →
    π ⊚ σ ≡ π𝐸𝑙𝑠 σ
  π⟦⟧ σ = ap π𝐸𝑙𝑠 (π𝑧η σ)

  𝑧⟦⟧ : {Γ Δ : ctx} {A : ty} (σ : tms Γ (Δ ⊹ A)) →
    𝑧 ⟦ σ ⟧ ≡ 𝑧𝐸𝑙𝑠 σ
  𝑧⟦⟧ σ = ap 𝑧𝐸𝑙𝑠 (π𝑧η σ)

  W₁tm : {Γ : ctx} (A : ty) {B : ty} → tm Γ B → tm (Γ ⊹ A) B
  W₁tm A t = t ⟦ π ⟧

  W₁tms : {Γ Δ : ctx} (A : ty) → tms Γ Δ → tms (Γ ⊹ A) Δ
  W₁tms A σ = σ ⊚ π

  W₂tms : {Γ Δ : ctx} (A : ty) → tms Γ Δ → tms (Γ ⊹ A) (Δ ⊹ A)
  W₂tms A σ = W₁tms A σ ⊕ 𝑧

  Wtm⟦⟧ : {Γ Δ : ctx} {A B : ty} (t : tm Δ B) (σ : tms Γ Δ) (s : tm Γ A) →
    W₁tm A t ⟦ σ ⊕ s ⟧ ≡ t ⟦ σ ⟧
  Wtm⟦⟧ t σ s =
    t ⟦ π ⟧ ⟦ σ ⊕ s ⟧
      ≡⟨ ⟦⟧⟦⟧ t π (σ ⊕ s) ⟩
    t ⟦ π ⊚ (σ ⊕ s) ⟧
      ≡⟨ ap (t ⟦_⟧) (π⟦⟧ (σ ⊕ s)) ⟩
    t ⟦ σ ⟧
      ∎

  Wtms⊚ : {Γ Δ Σ : ctx} {A : ty} (σ : tms Δ Σ) (τ : tms Γ Δ) (t : tm Γ A) →
    W₁tms A σ ⊚ (τ ⊕ t) ≡ σ ⊚ τ
  Wtms⊚ ! τ t = refl
  Wtms⊚ (σ ⊕ s) τ t i = Wtms⊚ σ τ t i ⊕ Wtm⟦⟧ s τ t i

  Wlem1 : {Γ Δ : ctx} {A B : ty} (t : tm Δ B) (σ : tms Γ Δ) →
    t ⟦ W₁tms A σ ⟧ ≡ W₁tm A (t ⟦ σ ⟧)
  Wlem1 t σ = ⟦⟧⟦⟧ t σ π ⁻¹

  Wlem2 : {Γ Δ Σ : ctx} {A : ty} (σ : tms Δ Σ) (τ : tms Γ Δ) →
    σ ⊚ W₁tms A τ ≡ W₁tms A (σ ⊚ τ)
  Wlem2 ! τ = refl
  Wlem2 (σ ⊕ t) τ i = Wlem2 σ τ i ⊕ Wlem1 t τ i

  Wlem3 : {Γ Δ Σ : ctx} {A : ty} (σ : tms Δ Σ) (τ : tms Γ Δ) →
    W₁tms A σ ⊚ W₂tms A τ ≡ W₁tms A (σ ⊚ τ)
  Wlem3 {A = A} σ τ =
    W₁tms A σ ⊚ (W₁tms A τ ⊕ 𝑧)
      ≡⟨ Wtms⊚ σ (W₁tms A τ) 𝑧 ⟩
    σ ⊚ W₁tms A τ
      ≡⟨ Wlem2 σ τ ⟩
    W₁tms A (σ ⊚ τ)
      ∎

  Wlem4 : {Γ Δ Σ : ctx} {A : ty} (σ : tms Δ Σ) (τ : tms Γ Δ) →
    W₂tms A σ ⊚ W₂tms A τ ≡ W₂tms A (σ ⊚ τ)
  Wlem4 {A = A} σ τ i = Wlem3 σ τ i ⊕ 𝑧⟦⟧ (W₂tms A τ) i

  -- Variable theory

  IntVar = 𝑉𝑎𝑟 ty
  IntRen = 𝑅𝑒𝑛 ty

  ρεν : Contextual ℓ₁ ℓ₁
  ty ρεν = ty
  tm ρεν = IntVar
  _⟦_⟧ ρεν = _[_]𝑅
  𝒾𝒹 ρεν Γ = id𝑅𝑒𝑛 Γ
  𝒾𝒹L ρεν = ∘𝑅𝑒𝑛IdL
  𝒾𝒹⟦⟧ ρεν = [id]𝑅𝑒𝑛
  ⟦⟧⟦⟧ ρεν = [][]𝑅𝑒𝑛
  isSetTm ρεν = 𝑉𝑎𝑟Path.isSet𝑉𝑎𝑟

  REN : Category ℓ₁ ℓ₁
  REN = 𝑎𝑚𝑏Cat ρεν

  makeVar : {Γ : ctx} {A : ty} → IntVar Γ A → tm Γ A
  makeVar {Γ} = derive (𝒾𝒹 Γ)

  makeRen : {Γ Δ : ctx} → IntRen Γ Δ → tms Γ Δ
  makeRen {Γ} = derive𝑅𝑒𝑛 (𝒾𝒹 Γ)

  derive⟦⟧ : {Γ Δ Σ : ctx} {A : ty} (v : IntVar Σ A) (σ : tms Δ Σ) (τ : tms Γ Δ) →
    derive σ v ⟦ τ ⟧ ≡ derive (σ ⊚ τ) v
  derive⟦⟧ 𝑧𝑣 σ τ =
    𝑧𝐸𝑙𝑠 σ ⟦ τ ⟧
      ≡⟨ ap _⟦ τ ⟧ (𝑧⟦⟧ σ ⁻¹) ⟩
    𝑧 ⟦ σ ⟧ ⟦ τ ⟧
      ≡⟨ ⟦⟧⟦⟧ 𝑧 σ τ ⟩
    𝑧 ⟦ σ ⊚ τ ⟧
      ≡⟨ 𝑧⟦⟧ (σ ⊚ τ) ⟩
    𝑧𝐸𝑙𝑠 (σ ⊚ τ)
      ∎
  derive⟦⟧ (𝑠𝑣 v) σ τ =
    derive (π𝐸𝑙𝑠 σ) v ⟦ τ ⟧
      ≡⟨ (λ i → derive (π⟦⟧ σ (~ i)) v ⟦ τ ⟧) ⟩
    derive (π ⊚ σ) v ⟦ τ ⟧
      ≡⟨ ap _⟦ τ ⟧ (derive⟦⟧ v π σ ⁻¹) ⟩
    derive π v ⟦ σ ⟧ ⟦ τ ⟧
      ≡⟨ ⟦⟧⟦⟧ (derive π v) σ τ ⟩
    derive π v ⟦ σ ⊚ τ ⟧
      ≡⟨ derive⟦⟧ v π (σ ⊚ τ) ⟩
    derive (π ⊚ (σ ⊚ τ)) v
      ≡⟨ (λ i → derive (π⟦⟧ (σ ⊚ τ) i) v) ⟩
    derive (π𝐸𝑙𝑠 (σ ⊚ τ)) v
      ∎

  var⟦⟧ : {Γ Δ : ctx} {A : ty} (v : IntVar Δ A) (σ : tms Γ Δ) →
    makeVar v ⟦ σ ⟧ ≡ derive σ v
  var⟦⟧ {Γ} {Δ} v σ =
    derive (𝒾𝒹 Δ) v ⟦ σ ⟧
      ≡⟨ derive⟦⟧ v (𝒾𝒹 Δ) σ ⟩
    derive (𝒾𝒹 Δ ⊚ σ) v
      ≡⟨ (λ i → derive (𝒾𝒹L σ i) v) ⟩
    derive σ v
      ∎

  make𝑠𝑣 : {Γ : ctx} {A B : ty} (v : IntVar Γ B) →
    makeVar (𝑠𝑣 v) ≡ W₁tm A (makeVar v)
  make𝑠𝑣 v = var⟦⟧ v π ⁻¹

  makeW : {Γ Δ : ctx} {A : ty} (σ : IntRen Γ Δ) →
    makeRen (W₁𝑅𝑒𝑛 A σ) ≡ W₁tms A (makeRen σ)
  makeW ! = refl
  makeW (σ ⊕ v) i = makeW σ i ⊕ make𝑠𝑣 v i

  𝑠𝑣⟦⟧ : {Γ Δ : ctx} {A B : ty} (v : IntVar Δ B) (σ : tms Γ Δ) (t : tm Γ A) →
    makeVar (𝑠𝑣 v) ⟦ σ ⊕ t ⟧ ≡ makeVar v ⟦ σ ⟧
  𝑠𝑣⟦⟧ v σ t =
    makeVar (𝑠𝑣 v) ⟦ σ ⊕ t ⟧
      ≡⟨ ap _⟦ σ ⊕ t ⟧ (make𝑠𝑣 v) ⟩
    W₁tm _ (makeVar v) ⟦ σ ⊕ t ⟧
      ≡⟨ Wtm⟦⟧ (makeVar v) σ t ⟩
    makeVar v ⟦ σ ⟧
      ∎

  make[]𝑅 : {Γ Δ : ctx} {A : ty} (v : IntVar Δ A) (σ : IntRen Γ Δ) →
    makeVar (v [ σ ]𝑅) ≡ makeVar v ⟦ makeRen σ ⟧
  make[]𝑅 𝑧𝑣 (σ ⊕ t) = 𝑧⟦⟧ (makeRen (σ ⊕ t)) ⁻¹
  make[]𝑅 (𝑠𝑣 v) (σ ⊕ t) =
    makeVar (v [ σ ]𝑅)
      ≡⟨ make[]𝑅 v σ ⟩
    makeVar v ⟦ makeRen σ ⟧
      ≡⟨ 𝑠𝑣⟦⟧ v (makeRen σ) (makeVar t) ⁻¹ ⟩
    makeVar (𝑠𝑣 v) ⟦ makeRen (σ ⊕ t) ⟧
      ∎

  make∘𝑅𝑒𝑛 : {Γ Δ Σ : ctx} (σ : IntRen Δ Σ) (τ : IntRen Γ Δ) →
    makeRen (σ ∘𝑅𝑒𝑛 τ) ≡ makeRen σ ⊚ makeRen τ
  make∘𝑅𝑒𝑛 ! τ = refl
  make∘𝑅𝑒𝑛 (σ ⊕ v) τ i = make∘𝑅𝑒𝑛 σ τ i ⊕ make[]𝑅 v τ i

  𝒾𝒹η₂ : {Γ : ctx} → makeRen (id𝑅𝑒𝑛 Γ) ≡ 𝒾𝒹 Γ
  𝒾𝒹η₂ {Γ} = deriveId (𝒾𝒹 Γ)

  πη : {Γ : ctx} {A : ty} → makeRen (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) ≡ π
  πη {Γ} {A} =
    makeRen (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ))
      ≡⟨ makeW (id𝑅𝑒𝑛 Γ) ⟩
    W₁tms A (makeRen (id𝑅𝑒𝑛 Γ))
      ≡⟨ ap (W₁tms A) 𝒾𝒹η₂ ⟩
    𝒾𝒹 Γ ⊚ π
      ≡⟨ 𝒾𝒹L π ⟩
    π
      ∎

  -- Some transport lemmas
  transp𝒾𝒹 : {Δ Σ : ctx} (a : Δ ≡ Σ) →
    transport (λ i → tms (a i) (a i)) (𝒾𝒹 Δ) ≡ 𝒾𝒹 Σ
  transp𝒾𝒹 {Δ} {Σ} a =
    J (λ Σ a → transport (λ i → tms (a i) (a i)) (𝒾𝒹 Δ) ≡ 𝒾𝒹 Σ)
      (transportRefl (𝒾𝒹 Δ)) a

  transp⟦⟧ : {Γ₁ Γ₂ Δ₁ Δ₂ : ctx} {A : ty} (a : Γ₁ ≡ Γ₂)
    (b : Δ₁ ≡ Δ₂) (t : tm Δ₁ A) (σ : tms Γ₁ Δ₁) →
    transport (λ i → tm (a i) A) (t ⟦ σ ⟧)
      ≡ transport (λ i → tm (b i) A) t ⟦ transport (λ i → tms (a i) (b i)) σ ⟧
  transp⟦⟧ {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} a b t σ =
    J (λ Γ₂ a → transport (λ i → tm (a i) A) (t ⟦ σ ⟧)
      ≡ transport (λ i → tm (b i) A) t ⟦ transport (λ i → tms (a i) (b i)) σ ⟧)
      (J (λ Δ₂ b → transport (λ i → tm Γ₁ A) (t ⟦ σ ⟧) ≡
        transport (λ i → tm (b i) A) t ⟦ transport (λ i → tms Γ₁ (b i)) σ ⟧)
        (transportRefl (t ⟦ σ ⟧) ∙ (λ i → transportRefl t (~ i) ⟦ transportRefl σ (~ i) ⟧))
        b) a

𝑎𝑚𝑏Cat 𝒞 = Contextual.ambCat 𝒞
