{-# OPTIONS --cubical #-}

module contextual where

open import lists public

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Agda.Builtin.Char public

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

-- This new definition of a contextual category arose as a way to de-boilerplate the code;
-- it is the most natural variation of the definition to use in an implementation.

record Contextual (ℓ₁ ℓ₂ : Level) : Type (lsuc (ℓ₁ ⊔ ℓ₂))

𝑎𝑚𝑏Cat : Contextual ℓ₁ ℓ₂ → Precategory ℓ₁ (ℓ₁ ⊔ ℓ₂)
isCat𝐴𝑚𝑏Cat : (𝒞 : Contextual ℓ₁ ℓ₂) → isCategory (𝑎𝑚𝑏Cat 𝒞)

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
  σ ⊚ τ = map𝑇𝑚𝑠 _⟦ τ ⟧ σ

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
    σ ⊚ τ ⊚ μ ≡ σ ⊚ (τ ⊚ μ)
  ⊚Assoc ! τ μ = refl
  ⊚Assoc (σ ⊕ t) τ μ i = ⊚Assoc σ τ μ i ⊕ ⟦⟧⟦⟧ t τ μ i

  private
    module P = 𝑇𝑚𝑠Path tm isSetTm

  isSetTms = P.isSet𝑇𝑚𝑠

  -- Every contextual category has an ambient category of contexts and terms

  open Precategory hiding (_∘_)

  ambCat : Precategory ℓ₁ (ℓ₁ ⊔ ℓ₂)
  ob ambCat = ctx
  Hom[_,_] ambCat Γ Δ = tms Γ Δ
  Precategory.id ambCat Γ = 𝒾𝒹 Γ
  _⋆_ ambCat τ σ = σ ⊚ τ
  ⋆IdL ambCat = 𝒾𝒹R
  ⋆IdR ambCat = 𝒾𝒹L
  ⋆Assoc ambCat μ τ σ = ⊚Assoc σ τ μ ⁻¹

  isCatAmbCat : isCategory ambCat
  isSetHom isCatAmbCat = isSetTms

  -- ∅ is automatically the terminal object with unique morphism !

  !η : {Γ : ctx} (σ : tms Γ ∅) → ! ≡ σ
  !η ! = refl

  -- Contextual categories automatically have products

  π : {Γ : ctx} {A : ty} → tms (Γ ⊹ A) Γ
  π {Γ} {A} = π𝑇𝑚𝑠 (𝒾𝒹 (Γ ⊹ A))

  𝑧 : {Γ : ctx} {A : ty} → tm (Γ ⊹ A) A
  𝑧 {Γ} {A} = 𝑧𝑇𝑚𝑠 (𝒾𝒹 (Γ ⊹ A))

  𝒾𝒹η : {Γ : ctx} {A : ty} → π ⊕ 𝑧 ≡ 𝒾𝒹 (Γ ⊹ A) 
  𝒾𝒹η {Γ} {A} = π𝑧η𝑇𝑚𝑠 (𝒾𝒹 (Γ ⊹ A))

  π𝑧η : {Γ Δ : ctx} {A : ty} (σ : tms Γ (Δ ⊹ A)) →
    (π ⊚ σ) ⊕ (𝑧 ⟦ σ ⟧) ≡ σ
  π𝑧η {Γ} {Δ} {A} σ =
    π ⊚ σ ⊕ 𝑧 ⟦ σ ⟧
      ≡⟨ ap (_⊚ σ) 𝒾𝒹η ⟩
    𝒾𝒹 (Δ ⊹ A) ⊚ σ
      ≡⟨ 𝒾𝒹L σ ⟩
    σ
      ∎

  πβ : {Γ Δ : ctx} {A : ty} (σ : tms Γ (Δ ⊹ A)) →
    π ⊚ σ ≡ π𝑇𝑚𝑠 σ
  πβ σ = ap π𝑇𝑚𝑠 (π𝑧η σ)

  𝑧β : {Γ Δ : ctx} {A : ty} (σ : tms Γ (Δ ⊹ A)) →
    𝑧 ⟦ σ ⟧ ≡ 𝑧𝑇𝑚𝑠 σ
  𝑧β σ = ap 𝑧𝑇𝑚𝑠 (π𝑧η σ)

  -- The identity function includes with it a notion of internal variables

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

  REN : Precategory ℓ₁ ℓ₁
  REN = 𝑎𝑚𝑏Cat ρεν

  instance
    isCat𝑅𝑒𝑛 : isCategory REN
    isCat𝑅𝑒𝑛 = isCat𝐴𝑚𝑏Cat ρεν

  makeVar : {Γ : ctx} {A : ty} → IntVar Γ A → tm Γ A
  makeVar {Γ} = derive (𝒾𝒹 Γ)

  deriveRen : {Γ Δ Σ : ctx} → tms Γ Δ → IntRen Δ Σ → tms Γ Σ
  deriveRen σ = map𝑇𝑚𝑠 (derive σ)

  makeRen : {Γ Δ : ctx} → IntRen Γ Δ → tms Γ Δ
  makeRen {Γ} = deriveRen (𝒾𝒹 Γ)

  derive⟦⟧ : {Γ Δ Σ : ctx} {A : ty} (v : IntVar Σ A) (σ : tms Δ Σ) (τ : tms Γ Δ) →
    derive σ v ⟦ τ ⟧ ≡ derive (σ ⊚ τ) v
  derive⟦⟧ 𝑧𝑣 σ τ =
    𝑧𝑇𝑚𝑠 σ ⟦ τ ⟧
      ≡⟨ ap _⟦ τ ⟧ (𝑧β σ ⁻¹) ⟩
    𝑧 ⟦ σ ⟧ ⟦ τ ⟧
      ≡⟨ ⟦⟧⟦⟧ 𝑧 σ τ ⟩
    𝑧 ⟦ σ ⊚ τ ⟧
      ≡⟨ 𝑧β (σ ⊚ τ) ⟩
    𝑧𝑇𝑚𝑠 (σ ⊚ τ)
      ∎
  derive⟦⟧ (𝑠𝑣 v) σ τ =
    derive (π𝑇𝑚𝑠 σ) v ⟦ τ ⟧
      ≡⟨ (λ i → derive (πβ σ (~ i)) v ⟦ τ ⟧) ⟩
    derive (π ⊚ σ) v ⟦ τ ⟧
      ≡⟨ ap _⟦ τ ⟧ (derive⟦⟧ v π σ ⁻¹) ⟩
    derive π v ⟦ σ ⟧ ⟦ τ ⟧
      ≡⟨ ⟦⟧⟦⟧ (derive π v) σ τ ⟩
    derive π v ⟦ σ ⊚ τ ⟧
      ≡⟨ derive⟦⟧ v π (σ ⊚ τ) ⟩
    derive (π ⊚ (σ ⊚ τ)) v
      ≡⟨ (λ i → derive (πβ (σ ⊚ τ) i) v) ⟩
    derive (π𝑇𝑚𝑠 (σ ⊚ τ)) v
      ∎

  varβ : {Γ Δ : ctx} {A : ty} (v : IntVar Δ A) (σ : tms Γ Δ) →
    makeVar v ⟦ σ ⟧ ≡ derive σ v
  varβ {Γ} {Δ} v σ =
    derive (𝒾𝒹 Δ) v ⟦ σ ⟧
      ≡⟨ derive⟦⟧ v (𝒾𝒹 Δ) σ ⟩
    derive (𝒾𝒹 Δ ⊚ σ) v
      ≡⟨ (λ i → derive (𝒾𝒹L σ i) v) ⟩
    derive σ v
      ∎

  W₁tm : {Γ : ctx} (A : ty) {B : ty} → tm Γ B → tm (Γ ⊹ A) B
  W₁tm A t = t ⟦ π ⟧

  W₁tms : {Γ Δ : ctx} (A : ty) → tms Γ Δ → tms (Γ ⊹ A) Δ
  W₁tms A σ = σ ⊚ π

  W₂tms : {Γ Δ : ctx} (A : ty) → tms Γ Δ → tms (Γ ⊹ A) (Δ ⊹ A)
  W₂tms A σ = W₁tms A σ ⊕ 𝑧

  W₁lem1 : {Γ Δ : ctx} {A B : ty} (t : tm Δ B) (σ : tms Γ Δ) (s : tm Γ A) →
    W₁tm A t ⟦ σ ⊕ s ⟧ ≡ t ⟦ σ ⟧
  W₁lem1 t σ s =
    t ⟦ π ⟧ ⟦ σ ⊕ s ⟧
      ≡⟨ ⟦⟧⟦⟧ t π (σ ⊕ s) ⟩
    t ⟦ π ⊚ (σ ⊕ s) ⟧
      ≡⟨ ap (t ⟦_⟧) (πβ (σ ⊕ s)) ⟩
    t ⟦ σ ⟧
      ∎

  W₁lem2 : {Γ Δ Σ : ctx} {A : ty} (σ : tms Δ Σ) (τ : tms Γ Δ) (t : tm Γ A) →
    W₁tms A σ ⊚ (τ ⊕ t) ≡ σ ⊚ τ
  W₁lem2 ! τ t = refl
  W₁lem2 (σ ⊕ s) τ t i = W₁lem2 σ τ t i ⊕ W₁lem1 s τ t i

  make𝑠𝑣 : {Γ : ctx} {A B : ty} (v : IntVar Γ B) →
    makeVar (𝑠𝑣 v) ≡ W₁tm A (makeVar v)
  make𝑠𝑣 v = varβ v π ⁻¹

  makeW₁ : {Γ Δ : ctx} {A : ty} (σ : IntRen Γ Δ) →
    makeRen (W₁𝑅𝑒𝑛 A σ) ≡ W₁tms A (makeRen σ)
  makeW₁ ! = refl
  makeW₁ (σ ⊕ v) i = makeW₁ σ i ⊕ make𝑠𝑣 v i

  deriveW₁ : {Γ Δ Σ : ctx} {A : ty} (σ : tms Γ Δ) (t : tm Γ A) (v : IntRen Δ Σ) →
    deriveRen (σ ⊕ t) (W₁𝑅𝑒𝑛 A v) ≡ deriveRen σ v
  deriveW₁ σ t ! = refl
  deriveW₁ σ t (τ ⊕ v) i = deriveW₁ σ t τ i ⊕ derive σ v

  W₁⟦⟧ : {Γ Δ : ctx} {A B : ty} (v : IntVar Δ B) (σ : tms Γ Δ) (t : tm Γ A) →
    makeVar (𝑠𝑣 v) ⟦ σ ⊕ t ⟧ ≡ makeVar v ⟦ σ ⟧
  W₁⟦⟧ v σ t =
    makeVar (𝑠𝑣 v) ⟦ σ ⊕ t ⟧
      ≡⟨ ap _⟦ σ ⊕ t ⟧ (make𝑠𝑣 v) ⟩
    W₁tm _ (makeVar v) ⟦ σ ⊕ t ⟧
      ≡⟨ W₁lem1 (makeVar v) σ t ⟩
    makeVar v ⟦ σ ⟧
      ∎

  make[]𝑅 : {Γ Δ : ctx} {A : ty} (v : IntVar Δ A) (σ : IntRen Γ Δ) →
    makeVar (v [ σ ]𝑅) ≡ makeVar v ⟦ makeRen σ ⟧
  make[]𝑅 𝑧𝑣 (σ ⊕ t) = 𝑧β (makeRen (σ ⊕ t)) ⁻¹
  make[]𝑅 (𝑠𝑣 v) (σ ⊕ t) =
    makeVar (v [ σ ]𝑅)
      ≡⟨ make[]𝑅 v σ ⟩
    makeVar v ⟦ makeRen σ ⟧
      ≡⟨ W₁⟦⟧ v (makeRen σ) (makeVar t) ⁻¹ ⟩
    makeVar (𝑠𝑣 v) ⟦ makeRen (σ ⊕ t) ⟧
      ∎

  make∘𝑅𝑒𝑛 : {Γ Δ Σ : ctx} (σ : IntRen Δ Σ) (τ : IntRen Γ Δ) →
    makeRen (σ ∘𝑅𝑒𝑛 τ) ≡ makeRen σ ⊚ makeRen τ
  make∘𝑅𝑒𝑛 ! τ = refl
  make∘𝑅𝑒𝑛 (σ ⊕ v) τ i = make∘𝑅𝑒𝑛 σ τ i ⊕ make[]𝑅 v τ i

  -- Taking apart the variables and putting them back together does nothing

  derive𝒾𝒹 : {Γ Δ : ctx} (σ : tms Γ Δ) →
    deriveRen σ (id𝑅𝑒𝑛 Δ) ≡ σ
  derive𝒾𝒹 ! = refl
  derive𝒾𝒹 {Γ} {Δ ⊹ A} (σ ⊕ t) =
    deriveRen (σ ⊕ t) (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ)) ⊕ t
      ≡⟨ ap (_⊕ t) (deriveW₁ σ t (id𝑅𝑒𝑛 Δ)) ⟩
    deriveRen σ (id𝑅𝑒𝑛 Δ) ⊕ t
      ≡⟨ ap (_⊕ t) (derive𝒾𝒹 σ) ⟩
    σ ⊕ t
      ∎

  𝒾𝒹η₂ : {Γ : ctx} → makeRen (id𝑅𝑒𝑛 Γ) ≡ 𝒾𝒹 Γ
  𝒾𝒹η₂ {Γ} = derive𝒾𝒹 (𝒾𝒹 Γ)

  πη : {Γ : ctx} {A : ty} → makeRen (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) ≡ π
  πη {Γ} {A} =
    makeRen (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ))
      ≡⟨ makeW₁ (id𝑅𝑒𝑛 Γ) ⟩
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
isCat𝐴𝑚𝑏Cat 𝒞 = Contextual.isCatAmbCat 𝒞

module _ (𝒞 : Contextual ℓ₁ ℓ₂) where
  open Contextual 𝒞
  open Functor

  ιREN : Functor REN ambCat
  F-ob ιREN Γ = Γ
  F-hom ιREN σ = makeRen σ
  F-id ιREN = 𝒾𝒹η₂
  F-seq ιREN σ τ = make∘𝑅𝑒𝑛 τ σ

  private
    module R = Contextual ρεν

  makeRenVar : {Γ : ctx} {A : ty} (v : R.IntVar Γ A) → R.makeVar v ≡ v
  makeRenVar 𝑧𝑣 = refl
  makeRenVar {Γ ⊹ A} (𝑠𝑣 v) =
    derive (map𝑇𝑚𝑠 𝑠𝑣 (id𝑅𝑒𝑛 Γ)) v
      ≡⟨ deriveMap 𝑠𝑣 (id𝑅𝑒𝑛 Γ) v ⟩
    𝑠𝑣 (derive (id𝑅𝑒𝑛 Γ) v)
      ≡⟨ ap 𝑠𝑣 (makeRenVar v) ⟩
    𝑠𝑣 v
      ∎

-- The idea is that a contextual functor preserves the contextual structure

record ContextualFunctor (𝒞 : Contextual ℓ₁ ℓ₂) (𝒟 : Contextual ℓ₃ ℓ₄)
       : Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  open Contextual

  private
    module C = Contextual 𝒞
    module D = Contextual 𝒟
  
  field
    CF-ty : ty 𝒞 → ty 𝒟

  CF-ctx : ctx 𝒞 → ctx 𝒟
  CF-ctx Γ = map𝐶𝑡𝑥 CF-ty Γ

  field
    CF-tm : {Γ : ctx 𝒞} {A : ty 𝒞} → tm 𝒞 Γ A → tm 𝒟 (CF-ctx Γ) (CF-ty A)

  CF-tms : {Γ Δ : ctx 𝒞} → tms 𝒞 Γ Δ → tms 𝒟 (CF-ctx Γ) (CF-ctx Δ)
  CF-tms σ = map𝑇𝑚𝑠₁ CF-tm σ

  field
    CF-id : {Γ : ctx 𝒞} → CF-tms (𝒾𝒹 𝒞 Γ) ≡ 𝒾𝒹 𝒟 (CF-ctx Γ)
    CF-sub : {Γ Δ : ctx 𝒞} {A : ty 𝒞} (t : tm 𝒞 Δ A) (σ : tms 𝒞 Γ Δ) →
      CF-tm (t C.⟦ σ ⟧) ≡ CF-tm t D.⟦ CF-tms σ ⟧

  CF-comp : {Γ Δ Σ : ctx 𝒞} (σ : tms 𝒞 Δ Σ) (τ : tms 𝒞 Γ Δ) →
    CF-tms (σ C.⊚ τ) ≡ (CF-tms σ) D.⊚ (CF-tms τ)
  CF-comp ! τ = refl
  CF-comp (σ ⊕ t) τ i = CF-comp σ τ i ⊕ CF-sub t τ i

  CF-Var : {Γ : C.ctx} {A : C.ty} (v : C.IntVar Γ A) →
    CF-tm (C.makeVar v) ≡ D.makeVar (tr𝑉𝑎𝑟 CF-ty v)
  CF-Var {Γ} v =
    CF-tm (C.makeVar v)
      ≡⟨ deriveMap₁ CF-tm (C.𝒾𝒹 Γ) v ⁻¹ ⟩
    derive (CF-tms (C.𝒾𝒹 Γ)) (tr𝑉𝑎𝑟 CF-ty v)
      ≡⟨ (λ i → derive (CF-id i) (tr𝑉𝑎𝑟 CF-ty v)) ⟩
    D.makeVar (tr𝑉𝑎𝑟 CF-ty v)
      ∎

  transpCF-tm : {Γ : C.ctx} {A B : C.ty} (a : A ≡ B) (t : C.tm Γ A) →
    transport (λ i → D.tm (CF-ctx Γ) (CF-ty (a i))) (CF-tm t)
      ≡ CF-tm (transport (λ i → C.tm Γ (a i)) t)
  transpCF-tm {Γ} a t =
    J (λ B a → transport (λ i → D.tm (CF-ctx Γ) (CF-ty (a i))) (CF-tm t)
      ≡ CF-tm (transport (λ i → C.tm Γ (a i)) t))
      (transportRefl (CF-tm t) ∙ ap CF-tm (transportRefl t ⁻¹)) a

  open Functor

  -- A contextual functor induces a functor between the ambient categories

  ambFun : Functor (ambCat 𝒞) (ambCat 𝒟)
  F-ob ambFun = CF-ctx
  F-hom ambFun = CF-tms
  F-id ambFun = CF-id
  F-seq ambFun τ σ = CF-comp σ τ

open Contextual
open ContextualFunctor

-- We define the identity CF and composition of CFs

idCF : (𝒞 : Contextual ℓ₁ ℓ₂) → ContextualFunctor 𝒞 𝒞
CF-ty (idCF 𝒞) A = A
CF-tm (idCF 𝒞) {Γ} {A} t = transport (λ i → tm 𝒞 (map𝐶𝑡𝑥id Γ (~ i)) A) t
CF-id (idCF 𝒞) {Γ} =
  map𝑇𝑚𝑠₁ (λ {A} t → transport (λ i → tm 𝒞 (map𝐶𝑡𝑥id Γ (~ i)) A) t) (𝒾𝒹 𝒞 Γ)
    ≡⟨ map𝑇𝑚𝑠₁id (𝒾𝒹 𝒞 Γ) ⟩
  transport (λ i → 𝑇𝑚𝑠 (tm 𝒞) (map𝐶𝑡𝑥id Γ (~ i)) (map𝐶𝑡𝑥id Γ (~ i))) (𝒾𝒹 𝒞 Γ)
    ≡⟨ transp𝒾𝒹 𝒞 (map𝐶𝑡𝑥id Γ ⁻¹) ⟩
  𝒾𝒹 𝒞 (map𝐶𝑡𝑥 (λ A → A) Γ)
    ∎
CF-sub (idCF 𝒞) {Γ} {Δ} {A} t σ =
  transport (λ i → C.tm (map𝐶𝑡𝑥id Γ (~ i)) A) (t C.⟦ σ ⟧)
    ≡⟨ C.transp⟦⟧ (map𝐶𝑡𝑥id Γ ⁻¹) (map𝐶𝑡𝑥id Δ ⁻¹) t σ ⟩
  transport (λ i → C.tm (map𝐶𝑡𝑥id Δ (~ i)) A) t
    C.⟦ transport (λ i → C.tms (map𝐶𝑡𝑥id Γ (~ i)) (map𝐶𝑡𝑥id Δ (~ i))) σ ⟧
    ≡⟨ (λ i → transport (λ i → C.tm (map𝐶𝑡𝑥id Δ (~ i)) A) t C.⟦ map𝑇𝑚𝑠₁id σ (~ i) ⟧) ⟩
  transport (λ i → C.tm (map𝐶𝑡𝑥id Δ (~ i)) A) t
    C.⟦ map𝑇𝑚𝑠₁ (λ {B} → transport (λ i → C.tm (map𝐶𝑡𝑥id Γ (~ i)) B)) σ ⟧
    ∎ where
  module C = Contextual 𝒞

_∘CF_ : {𝒞 : Contextual ℓ₁ ℓ₂} {𝒟 : Contextual ℓ₃ ℓ₄} {ℰ : Contextual ℓ₅ ℓ₆} →
  ContextualFunctor 𝒟 ℰ → ContextualFunctor 𝒞 𝒟 → ContextualFunctor 𝒞 ℰ
CF-ty (G ∘CF F) = CF-ty G ∘ CF-ty F
CF-tm (_∘CF_ {ℰ = ℰ} G F) {Γ} {A} t  =
  transport (λ i → tm ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (CF-ty G (CF-ty F A)))
    (CF-tm G (CF-tm F t))
CF-id (_∘CF_ {𝒞 = 𝒞} {𝒟} {ℰ} G F) {Γ} =
  map𝑇𝑚𝑠₁ (CF-tm (G ∘CF F)) (𝒾𝒹 𝒞 Γ)
    ≡⟨ map𝑇𝑚𝑠comp₂ (λ {A} → transport (λ i → tm ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) A))
      (CF-tm G ∘ CF-tm F) (𝒾𝒹 𝒞 Γ) ⁻¹ ⟩
  map𝑇𝑚𝑠 (λ {A} → transport (λ i → tm ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) A))
    (map𝑇𝑚𝑠₁ (λ x → CF-tm G (CF-tm F x)) (𝒾𝒹 𝒞 Γ))
    ≡⟨ map𝑇𝑚𝑠comp₃ (CF-tm G) (CF-tm F) (𝒾𝒹 𝒞 Γ) ⟩
  transport (λ i → tms ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i))
    (CF-tms G (CF-tms F (𝒾𝒹 𝒞 Γ)))
    ≡⟨ (λ i → transport (λ i → tms ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i)
      (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i)) (CF-tms G (CF-id F i))) ⟩
  transport (λ i → tms ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i))
    (CF-tms G (𝒾𝒹 𝒟 (CF-ctx F Γ)))
    ≡⟨ (λ i → transport (λ i → tms ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i)
      (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i)) (CF-id G i)) ⟩
  transport (λ i → tms ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i))
    (𝒾𝒹 ℰ (CF-ctx G (CF-ctx F Γ)))
    ≡⟨ transp𝒾𝒹 ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ) ⟩
  𝒾𝒹 ℰ (map𝐶𝑡𝑥 (CF-ty G ∘ CF-ty F) Γ)
    ∎   
CF-sub (_∘CF_ {𝒞 = 𝒞} {𝒟} {ℰ} G F) {Γ} {Δ} {A} t σ =
  transport (λ i → tm ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (CF-ty G (CF-ty F A)))
    (CF-tm G (CF-tm F (t C.⟦ σ ⟧)))
    ≡⟨ (λ i → transport (λ i → tm ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (CF-ty G (CF-ty F A)))
      (CF-tm G (CF-sub F t σ i))) ⟩
  transport (λ i → tm ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (CF-ty G (CF-ty F A)))
    (CF-tm G (CF-tm F t D.⟦ CF-tms F σ ⟧))
    ≡⟨ (λ i → transport (λ i → tm ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (CF-ty G (CF-ty F A)))
      (CF-sub G (CF-tm F t) (CF-tms F σ) i)) ⟩
  transport (λ i → tm ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (CF-ty G (CF-ty F A)))
    (CF-tm G (CF-tm F t) E.⟦ CF-tms G (CF-tms F σ) ⟧)
    ≡⟨ E.transp⟦⟧ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ) (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Δ)
      (CF-tm G (CF-tm F t)) (CF-tms G (CF-tms F σ)) ⟩
  transport (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Δ i) (CF-ty G (CF-ty F A)))
    (CF-tm G (CF-tm F t)) E.⟦ transport (λ i → E.tms (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i)
      (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Δ i)) (CF-tms G (CF-tms F σ)) ⟧
    ≡⟨ (λ i → transport (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Δ i) (CF-ty G (CF-ty F A)))
      (CF-tm G (CF-tm F t)) E.⟦ map𝑇𝑚𝑠comp₃ (CF-tm G) (CF-tm F) σ (~ i) ⟧) ⟩
  transport (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Δ i) (CF-ty G (CF-ty F A)))
    (CF-tm G (CF-tm F t)) E.⟦ map𝑇𝑚𝑠 (λ {B} → transport
      (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) B)) (map𝑇𝑚𝑠₁ (CF-tm G ∘ CF-tm F) σ) ⟧
    ≡⟨ (λ i → transport (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Δ i) (CF-ty G (CF-ty F A)))
      (CF-tm G (CF-tm F t)) E.⟦ map𝑇𝑚𝑠comp₂ {tm₂ = E.tm} (λ {B} → transport
        (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) B)) (CF-tm G ∘ CF-tm F) σ i ⟧) ⟩
  transport (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Δ i) (CF-ty G (CF-ty F A)))
    (CF-tm G (CF-tm F t)) E.⟦ map𝑇𝑚𝑠₁ (λ {B} s → transport 
      (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (CF-ty G (CF-ty F B)))
      (CF-tm G (CF-tm F s))) σ ⟧
    ∎ where
    module C = Contextual 𝒞
    module D = Contextual 𝒟
    module E = Contextual ℰ
