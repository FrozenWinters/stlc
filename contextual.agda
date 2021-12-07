{-# OPTIONS --cubical #-}

module contextual where

open import lists public

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Agda.Builtin.Char public

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

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

  derive : {Γ Δ : ctx} {A : ty} → tms Γ Δ → IntVar Δ A → tm Γ A
  derive σ 𝑧𝑣 = 𝑧𝑇𝑚𝑠 σ
  derive σ (𝑠𝑣 v) = derive (π𝑇𝑚𝑠 σ) v

  makeVar : {Γ : ctx} {A : ty} → IntVar Γ A → tm Γ A
  makeVar {Γ} = derive (𝒾𝒹 Γ)

  deriveRen : {Γ Δ Σ : ctx} → tms Γ Δ → IntRen Δ Σ → tms Γ Σ
  deriveRen σ = map𝑇𝑚𝑠 (derive σ)

  makeRen : {Γ Δ : ctx} → IntRen Γ Δ → tms Γ Δ
  makeRen {Γ} = deriveRen (𝒾𝒹 Γ)

  deriveMap : {Γ Δ Σ : ctx} (f : {A : ty} → tm Γ A → tm Δ A) (σ : tms Γ Σ) {A : ty}
    (v : IntVar Σ A) → derive (map𝑇𝑚𝑠 f σ) v ≡ f (derive σ v)
  deriveMap f (σ ⊕ t) 𝑧𝑣 = refl
  deriveMap f (σ ⊕ t) (𝑠𝑣 v) = deriveMap f σ v

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
    makeVar v ⟦ π ⟧ ⟦ σ ⊕ t ⟧
      ≡⟨ ⟦⟧⟦⟧ (makeVar v) π (σ ⊕ t) ⟩
    makeVar v ⟦ π ⊚ (σ ⊕ t) ⟧
      ≡⟨ ap (makeVar v ⟦_⟧) (πβ (σ ⊕ t)) ⟩
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

  open Functor

  -- A contextual functor induces a functor between the ambient categories

  ambFun : Functor (ambCat 𝒞) (ambCat 𝒟)
  F-ob ambFun = CF-ctx
  F-hom ambFun = CF-tms
  F-id ambFun = CF-id
  F-seq ambFun τ σ = CF-comp σ τ
