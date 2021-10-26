{-# OPTIONS --cubical #-}

module contextual where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything renaming (cong to ap) public
open import Cubical.Data.Sigma
open import Cubical.Data.Unit as ⊤ renaming (Unit to ⊤)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

-- First we define the basic data structures used to build contextual categories

-- Reversed List
infixl 20 _⊹_
data RL (ty : Type ℓ) : Type ℓ where
  ∅ : RL ty
  _⊹_ : RL ty → ty → RL ty

mapRL : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} (f : ty₁ → ty₂) (Γ : RL ty₁) → RL ty₂
mapRL f ∅ = ∅
mapRL f (Γ ⊹ A) = mapRL f Γ ⊹ f A

-- Indexed List
infixl 20 _⊕_
data IL {ty : Type ℓ₁} (tm : RL ty → ty → Type ℓ₂)
     : (Γ Δ : RL ty) → Type (ℓ₁ ⊔ ℓ₂) where
  ! : {Γ : RL ty} → IL tm Γ ∅
  _⊕_ : {Γ Δ : RL ty} {A : ty} → IL tm Γ Δ → tm Γ A → IL tm Γ (Δ ⊹ A)

mapIL : {ty : Type ℓ₁} {Γ₁ Γ₂ Δ : RL ty} {tm₁ : RL ty → ty → Type ℓ₂} {tm₂ : RL ty → ty → Type ℓ₃}
  (f : {A : ty} → tm₁ Γ₁ A → tm₂ Γ₂ A) (σ : IL tm₁ Γ₁ Δ) → IL tm₂ Γ₂ Δ
mapIL f ! = !
mapIL f (σ ⊕ t) = mapIL f σ ⊕ f t

-- This version is sometimes harder to use since the target context is defined recursively
mapIL₁ : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} {tm₁ : RL ty₁ → ty₁ → Type ℓ₃}
  {tm₂ : RL ty₂ → ty₂ → Type ℓ₄} {Γ₁ Δ : RL ty₁} {Γ₂ : RL ty₂} {P : ty₁ → ty₂}
  (f : {A : ty₁} → tm₁ Γ₁ A → tm₂ Γ₂ (P A)) → IL tm₁ Γ₁ Δ → IL tm₂ Γ₂ (mapRL P Δ)
mapIL₁ f ! = !
mapIL₁ f (σ ⊕ t) = mapIL₁ f σ ⊕ f t

-- We prove that if tm is a set, then IL tm is a set

module ILPath {ty : Type ℓ₁} (tm : RL ty → ty → Type ℓ₂)
       (isSetTm : {Γ : RL ty} {A : ty} → isSet (tm Γ A)) where

  ctx = RL ty
  tms = IL tm

  isPropLift : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → isProp A → isProp (Lift {ℓ₁} {ℓ₂} A)
  isPropLift p (lift x) (lift y) = ap lift (p x y)

  Code : {Γ Δ : ctx} → tms Γ Δ → tms Γ Δ → Type ℓ₂
  Code ! ! = Lift ⊤
  Code (σ ⊕ t) (τ ⊕ s) = (t ≡ s) × Code σ τ

  reflCode : {Γ Δ : ctx} (σ : tms Γ Δ) → Code σ σ
  reflCode ! = lift tt
  reflCode (σ ⊕ t) = refl , reflCode σ

  encode : {Γ Δ : ctx} (σ τ : tms Γ Δ) → σ ≡ τ → Code σ τ
  encode σ τ = J (λ μ _ → Code σ μ) (reflCode σ)

  encodeRefl : {Γ Δ : ctx} (σ : tms Γ Δ) → encode σ σ refl ≡ reflCode σ
  encodeRefl σ = JRefl (λ τ _ → Code σ τ) (reflCode σ)

  decode : {Γ Δ : ctx} (σ τ : tms Γ Δ) → Code σ τ → σ ≡ τ
  decode ! ! x = refl
  decode (σ ⊕ t) (τ ⊕ s) (p , q) i = decode σ τ q i ⊕ p i

  decodeRefl : {Γ Δ : ctx} (σ : tms Γ Δ) → decode σ σ (reflCode σ) ≡ refl
  decodeRefl ! = refl
  decodeRefl (σ ⊕ t) = ap (ap (_⊕ t)) (decodeRefl σ)

  decodeEncode : {Γ Δ : ctx} (σ τ : tms Γ Δ) (p : σ ≡ τ) → decode σ τ (encode σ τ p) ≡ p
  decodeEncode σ τ =
    J (λ μ q → decode σ μ (encode σ μ q) ≡ q)
      (ap (decode σ σ) (encodeRefl σ) ∙ decodeRefl σ)

  isPropCode : {Γ Δ : ctx} (σ τ : tms Γ Δ) → isProp (Code σ τ)
  isPropCode ! ! = isPropLift isPropUnit
  isPropCode (σ ⊕ t) (τ ⊕ s) = isPropΣ (isSetTm t s) (λ _ → isPropCode σ τ)

  isSetTms : {Γ Δ : ctx} → isSet (tms Γ Δ)
  isSetTms σ τ =
    isOfHLevelRetract 1
      (encode σ τ)
      (decode σ τ)
      (decodeEncode σ τ)
      (isPropCode σ τ)

-- Now onto the fundemental definitions

record Contextual (ℓ₁ ℓ₂ : Level) : Type (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    ty : Type ℓ₁
    
  ctx = RL ty
  
  field
    tm : ctx → ty → Type ℓ₂

  tms = IL tm

  infixl 30 _⟦_⟧
  field
    _⟦_⟧ : {Γ Δ : ctx} {A : ty} → tm Δ A → tms Γ Δ → tm Γ A

  infixl 20 _⊚_
  _⊚_ : {Γ Δ Σ : ctx} → tms Δ Σ → tms Γ Δ → tms Γ Σ
  σ ⊚ τ = mapIL _⟦ τ ⟧ σ

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
    module P = ILPath tm isSetTm

  isSetTms = P.isSetTms

  open Precategory

  ambCat : Precategory ℓ₁ (ℓ₁ ⊔ ℓ₂)
  ob ambCat = ctx
  Hom[_,_] ambCat Γ Δ = tms Γ Δ
  Precategory.id ambCat Γ = 𝒾𝒹 Γ
  _⋆_ ambCat τ σ = σ ⊚ τ
  ⋆IdL ambCat = 𝒾𝒹R
  ⋆IdR ambCat = 𝒾𝒹L
  ⋆Assoc ambCat μ τ σ = ⊚Assoc σ τ μ ⁻¹

record ContextualFunctor (𝒞 : Contextual ℓ₁ ℓ₂) (𝒟 : Contextual ℓ₃ ℓ₄)
       : Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  open Contextual

  private
    module C = Contextual 𝒞
    module D = Contextual 𝒟
  
  field
    CF-ty : ty 𝒞 → ty 𝒟

  CF-ctx : ctx 𝒞 → ctx 𝒟
  CF-ctx Γ = mapRL CF-ty Γ

  field
    CF-tm : {Γ : ctx 𝒞} {A : ty 𝒞} → tm 𝒞 Γ A → tm 𝒟 (CF-ctx Γ) (CF-ty A)

  CF-tms : {Γ Δ : ctx 𝒞} → tms 𝒞 Γ Δ → tms 𝒟 (CF-ctx Γ) (CF-ctx Δ)
  CF-tms σ = mapIL₁ CF-tm σ

  field
    CF-id : {Γ : ctx 𝒞} → CF-tms (𝒾𝒹 𝒞 Γ) ≡ 𝒾𝒹 𝒟 (CF-ctx Γ)
    CF-sub : {Γ Δ : ctx 𝒞} {A : ty 𝒞} (t : tm 𝒞 Δ A) (σ : tms 𝒞 Γ Δ) →
      CF-tm (t C.⟦ σ ⟧) ≡ CF-tm t D.⟦ CF-tms σ ⟧

  CF-comp : {Γ Δ Σ : ctx 𝒞} (σ : tms 𝒞 Δ Σ) (τ : tms 𝒞 Γ Δ) →
    CF-tms (σ C.⊚ τ) ≡ (CF-tms σ) D.⊚ (CF-tms τ)
  CF-comp ! τ = refl
  CF-comp (σ ⊕ t) τ i = CF-comp σ τ i ⊕ CF-sub t τ i

  open Functor

  ambFun : Functor (ambCat 𝒞) (ambCat 𝒟)
  F-ob ambFun = CF-ctx
  F-hom ambFun = CF-tms
  F-id ambFun = CF-id
  F-seq ambFun τ σ = CF-comp σ τ
