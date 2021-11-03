{-# OPTIONS --cubical #-}

module lists where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything renaming (cong to ap) public
open import Cubical.Data.Sigma
open import Cubical.Data.Unit as ⊤ renaming (Unit to ⊤)

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

-- We define the basic data structures used to build contextual categories.

-- Reversed List
infixl 20 _⊹_
data RL (ty : Type ℓ) : Type ℓ where
  ∅ : RL ty
  _⊹_ : RL ty → ty → RL ty

mapRL : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} (f : ty₁ → ty₂) (Γ : RL ty₁) → RL ty₂
mapRL f ∅ = ∅
mapRL f (Γ ⊹ A) = mapRL f Γ ⊹ f A

mapRLid : {ty : Type ℓ} (Γ : RL ty) → mapRL (λ A → A) Γ ≡ Γ
mapRLid ∅ = refl
mapRLid (Γ ⊹ A) i = mapRLid Γ i ⊹ A

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

πIL : {ty : Type ℓ₁} {tm : RL ty → ty → Type ℓ₂} {Γ Δ : RL ty} {A : ty}
  → IL tm Γ (Δ ⊹ A) → IL tm Γ Δ
πIL (σ ⊕ t) = σ

𝑧IL : {ty : Type ℓ₁} {tm : RL ty → ty → Type ℓ₂} {Γ Δ : RL ty} {A : ty}
  → IL tm Γ (Δ ⊹ A) → tm Γ A
𝑧IL (σ ⊕ t) = t

π𝑧ηIL : {ty : Type ℓ₁} {tm : RL ty → ty → Type ℓ₂} {Γ Δ : RL ty} {A : ty}
  (σ : IL tm Γ (Δ ⊹ A)) → (πIL σ) ⊕ (𝑧IL σ) ≡ σ
π𝑧ηIL (σ ⊕ t) = refl

-- This version is sometimes harder to use since the target context is defined recursively,
-- while the previous version, on the other hand, has target Δ definitionally.
mapIL₁ : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} {tm₁ : RL ty₁ → ty₁ → Type ℓ₃}
  {tm₂ : RL ty₂ → ty₂ → Type ℓ₄} {Γ₁ Δ : RL ty₁} {Γ₂ : RL ty₂} {P : ty₁ → ty₂}
  (f : {A : ty₁} → tm₁ Γ₁ A → tm₂ Γ₂ (P A)) → IL tm₁ Γ₁ Δ → IL tm₂ Γ₂ (mapRL P Δ)
mapIL₁ f ! = !
mapIL₁ f (σ ⊕ t) = mapIL₁ f σ ⊕ f t

-- We prove that if tm is a set, then IL tm is a set;
-- this is mostly taken from the stdlib treatment of lists.

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
