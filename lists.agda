{-# OPTIONS --cubical #-}

module lists where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything renaming (cong to ap) public
open import Cubical.Data.Sigma
open import Cubical.Data.Unit as ⊤ renaming (Unit to ⊤)

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

-- We define the basic data structures used to build contextual categories.

-- 𝐶𝑡𝑥 is a (reversed) list former
infixl 20 _⊹_
data 𝐶𝑡𝑥 (ty : Type ℓ) : Type ℓ where
  ∅ : 𝐶𝑡𝑥 ty
  _⊹_ : 𝐶𝑡𝑥 ty → ty → 𝐶𝑡𝑥 ty

map𝐶𝑡𝑥 : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} (f : ty₁ → ty₂) (Γ : 𝐶𝑡𝑥 ty₁) → 𝐶𝑡𝑥 ty₂
map𝐶𝑡𝑥 f ∅ = ∅
map𝐶𝑡𝑥 f (Γ ⊹ A) = map𝐶𝑡𝑥 f Γ ⊹ f A

-- 𝑇𝑚𝑠 forms indexed lists representing substitutions (terms of given types in a common context)
infixl 20 _⊕_
data 𝑇𝑚𝑠 {ty : Type ℓ₁} (tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂)
     : (Γ Δ : 𝐶𝑡𝑥 ty) → Type (ℓ₁ ⊔ ℓ₂) where
  ! : {Γ : 𝐶𝑡𝑥 ty} → 𝑇𝑚𝑠 tm Γ ∅
  _⊕_ : {Γ Δ : 𝐶𝑡𝑥 ty} {A : ty} → 𝑇𝑚𝑠 tm Γ Δ → tm Γ A → 𝑇𝑚𝑠 tm Γ (Δ ⊹ A)

map𝑇𝑚𝑠 : {ty : Type ℓ₁} {Γ₁ Γ₂ Δ : 𝐶𝑡𝑥 ty} {tm₁ : 𝐶𝑡𝑥 ty → ty → Type ℓ₂}
  {tm₂ : 𝐶𝑡𝑥 ty → ty → Type ℓ₃} (f : {A : ty} → tm₁ Γ₁ A → tm₂ Γ₂ A)
  (σ : 𝑇𝑚𝑠 tm₁ Γ₁ Δ) → 𝑇𝑚𝑠 tm₂ Γ₂ Δ
map𝑇𝑚𝑠 f ! = !
map𝑇𝑚𝑠 f (σ ⊕ t) = map𝑇𝑚𝑠 f σ ⊕ f t

π𝑇𝑚𝑠 : {ty : Type ℓ₁} {tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂} {Γ Δ : 𝐶𝑡𝑥 ty} {A : ty}
  → 𝑇𝑚𝑠 tm Γ (Δ ⊹ A) → 𝑇𝑚𝑠 tm Γ Δ
π𝑇𝑚𝑠 (σ ⊕ t) = σ

𝑧𝑇𝑚𝑠 : {ty : Type ℓ₁} {tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂} {Γ Δ : 𝐶𝑡𝑥 ty} {A : ty}
  → 𝑇𝑚𝑠 tm Γ (Δ ⊹ A) → tm Γ A
𝑧𝑇𝑚𝑠 (σ ⊕ t) = t

π𝑧η𝑇𝑚𝑠 : {ty : Type ℓ₁} {tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂} {Γ Δ : 𝐶𝑡𝑥 ty} {A : ty}
  (σ : 𝑇𝑚𝑠 tm Γ (Δ ⊹ A)) → (π𝑇𝑚𝑠 σ) ⊕ (𝑧𝑇𝑚𝑠 σ) ≡ σ
π𝑧η𝑇𝑚𝑠 (σ ⊕ t) = refl

-- This version is sometimes harder to use since the target context is defined recursively,
-- while the previous version, on the other hand, has target Δ definitionally.
map𝑇𝑚𝑠₁ : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} {tm₁ : 𝐶𝑡𝑥 ty₁ → ty₁ → Type ℓ₃}
  {tm₂ : 𝐶𝑡𝑥 ty₂ → ty₂ → Type ℓ₄} {Γ₁ Δ : 𝐶𝑡𝑥 ty₁} {Γ₂ : 𝐶𝑡𝑥 ty₂} {P : ty₁ → ty₂}
  (f : {A : ty₁} → tm₁ Γ₁ A → tm₂ Γ₂ (P A)) → 𝑇𝑚𝑠 tm₁ Γ₁ Δ → 𝑇𝑚𝑠 tm₂ Γ₂ (map𝐶𝑡𝑥 P Δ)
map𝑇𝑚𝑠₁ f ! = !
map𝑇𝑚𝑠₁ f (σ ⊕ t) = map𝑇𝑚𝑠₁ f σ ⊕ f t

map𝑇𝑚𝑠comp : {ty : Type ℓ₁} {tm₁ : 𝐶𝑡𝑥 ty → ty → Type ℓ₂} {tm₂ : 𝐶𝑡𝑥 ty → ty → Type ℓ₃}
  {tm₃ : 𝐶𝑡𝑥 ty → ty → Type ℓ₄} {Γ₁ Γ₂ Γ₃ Δ : 𝐶𝑡𝑥 ty} (f : {A : ty} → tm₂ Γ₂ A → tm₃ Γ₃ A)
  (g : {A : ty} → tm₁ Γ₁ A → tm₂ Γ₂ A) (σ : 𝑇𝑚𝑠 tm₁ Γ₁ Δ) →
  map𝑇𝑚𝑠 {tm₁ = tm₂} {tm₂ = tm₃} f (map𝑇𝑚𝑠 g σ) ≡ map𝑇𝑚𝑠 (f ∘ g) σ
map𝑇𝑚𝑠comp f g ! = refl
map𝑇𝑚𝑠comp {tm₂ = tm₂} {Γ₂ = Γ₂} f g (σ ⊕ t) i =
  map𝑇𝑚𝑠comp {tm₂ = tm₂} {Γ₂ = Γ₂} f g σ i ⊕ f (g t)

map𝑇𝑚𝑠comp₁ : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} {tm₁ : 𝐶𝑡𝑥 ty₁ → ty₁ → Type ℓ₃}
  {tm₂ : 𝐶𝑡𝑥 ty₁ → ty₁ → Type ℓ₄} {tm₃ : 𝐶𝑡𝑥 ty₂ → ty₂ → Type ℓ₅} {Γ₁ Γ₂ Δ : 𝐶𝑡𝑥 ty₁}
  {Γ₃ : 𝐶𝑡𝑥 ty₂} {P : ty₁ → ty₂} (f : {A : ty₁} → tm₂ Γ₂ A → tm₃ Γ₃ (P A))
  (g : {A : ty₁} → tm₁ Γ₁ A → tm₂ Γ₂ A)  (σ : 𝑇𝑚𝑠 tm₁ Γ₁ Δ) →
  map𝑇𝑚𝑠₁ {tm₁ = tm₂} {tm₂ = tm₃} f (map𝑇𝑚𝑠 g σ) ≡ map𝑇𝑚𝑠₁ (f ∘ g) σ
map𝑇𝑚𝑠comp₁ f g ! = refl
map𝑇𝑚𝑠comp₁ {tm₂ = tm₂} {Γ₂ = Γ₂} f g (σ ⊕ t) i =
  map𝑇𝑚𝑠comp₁ {tm₂ = tm₂} {Γ₂ = Γ₂} f g σ i ⊕ f (g t)

map𝑇𝑚𝑠comp₂ : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} {tm₁ : 𝐶𝑡𝑥 ty₁ → ty₁ → Type ℓ₃}
  {tm₂ : 𝐶𝑡𝑥 ty₂ → ty₂ → Type ℓ₄} {tm₃ : 𝐶𝑡𝑥 ty₂ → ty₂ → Type ℓ₅} {Γ₁ Δ : 𝐶𝑡𝑥 ty₁}
  {Γ₂ Γ₃ : 𝐶𝑡𝑥 ty₂} {P : ty₁ → ty₂} (f : {A : ty₂} → tm₂ Γ₂ A → tm₃ Γ₃ A)
  (g : {A : ty₁} → tm₁ Γ₁ A → tm₂ Γ₂ (P A))  (σ : 𝑇𝑚𝑠 tm₁ Γ₁ Δ) →
  map𝑇𝑚𝑠 {tm₁ = tm₂} {tm₂ = tm₃} f (map𝑇𝑚𝑠₁ g σ) ≡ map𝑇𝑚𝑠₁ (f ∘ g) σ
map𝑇𝑚𝑠comp₂ f g ! = refl
map𝑇𝑚𝑠comp₂ {tm₂ = tm₂} {Γ₂ = Γ₂} f g (σ ⊕ t) i =
  map𝑇𝑚𝑠comp₂ {tm₂ = tm₂} {Γ₂ = Γ₂} f g σ i ⊕ f (g t)

{-map𝑇𝑚𝑠comp₃ : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} {ty₃ : Type ℓ₃} {tm₁ : 𝐶𝑡𝑥 ty₁ → ty₁ → Type ℓ₄}
  {tm₂ : 𝐶𝑡𝑥 ty₂ → ty₂ → Type ℓ₅} {tm₃ : 𝐶𝑡𝑥 ty₃ → ty₃ → Type ℓ₆} {Γ₁ Δ : 𝐶𝑡𝑥 ty₁}
  {Γ₂ : 𝐶𝑡𝑥 ty₂} {Γ₃ : 𝐶𝑡𝑥 ty₃} {P : ty₂ → ty₃} (f : {A : ty₂} → tm₂ Γ₂ A → tm₃ Γ₃ (P A))
  {Q : ty₁ → ty₂} (g : {A : ty₁} → tm₁ Γ₁ A → tm₂ Γ₂ (Q A)) (σ : 𝑇𝑚𝑠 tm₁ Γ₁ Δ) →
  map𝑇𝑚𝑠₁ {tm₁ = tm₂} {tm₂ = tm₃} f (map𝑇𝑚𝑠₁ g σ) ≡ {!map𝑇𝑚𝑠₁ {tm₁ = tm₁} {tm₂ = tm₃} {P = P ∘ Q} (f ∘ g) σ!}
map𝑇𝑚𝑠comp₃ f g ! = refl
map𝑇𝑚𝑠comp₃ {tm₂ = tm₂} {Γ₂ = Γ₂} f g (σ ⊕ t) i =
  map𝑇𝑚𝑠comp₃ {tm₂ = tm₂} {Γ₂ = Γ₂} f g σ i ⊕ f (g t)-}

-- Variables
data 𝑉𝑎𝑟 (ty : Type ℓ) : (Γ : 𝐶𝑡𝑥 ty) (A : ty) → Type ℓ where
  𝑧𝑣 : {Γ : 𝐶𝑡𝑥 ty} {A : ty} → 𝑉𝑎𝑟 ty (Γ ⊹ A) A
  𝑠𝑣 : {Γ : 𝐶𝑡𝑥 ty} {A B : ty} → 𝑉𝑎𝑟 ty Γ A → 𝑉𝑎𝑟 ty (Γ ⊹ B) A

𝑅𝑒𝑛 : (ty : Type ℓ) → 𝐶𝑡𝑥 ty → 𝐶𝑡𝑥 ty → Type ℓ
𝑅𝑒𝑛 ty = 𝑇𝑚𝑠 (𝑉𝑎𝑟 ty)

module _ {ty : Type ℓ} where
  private
    ctx = 𝐶𝑡𝑥 ty
  
  W₁𝑅𝑒𝑛 : {Γ Δ : ctx} {A : ty} → 𝑅𝑒𝑛 ty Γ Δ → 𝑅𝑒𝑛 ty (Γ ⊹ A) Δ
  W₁𝑅𝑒𝑛 = map𝑇𝑚𝑠 𝑠𝑣

  W₂𝑅𝑒𝑛 : {Γ Δ : ctx} {A : ty} → 𝑅𝑒𝑛 ty Γ Δ → 𝑅𝑒𝑛 ty (Γ ⊹ A) (Δ ⊹ A)
  W₂𝑅𝑒𝑛 σ = W₁𝑅𝑒𝑛 σ ⊕ 𝑧𝑣

  id𝑅𝑒𝑛 : (Γ : ctx) → 𝑅𝑒𝑛 ty Γ Γ
  id𝑅𝑒𝑛 ∅ = !
  id𝑅𝑒𝑛 (Γ ⊹ A) = W₂𝑅𝑒𝑛 (id𝑅𝑒𝑛 Γ)

tr𝑉𝑎𝑟 : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} (f : ty₁ → ty₂) {Γ : 𝐶𝑡𝑥 ty₁} {A : ty₁}
  → 𝑉𝑎𝑟 ty₁ Γ A → 𝑉𝑎𝑟 ty₂ (map𝐶𝑡𝑥 f Γ) (f A)
tr𝑉𝑎𝑟 f 𝑧𝑣 = 𝑧𝑣
tr𝑉𝑎𝑟 f (𝑠𝑣 v) = 𝑠𝑣 (tr𝑉𝑎𝑟 f v)

tr𝑅𝑒𝑛 : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} (f : ty₁ → ty₂) {Γ Δ : 𝐶𝑡𝑥 ty₁}
  → 𝑅𝑒𝑛 ty₁ Γ Δ → 𝑅𝑒𝑛 ty₂ (map𝐶𝑡𝑥 f Γ) (map𝐶𝑡𝑥 f Δ)
tr𝑅𝑒𝑛 f = map𝑇𝑚𝑠₁ (tr𝑉𝑎𝑟 f)

trId : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} (f : ty₁ → ty₂) (Γ : 𝐶𝑡𝑥 ty₁) →
  tr𝑅𝑒𝑛 f (id𝑅𝑒𝑛 Γ) ≡ id𝑅𝑒𝑛 (map𝐶𝑡𝑥 f Γ)
trId f ∅ = refl
trId f (Γ ⊹ A) =
  map𝑇𝑚𝑠₁ (tr𝑉𝑎𝑟 f) (map𝑇𝑚𝑠 𝑠𝑣 (id𝑅𝑒𝑛 Γ)) ⊕ 𝑧𝑣
    ≡⟨ ap (_⊕ 𝑧𝑣) (map𝑇𝑚𝑠comp₁ (tr𝑉𝑎𝑟 f) 𝑠𝑣 (id𝑅𝑒𝑛 Γ)) ⟩
  map𝑇𝑚𝑠₁ (𝑠𝑣 ∘ (tr𝑉𝑎𝑟 f)) (id𝑅𝑒𝑛 Γ) ⊕ 𝑧𝑣
    ≡⟨ ap (_⊕ 𝑧𝑣) (map𝑇𝑚𝑠comp₂ 𝑠𝑣 (tr𝑉𝑎𝑟 f) (id𝑅𝑒𝑛 Γ) ⁻¹) ⟩
  W₂𝑅𝑒𝑛 (tr𝑅𝑒𝑛 f (id𝑅𝑒𝑛 Γ))
    ≡⟨ ap W₂𝑅𝑒𝑛 (trId f Γ) ⟩
  W₂𝑅𝑒𝑛 (id𝑅𝑒𝑛 (map𝐶𝑡𝑥 f Γ))
    ∎

-- Proofs that things are sets

-- We prove that if tm is a set, then 𝑇𝑚𝑠 tm is a set;
-- this is mostly taken from the stdlib treatment of lists.

module 𝑇𝑚𝑠Path {ty : Type ℓ₁} (tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂)
       (isSetTm : {Γ : 𝐶𝑡𝑥 ty} {A : ty} → isSet (tm Γ A)) where

  ctx = 𝐶𝑡𝑥 ty
  tms = 𝑇𝑚𝑠 tm

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
