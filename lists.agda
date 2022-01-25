{-# OPTIONS --cubical --allow-unsolved-metas #-}

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

map𝐶𝑡𝑥id : {ty : Type ℓ} (Γ : 𝐶𝑡𝑥 ty) → map𝐶𝑡𝑥 (λ A → A) Γ ≡ Γ
map𝐶𝑡𝑥id ∅ = refl
map𝐶𝑡𝑥id (Γ ⊹ A) i = map𝐶𝑡𝑥id Γ i ⊹ A

map𝐶𝑡𝑥comp : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} {ty₃ : Type ℓ₃} (g : ty₂ → ty₃) (f : ty₁ → ty₂)
  (Γ : 𝐶𝑡𝑥 ty₁) → map𝐶𝑡𝑥 g (map𝐶𝑡𝑥 f Γ) ≡ map𝐶𝑡𝑥 (g ∘ f) Γ
map𝐶𝑡𝑥comp g f ∅ = refl
map𝐶𝑡𝑥comp g f (Γ ⊹ A) i = map𝐶𝑡𝑥comp g f Γ i ⊹ g (f A)

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

transport⊕ : {ty : Type ℓ₁} {tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂} {Γ Δ Σ Ω : 𝐶𝑡𝑥 ty} {A : ty}
  (a : Γ ≡ Δ) (b : Σ ≡ Ω) (σ : 𝑇𝑚𝑠 tm Γ Σ) (t : tm Γ A) →
  transport (λ i → 𝑇𝑚𝑠 tm (a i) (b i ⊹ A)) (σ ⊕ t)
    ≡ transport (λ i → 𝑇𝑚𝑠 tm (a i) (b i)) σ ⊕ transport (λ i → tm (a i) A) t
transport⊕ {tm = tm} {Γ} {Δ} {Σ} {Ω} {A} a b σ t =
  J (λ Δ a → transport (λ i → 𝑇𝑚𝑠 tm (a i) (b i ⊹ A)) (σ ⊕ t)
    ≡ transport (λ i → 𝑇𝑚𝑠 tm (a i) (b i)) σ ⊕ transport (λ i → tm (a i) A) t)
    (J (λ Ω b →  transport (λ i → 𝑇𝑚𝑠 tm Γ (b i ⊹ A)) (σ ⊕ t) ≡
      transport (λ i → 𝑇𝑚𝑠 tm Γ (b i)) σ ⊕ transport (λ i → tm Γ A) t)
      (transportRefl (σ ⊕ t) ∙ (λ i → transportRefl σ (~ i) ⊕ transportRefl t (~ i))) b) a

map𝑇𝑚𝑠comp₃ : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} {ty₃ : Type ℓ₃} {Γ Δ : 𝐶𝑡𝑥 ty₁}
  {tm₁ : 𝐶𝑡𝑥 ty₁ → ty₁ → Type ℓ₄} {tm₂ : 𝐶𝑡𝑥 ty₂ → ty₂ → Type ℓ₅} {tm₃ : 𝐶𝑡𝑥 ty₃ → ty₃ → Type ℓ₆}
  {P : ty₁ → ty₂} {Q : ty₂ → ty₃}
  (f : {A : ty₂} → tm₂ (map𝐶𝑡𝑥 P Γ) A → tm₃ (map𝐶𝑡𝑥 Q (map𝐶𝑡𝑥 P Γ)) (Q A))
  (g : {A : ty₁} → tm₁ Γ A → tm₂ (map𝐶𝑡𝑥 P Γ) (P A))
  (σ : 𝑇𝑚𝑠 tm₁ Γ Δ) →
  map𝑇𝑚𝑠 {tm₁ = tm₃} {tm₃} (λ {A} → transport (λ i → tm₃ (map𝐶𝑡𝑥comp Q P Γ i) A))
    (map𝑇𝑚𝑠₁ (f ∘ g) σ)
  ≡ transport (λ i → 𝑇𝑚𝑠 tm₃ (map𝐶𝑡𝑥comp Q P Γ i) (map𝐶𝑡𝑥comp Q P Δ i))
    (map𝑇𝑚𝑠₁ {tm₁ = tm₂} {tm₂ = tm₃} f (map𝑇𝑚𝑠₁ g σ))
map𝑇𝑚𝑠comp₃ f g ! = fromPathP (λ i → !) ⁻¹
map𝑇𝑚𝑠comp₃ {Γ = Δ} {Σ ⊹ A} {tm₁} {tm₂} {tm₃} {P} {Q} f g (σ ⊕ t) =
  map𝑇𝑚𝑠 (λ {B} → transport (λ i → tm₃ (map𝐶𝑡𝑥comp Q P Δ i) B)) (map𝑇𝑚𝑠₁ (f ∘ g) σ)
    ⊕ transport (λ i → tm₃ (map𝐶𝑡𝑥comp Q P Δ i) (Q (P A))) (f (g t))
    ≡⟨ (λ i → map𝑇𝑚𝑠comp₃ f g σ i
      ⊕ transport (λ i → tm₃ (map𝐶𝑡𝑥comp Q P Δ i) (Q (P A))) (f (g t))) ⟩
  transport (λ i → 𝑇𝑚𝑠 tm₃ (map𝐶𝑡𝑥comp Q P Δ i) (map𝐶𝑡𝑥comp Q P Σ i)) (map𝑇𝑚𝑠₁ f (map𝑇𝑚𝑠₁ g σ))
    ⊕ transport (λ i → tm₃ (map𝐶𝑡𝑥comp Q P Δ i) (Q (P A))) (f (g t))
    ≡⟨ transport⊕ (map𝐶𝑡𝑥comp Q P Δ) (map𝐶𝑡𝑥comp Q P Σ) (map𝑇𝑚𝑠₁ f (map𝑇𝑚𝑠₁ g σ)) (f (g t)) ⁻¹ ⟩
  transport (λ i → 𝑇𝑚𝑠 tm₃ (map𝐶𝑡𝑥comp Q P Δ i) (map𝐶𝑡𝑥comp Q P Σ i ⊹ Q (P A)))
    (map𝑇𝑚𝑠₁ f (map𝑇𝑚𝑠₁ g σ) ⊕ f (g t))
    ∎

map𝑇𝑚𝑠₁id : {ty : Type ℓ₁} {tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂} {Γ Δ : 𝐶𝑡𝑥 ty} (σ : 𝑇𝑚𝑠 tm Γ Δ) →
  map𝑇𝑚𝑠₁ {tm₁ = tm} {tm} (λ {A} → transport (λ i → tm (map𝐶𝑡𝑥id Γ (~ i)) A)) σ
  ≡ transport (λ i → 𝑇𝑚𝑠 tm (map𝐶𝑡𝑥id Γ (~ i)) (map𝐶𝑡𝑥id Δ (~ i))) σ
map𝑇𝑚𝑠₁id ! = fromPathP (λ i → !) ⁻¹
map𝑇𝑚𝑠₁id {tm = tm} {Γ} {Δ ⊹ A} (σ ⊕ t) =
  map𝑇𝑚𝑠₁ (λ {B} → transport (λ i → tm (map𝐶𝑡𝑥id Γ (~ i)) B)) σ
    ⊕ transport (λ i → tm (map𝐶𝑡𝑥id Γ (~ i)) A) t
    ≡⟨ (λ i → map𝑇𝑚𝑠₁id σ i ⊕ transport (λ i → tm (map𝐶𝑡𝑥id Γ (~ i)) A) t) ⟩
  transport (λ i → 𝑇𝑚𝑠 tm (map𝐶𝑡𝑥id Γ (~ i)) (map𝐶𝑡𝑥id Δ (~ i))) σ
    ⊕ transport (λ i → tm (map𝐶𝑡𝑥id Γ (~ i)) A) t
    ≡⟨ transport⊕ (map𝐶𝑡𝑥id Γ ⁻¹) (map𝐶𝑡𝑥id Δ ⁻¹) σ t ⁻¹ ⟩
  transport (λ i → 𝑇𝑚𝑠 tm (map𝐶𝑡𝑥id Γ (~ i)) (map𝐶𝑡𝑥id Δ (~ i) ⊹ A)) (σ ⊕ t)
    ∎

-- The proof of this lemma is due to Amélia (@plt_amy)
transport-tm : {ty : Type ℓ₁} {tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂} {Γ₁ Γ₂ Γ₃ : 𝐶𝑡𝑥 ty} {A₁ A₂ A₃ : ty}
  (a₁ : Γ₁ ≡ Γ₂) (b₁ : A₁ ≡ A₂) (a₂ : Γ₂ ≡ Γ₃) (b₂ : A₂ ≡ A₃) (t : tm Γ₁ A₁) →
  transport (λ i → tm (a₂ i) (b₂ i)) (transport (λ i → tm (a₁ i) (b₁ i)) t)
    ≡ transport (λ i → tm ((a₁ ∙ a₂) i) ((b₁ ∙ b₂) i)) t
transport-tm {tm = tm} a₁ b₁ a₂ b₂ t i =
  transport (λ j → tm (compPath-filler' a₁ a₂ i j) (compPath-filler' b₁ b₂ i j))
    (transp (λ j → tm (a₁ (~ i ∧ j)) (b₁ (~ i ∧ j))) i t)

-- Variables
data 𝑉𝑎𝑟 (ty : Type ℓ) : (Γ : 𝐶𝑡𝑥 ty) (A : ty) → Type ℓ where
  𝑧𝑣 : {Γ : 𝐶𝑡𝑥 ty} {A : ty} → 𝑉𝑎𝑟 ty (Γ ⊹ A) A
  𝑠𝑣 : {Γ : 𝐶𝑡𝑥 ty} {A B : ty} → 𝑉𝑎𝑟 ty Γ A → 𝑉𝑎𝑟 ty (Γ ⊹ B) A

𝑅𝑒𝑛 : (ty : Type ℓ) → 𝐶𝑡𝑥 ty → 𝐶𝑡𝑥 ty → Type ℓ
𝑅𝑒𝑛 ty = 𝑇𝑚𝑠 (𝑉𝑎𝑟 ty)

module _ {ty : Type ℓ} where
  private
    ctx = 𝐶𝑡𝑥 ty
    ren = 𝑅𝑒𝑛 ty
    var = 𝑉𝑎𝑟 ty
  
  W₁𝑅𝑒𝑛 : {Γ Δ : ctx} (A : ty) → ren Γ Δ → ren (Γ ⊹ A) Δ
  W₁𝑅𝑒𝑛 A = map𝑇𝑚𝑠 𝑠𝑣

  W₂𝑅𝑒𝑛 : {Γ Δ : ctx} (A : ty) → ren Γ Δ → ren (Γ ⊹ A) (Δ ⊹ A)
  W₂𝑅𝑒𝑛 A σ = W₁𝑅𝑒𝑛 A σ ⊕ 𝑧𝑣

  id𝑅𝑒𝑛 : (Γ : ctx) → ren Γ Γ
  id𝑅𝑒𝑛 ∅ = !
  id𝑅𝑒𝑛 (Γ ⊹ A) = W₂𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)

  infix 30 _[_]𝑅
  _[_]𝑅 : {Γ Δ : ctx} {A : ty} → var Δ A → ren Γ Δ → var Γ A
  𝑧𝑣 [ σ ⊕ v ]𝑅 = v
  𝑠𝑣 v [ σ ⊕ w ]𝑅 = v [ σ ]𝑅

  infixl 30 _∘𝑅𝑒𝑛_
  _∘𝑅𝑒𝑛_ : {Γ Δ Σ : ctx} → ren Δ Σ → ren Γ Δ → ren Γ Σ
  σ ∘𝑅𝑒𝑛 τ = map𝑇𝑚𝑠 _[ τ ]𝑅 σ

  Wlem1𝑅𝑒𝑛 : {Γ Δ Σ : ctx} {A : ty} (σ : ren Δ Σ) (τ : ren Γ Δ) (v : var Γ A) →
    W₁𝑅𝑒𝑛 A σ ∘𝑅𝑒𝑛 (τ ⊕ v) ≡ σ ∘𝑅𝑒𝑛 τ
  Wlem1𝑅𝑒𝑛 ! τ v = refl
  Wlem1𝑅𝑒𝑛 (σ ⊕ w) τ v = ap (_⊕ w [ τ ]𝑅) (Wlem1𝑅𝑒𝑛 σ τ v)

  Wlem2𝑅𝑒𝑛 : {Γ Δ : ctx} {A B : ty} (v : var Δ A) (σ : ren Γ Δ) →
    v [ W₁𝑅𝑒𝑛 B σ ]𝑅 ≡ 𝑠𝑣 (v [ σ ]𝑅)
  Wlem2𝑅𝑒𝑛 𝑧𝑣 (σ ⊕ v) = refl
  Wlem2𝑅𝑒𝑛 (𝑠𝑣 v) (σ ⊕ w) = Wlem2𝑅𝑒𝑛 v σ

  Wlem3𝑅𝑒𝑛 : {Γ Δ Σ : ctx} {A : ty} (σ : ren Δ Σ) (τ : ren Γ Δ) →
    σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A τ ≡ W₁𝑅𝑒𝑛 A (σ ∘𝑅𝑒𝑛 τ)
  Wlem3𝑅𝑒𝑛 ! τ = refl
  Wlem3𝑅𝑒𝑛 (σ ⊕ v) τ i = Wlem3𝑅𝑒𝑛 σ τ i ⊕ Wlem2𝑅𝑒𝑛 v τ i

  Wlem4𝑅𝑒𝑛 : {Γ Δ Σ : ctx} {A : ty} (σ : ren Δ Σ) (τ : ren Γ Δ) →
    W₂𝑅𝑒𝑛 A σ ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 A τ ≡ W₂𝑅𝑒𝑛 A (σ ∘𝑅𝑒𝑛 τ)
  Wlem4𝑅𝑒𝑛 ! τ = refl
  Wlem4𝑅𝑒𝑛 {A = A} (σ ⊕ v) τ =
    W₁𝑅𝑒𝑛 A σ ∘𝑅𝑒𝑛 (W₁𝑅𝑒𝑛 A τ ⊕ 𝑧𝑣) ⊕ v [ W₁𝑅𝑒𝑛 A τ ]𝑅 ⊕ 𝑧𝑣
      ≡⟨ (λ i → Wlem1𝑅𝑒𝑛 σ (W₁𝑅𝑒𝑛 A τ) 𝑧𝑣 i ⊕ Wlem2𝑅𝑒𝑛 v τ i ⊕ 𝑧𝑣) ⟩
    σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 A τ ⊕ 𝑠𝑣 (v [ τ ]𝑅) ⊕ 𝑧𝑣
      ≡⟨ (λ i → Wlem3𝑅𝑒𝑛 σ τ i ⊕ 𝑠𝑣 (v [ τ ]𝑅) ⊕ 𝑧𝑣) ⟩
    W₂𝑅𝑒𝑛 A (σ ∘𝑅𝑒𝑛 τ ⊕ v [ τ ]𝑅)
      ∎

  Wlem5𝑅𝑒𝑛 : {Γ Δ Σ : ctx} {A : ty} (σ : ren Δ Σ) (τ : ren Γ Δ) →
    W₁𝑅𝑒𝑛 A σ ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 A τ ≡ W₁𝑅𝑒𝑛 A (σ ∘𝑅𝑒𝑛 τ)
  Wlem5𝑅𝑒𝑛 ! τ = refl
  Wlem5𝑅𝑒𝑛 (σ ⊕ v) τ i = Wlem5𝑅𝑒𝑛 σ τ i ⊕ Wlem2𝑅𝑒𝑛 v τ i

  [][]𝑅𝑒𝑛 : {Γ Δ Σ : ctx} {A : ty} (v : var Σ A) (σ : ren Δ Σ) (τ : ren Γ Δ) →
    v [ σ ]𝑅 [ τ ]𝑅 ≡ v [ σ ∘𝑅𝑒𝑛 τ ]𝑅
  [][]𝑅𝑒𝑛 𝑧𝑣 (σ ⊕ v) τ = refl
  [][]𝑅𝑒𝑛 (𝑠𝑣 v) (σ ⊕ w) τ = [][]𝑅𝑒𝑛 v σ τ

  ∘𝑅𝑒𝑛Assoc : {Γ Δ Σ Ω : ctx} (σ : ren Σ Ω) (τ : ren Δ Σ) (μ : ren Γ Δ) →
    σ ∘𝑅𝑒𝑛 τ ∘𝑅𝑒𝑛 μ ≡ σ ∘𝑅𝑒𝑛 (τ ∘𝑅𝑒𝑛 μ)
  ∘𝑅𝑒𝑛Assoc ! τ μ = refl
  ∘𝑅𝑒𝑛Assoc (σ ⊕ v) τ μ i = ∘𝑅𝑒𝑛Assoc σ τ μ i ⊕ [][]𝑅𝑒𝑛 v τ μ i

  ∘𝑅𝑒𝑛IdL : {Γ Δ : ctx} (σ : ren Γ Δ) → id𝑅𝑒𝑛 Δ ∘𝑅𝑒𝑛 σ ≡ σ
  ∘𝑅𝑒𝑛IdL ! = refl
  ∘𝑅𝑒𝑛IdL {Γ} {Δ ⊹ A} (σ ⊕ v) =
    W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Δ) ∘𝑅𝑒𝑛 (σ ⊕ v) ⊕ v
      ≡⟨ ap (_⊕ v) (Wlem1𝑅𝑒𝑛 (id𝑅𝑒𝑛 Δ) σ v) ⟩
    id𝑅𝑒𝑛 Δ ∘𝑅𝑒𝑛 σ ⊕ v
      ≡⟨ ap (_⊕ v) (∘𝑅𝑒𝑛IdL σ) ⟩
    σ ⊕ v
      ∎

  [id]𝑅𝑒𝑛 : {Γ : ctx} {A : ty} (v : var Γ A) →
    v [ id𝑅𝑒𝑛 Γ ]𝑅 ≡ v
  [id]𝑅𝑒𝑛 𝑧𝑣 = refl
  [id]𝑅𝑒𝑛 {Γ ⊹ B} {A} (𝑠𝑣 v) =
    v [ W₁𝑅𝑒𝑛 B (id𝑅𝑒𝑛 Γ) ]𝑅
      ≡⟨ Wlem2𝑅𝑒𝑛 v (id𝑅𝑒𝑛 Γ) ⟩
    𝑠𝑣 (v [ id𝑅𝑒𝑛 Γ ]𝑅)
      ≡⟨ ap 𝑠𝑣 ([id]𝑅𝑒𝑛 v) ⟩
    𝑠𝑣 v
      ∎

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
  W₂𝑅𝑒𝑛 (f A) (tr𝑅𝑒𝑛 f (id𝑅𝑒𝑛 Γ))
    ≡⟨ ap (W₂𝑅𝑒𝑛 (f A)) (trId f Γ) ⟩
  W₂𝑅𝑒𝑛 (f A) (id𝑅𝑒𝑛 (map𝐶𝑡𝑥 f Γ))
    ∎

-- The idea for this construction is due to Reed Mullanix (@totbwf)
derive : {ty : Type ℓ₁} {tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂} {Γ Δ : 𝐶𝑡𝑥 ty} {A : ty} →
  𝑇𝑚𝑠 tm Γ Δ → 𝑉𝑎𝑟 ty Δ A → tm Γ A
derive σ 𝑧𝑣 = 𝑧𝑇𝑚𝑠 σ
derive σ (𝑠𝑣 v) = derive (π𝑇𝑚𝑠 σ) v

deriveMap : {ty : Type ℓ₁} {tm₁ : 𝐶𝑡𝑥 ty → ty → Type ℓ₂} {tm₂ : 𝐶𝑡𝑥 ty → ty → Type ℓ₃}
  {Γ Δ Σ : 𝐶𝑡𝑥 ty} (f : {A : ty} → tm₁ Γ A → tm₂ Δ A) (σ : 𝑇𝑚𝑠 tm₁ Γ Σ) {A : ty}
  (v : 𝑉𝑎𝑟 ty Σ A) → derive (map𝑇𝑚𝑠 {tm₁ = tm₁} {tm₂} f σ) v ≡ f (derive σ v)
deriveMap f (σ ⊕ t) 𝑧𝑣 = refl
deriveMap f (σ ⊕ t) (𝑠𝑣 v) = deriveMap f σ v

deriveMap₁ : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} {tm₁ : 𝐶𝑡𝑥 ty₁ → ty₁ → Type ℓ₃}
  {tm₂ : 𝐶𝑡𝑥 ty₂ → ty₂ → Type ℓ₄} {Γ Σ : 𝐶𝑡𝑥 ty₁} {Δ : 𝐶𝑡𝑥 ty₂} {P : ty₁ → ty₂}
  (f : {A : ty₁} → tm₁ Γ A → tm₂ Δ (P A)) (σ : 𝑇𝑚𝑠 tm₁ Γ Σ) {A : ty₁}
  (v : 𝑉𝑎𝑟 ty₁ Σ A) → derive (map𝑇𝑚𝑠₁ {tm₁ = tm₁} {tm₂} f σ) (tr𝑉𝑎𝑟 P v) ≡ f (derive σ v)
deriveMap₁ f (σ ⊕ t) 𝑧𝑣 = refl
deriveMap₁ f (σ ⊕ t) (𝑠𝑣 v) = deriveMap₁ f σ v

-- Proofs that things are sets

module 𝑉𝑎𝑟Path {ty : Type ℓ₁} where
  private
    ctx = 𝐶𝑡𝑥 ty
    var = 𝑉𝑎𝑟 ty

  isSet𝑉𝑎𝑟 : {Γ : ctx} {A : ty} → isSet (var Γ A)
  isSet𝑉𝑎𝑟 = {!!}

-- We prove that if tm is a set, then 𝑇𝑚𝑠 tm is a set;
-- this is mostly taken from the stdlib treatment of lists.

module 𝑇𝑚𝑠Path {ty : Type ℓ₁} (tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂)
       (isSetTm : {Γ : 𝐶𝑡𝑥 ty} {A : ty} → isSet (tm Γ A)) where

  private
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

  isSet𝑇𝑚𝑠 : {Γ Δ : ctx} → isSet (tms Γ Δ)
  isSet𝑇𝑚𝑠 σ τ =
    isOfHLevelRetract 1
      (encode σ τ)
      (decode σ τ)
      (decodeEncode σ τ)
      (isPropCode σ τ)
