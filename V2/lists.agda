{-# OPTIONS --cubical --allow-unsolved-metas #-}

module lists where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything renaming (cong to ap) public

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

infixl 20 _⊹_
data 𝐶𝑡𝑥 (ty : Type ℓ) : Type ℓ where
  ∅ : 𝐶𝑡𝑥 ty
  _⊹_ : 𝐶𝑡𝑥 ty → ty → 𝐶𝑡𝑥 ty

data 𝑉𝑎𝑟 (ty : Type ℓ) : (Γ : 𝐶𝑡𝑥 ty) (A : ty) → Type ℓ where
  𝑧𝑣 : {Γ : 𝐶𝑡𝑥 ty} {A : ty} → 𝑉𝑎𝑟 ty (Γ ⊹ A) A
  𝑠𝑣 : {Γ : 𝐶𝑡𝑥 ty} {A B : ty} → 𝑉𝑎𝑟 ty Γ A → 𝑉𝑎𝑟 ty (Γ ⊹ B) A

infixl 20 _⊕_
data 𝐸𝑙𝑠 {ty : Type ℓ₁} (el : ty → Type ℓ₂) : (Γ : 𝐶𝑡𝑥 ty) → Type (ℓ₁ ⊔ ℓ₂) where
  ! : 𝐸𝑙𝑠 el ∅
  _⊕_ : {Γ : 𝐶𝑡𝑥 ty} {A : ty} → 𝐸𝑙𝑠 el Γ → el A → 𝐸𝑙𝑠 el (Γ ⊹ A)

𝑇𝑚𝑠 : {ty : Type ℓ₁} (tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂) (Γ Δ : 𝐶𝑡𝑥 ty) → Type (ℓ₁ ⊔ ℓ₂)
𝑇𝑚𝑠 tm Γ Δ = 𝐸𝑙𝑠 (tm Γ) Δ

map𝐶𝑡𝑥 : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} (f : ty₁ → ty₂) (Γ : 𝐶𝑡𝑥 ty₁) → 𝐶𝑡𝑥 ty₂
map𝐶𝑡𝑥 f ∅ = ∅
map𝐶𝑡𝑥 f (Γ ⊹ A) = map𝐶𝑡𝑥 f Γ ⊹ f A

map𝐸𝑙𝑠 : {ty : Type ℓ₁} {Δ : 𝐶𝑡𝑥 ty} {el₁ : ty → Type ℓ₂} {el₂ : ty → Type ℓ₃}
  (f : {A : ty} → el₁ A → el₂ A) → 𝐸𝑙𝑠 el₁ Δ → 𝐸𝑙𝑠 el₂ Δ
map𝐸𝑙𝑠 f ! = !
map𝐸𝑙𝑠 f (σ ⊕ t) = map𝐸𝑙𝑠 f σ ⊕ f t

map𝐸𝑙𝑠₁ : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} {P : ty₁ → ty₂} {Δ : 𝐶𝑡𝑥 ty₁}
  {el₁ : ty₁ → Type ℓ₃} {el₂ : ty₂ → Type ℓ₄} 
  (f : {A : ty₁} → el₁ A → el₂ (P A)) → 𝐸𝑙𝑠 el₁ Δ → 𝐸𝑙𝑠 el₂ (map𝐶𝑡𝑥 P Δ)
map𝐸𝑙𝑠₁ f ! = !
map𝐸𝑙𝑠₁ f (σ ⊕ t) = map𝐸𝑙𝑠₁ f σ ⊕ f t

π𝐸𝑙𝑠 : {ty : Type ℓ₁} {el : ty → Type ℓ₂} {Γ : 𝐶𝑡𝑥 ty} {A : ty} →
  𝐸𝑙𝑠 el (Γ ⊹ A) → 𝐸𝑙𝑠 el Γ
π𝐸𝑙𝑠 (σ ⊕ t) = σ

𝑧𝐸𝑙𝑠 : {ty : Type ℓ₁} {el : ty → Type ℓ₂} {Γ : 𝐶𝑡𝑥 ty} {A : ty} →
  𝐸𝑙𝑠 el (Γ ⊹ A) → el A
𝑧𝐸𝑙𝑠 (σ ⊕ t) = t

π𝑧η𝐸𝑙𝑠 : {ty : Type ℓ₁} {el : ty → Type ℓ₂} {Γ : 𝐶𝑡𝑥 ty} {A : ty}
  (σ : 𝐸𝑙𝑠 el (Γ ⊹ A)) → (π𝐸𝑙𝑠 σ) ⊕ (𝑧𝐸𝑙𝑠 σ) ≡ σ
π𝑧η𝐸𝑙𝑠 (σ ⊕ t) = refl

derive : {ty : Type ℓ₁} {el : ty → Type ℓ₂} {Γ : 𝐶𝑡𝑥 ty} {A : ty} →
  𝐸𝑙𝑠 el Γ → 𝑉𝑎𝑟 ty Γ A → el A
derive σ 𝑧𝑣 = 𝑧𝐸𝑙𝑠 σ
derive σ (𝑠𝑣 v) = derive (π𝐸𝑙𝑠 σ) v

deriveMap : {ty : Type ℓ₁} {Γ : 𝐶𝑡𝑥 ty} {el₁ : ty → Type ℓ₂} {el₂ : ty → Type ℓ₃}
  (f : {A : ty} → el₁ A → el₂ A) (σ : 𝐸𝑙𝑠 el₁ Γ) {A : ty} (v : 𝑉𝑎𝑟 ty Γ A) →
  derive (map𝐸𝑙𝑠 f σ) v ≡ f (derive σ v)
deriveMap f (σ ⊕ t) 𝑧𝑣 = refl
deriveMap f (σ ⊕ t) (𝑠𝑣 v) = deriveMap f σ v

𝑅𝑒𝑛 : (ty : Type ℓ) → 𝐶𝑡𝑥 ty → 𝐶𝑡𝑥 ty → Type ℓ
𝑅𝑒𝑛 ty = 𝑇𝑚𝑠 (𝑉𝑎𝑟 ty)

derive𝑅𝑒𝑛 : {ty : Type ℓ₁} {el : ty → Type ℓ₂} {Γ Δ : 𝐶𝑡𝑥 ty} →
  𝐸𝑙𝑠 el Γ → 𝑅𝑒𝑛 ty Γ Δ → 𝐸𝑙𝑠 el Δ
derive𝑅𝑒𝑛 σ = map𝐸𝑙𝑠 (derive σ)

derive𝑅𝑒𝑛Map : {ty : Type ℓ₁} {Γ Δ : 𝐶𝑡𝑥 ty} {el₁ : ty → Type ℓ₂} {el₂ : ty → Type ℓ₃}
  (f : {A : ty} → el₁ A → el₂ A) (σ : 𝐸𝑙𝑠 el₁ Γ) (τ : 𝑅𝑒𝑛 ty Γ Δ) →
  derive𝑅𝑒𝑛 (map𝐸𝑙𝑠 f σ) τ ≡ map𝐸𝑙𝑠 f (derive𝑅𝑒𝑛 σ τ)
derive𝑅𝑒𝑛Map f σ ! = refl
derive𝑅𝑒𝑛Map f σ (τ ⊕ v) i = derive𝑅𝑒𝑛Map f σ τ i ⊕ deriveMap f σ v i

module _ {ty : Type ℓ} where
  private
    ctx = 𝐶𝑡𝑥 ty
    ren = 𝑅𝑒𝑛 ty
    var = 𝑉𝑎𝑟 ty

  W₁𝑅𝑒𝑛 : {Γ Δ : ctx} (A : ty) → ren Γ Δ → ren (Γ ⊹ A) Δ
  W₁𝑅𝑒𝑛 A = map𝐸𝑙𝑠 𝑠𝑣

  W₂𝑅𝑒𝑛 : {Γ Δ : ctx} (A : ty) → ren Γ Δ → ren (Γ ⊹ A) (Δ ⊹ A)
  W₂𝑅𝑒𝑛 A σ = W₁𝑅𝑒𝑛 A σ ⊕ 𝑧𝑣

  id𝑅𝑒𝑛 : (Γ : ctx) → ren Γ Γ
  id𝑅𝑒𝑛 ∅ = !
  id𝑅𝑒𝑛 (Γ ⊹ A) = W₂𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)

  infix 30 _[_]𝑅
  _[_]𝑅 : {Γ Δ : ctx} {A : ty} → var Δ A → ren Γ Δ → var Γ A
  v [ σ ]𝑅 = derive σ v

  infixl 30 _∘𝑅𝑒𝑛_
  _∘𝑅𝑒𝑛_ : {Γ Δ Σ : ctx} → ren Δ Σ → ren Γ Δ → ren Γ Σ
  σ ∘𝑅𝑒𝑛 τ = map𝐸𝑙𝑠 _[ τ ]𝑅 σ

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

deriveW : {ty : Type ℓ₁} {Γ Δ : 𝐶𝑡𝑥 ty} {A : ty} {el : ty → Type ℓ₂}
  (σ : 𝐸𝑙𝑠 el Γ) (t : el A) (τ : 𝑅𝑒𝑛 ty Γ Δ) →
  derive𝑅𝑒𝑛 (σ ⊕ t) (W₁𝑅𝑒𝑛 A τ) ≡ derive𝑅𝑒𝑛 σ τ
deriveW σ t ! = refl
deriveW σ t (τ ⊕ v) i = deriveW σ t τ i ⊕ derive σ v

deriveId : {ty : Type ℓ₁} {Γ : 𝐶𝑡𝑥 ty} {el : ty → Type ℓ₂} (σ : 𝐸𝑙𝑠 el Γ) →
  derive𝑅𝑒𝑛 σ (id𝑅𝑒𝑛 Γ) ≡ σ
deriveId ! = refl
deriveId {Γ = Γ ⊹ A} (σ ⊕ t) =
  derive𝑅𝑒𝑛 (σ ⊕ t) (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) ⊕ t
    ≡⟨ ap (_⊕ t) (deriveW σ t (id𝑅𝑒𝑛 Γ)) ⟩
  derive𝑅𝑒𝑛 σ (id𝑅𝑒𝑛 Γ) ⊕ t
    ≡⟨ ap (_⊕ t) (deriveId σ) ⟩
  σ ⊕ t
    ∎

{-deriveId₂ : {ty : Type ℓ₁} {Γ Δ : 𝐶𝑡𝑥 ty} (σ : 𝑅𝑒𝑛 ty Γ Δ) →
  derive𝑅𝑒𝑛 (id𝑅𝑒𝑛 Γ) σ ≡ σ
deriveId₂-}

map𝐶𝑡𝑥id : {ty : Type ℓ} (Γ : 𝐶𝑡𝑥 ty) → map𝐶𝑡𝑥 (λ A → A) Γ ≡ Γ
map𝐶𝑡𝑥id ∅ = refl
map𝐶𝑡𝑥id (Γ ⊹ A) i = map𝐶𝑡𝑥id Γ i ⊹ A

map𝐶𝑡𝑥comp : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} {ty₃ : Type ℓ₃} (g : ty₂ → ty₃) (f : ty₁ → ty₂)
  (Γ : 𝐶𝑡𝑥 ty₁) → map𝐶𝑡𝑥 g (map𝐶𝑡𝑥 f Γ) ≡ map𝐶𝑡𝑥 (g ∘ f) Γ
map𝐶𝑡𝑥comp g f ∅ = refl
map𝐶𝑡𝑥comp g f (Γ ⊹ A) i = map𝐶𝑡𝑥comp g f Γ i ⊹ g (f A)

map𝐸𝑙𝑠comp : {ty : Type ℓ₁} {el₁ : ty → Type ℓ₂} {el₂ : ty → Type ℓ₃}
  {el₃ : ty → Type ℓ₄} {Γ : 𝐶𝑡𝑥 ty} (f : {A : ty} → el₂ A → el₃ A)
  (g : {A : ty} → el₁ A → el₂ A) (σ : 𝐸𝑙𝑠 el₁ Γ) →
  map𝐸𝑙𝑠 f (map𝐸𝑙𝑠 g σ) ≡ map𝐸𝑙𝑠 (f ∘ g) σ
map𝐸𝑙𝑠comp f g ! = refl
map𝐸𝑙𝑠comp f g (σ ⊕ t) i = map𝐸𝑙𝑠comp f g σ i ⊕ f (g t)

map𝐸𝑙𝑠comp₁ : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} {el₁ : ty₁ → Type ℓ₃} {el₂ : ty₁ → Type ℓ₄}
  {el₃ : ty₂ → Type ℓ₅} {Γ : 𝐶𝑡𝑥 ty₁}  {P : ty₁ → ty₂} (f : {A : ty₁} → el₂ A → el₃ (P A))
  (g : {A : ty₁} → el₁ A → el₂ A) (σ : 𝐸𝑙𝑠 el₁ Γ) →
  map𝐸𝑙𝑠₁ {el₁ = el₂} {el₃} f (map𝐸𝑙𝑠 g σ) ≡ map𝐸𝑙𝑠₁ (f ∘ g) σ
map𝐸𝑙𝑠comp₁ f g ! = refl
map𝐸𝑙𝑠comp₁ f g (σ ⊕ t) i = map𝐸𝑙𝑠comp₁ f g σ i ⊕ f (g t)

map𝐸𝑙𝑠comp₂ : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} {el₁ : ty₁ → Type ℓ₃} {el₂ : ty₂ → Type ℓ₄}
  {el₃ : ty₂ → Type ℓ₅} {Γ : 𝐶𝑡𝑥 ty₁}  {P : ty₁ → ty₂} (f : {A : ty₂} → el₂ A → el₃ A)
  (g : {A : ty₁} → el₁ A → el₂ (P A)) (σ : 𝐸𝑙𝑠 el₁ Γ) →
  map𝐸𝑙𝑠 f (map𝐸𝑙𝑠₁ {el₁ = el₁} {el₂} g σ) ≡ map𝐸𝑙𝑠₁ (f ∘ g) σ
map𝐸𝑙𝑠comp₂ f g ! = refl
map𝐸𝑙𝑠comp₂ f g (σ ⊕ t) i = map𝐸𝑙𝑠comp₂ f g σ i ⊕ f (g t)

tr𝑉𝑎𝑟 : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} (f : ty₁ → ty₂) {Γ : 𝐶𝑡𝑥 ty₁} {A : ty₁}
  → 𝑉𝑎𝑟 ty₁ Γ A → 𝑉𝑎𝑟 ty₂ (map𝐶𝑡𝑥 f Γ) (f A)
tr𝑉𝑎𝑟 f 𝑧𝑣 = 𝑧𝑣
tr𝑉𝑎𝑟 f (𝑠𝑣 v) = 𝑠𝑣 (tr𝑉𝑎𝑟 f v)

tr𝑅𝑒𝑛 : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} (f : ty₁ → ty₂) {Γ Δ : 𝐶𝑡𝑥 ty₁}
  → 𝑅𝑒𝑛 ty₁ Γ Δ → 𝑅𝑒𝑛 ty₂ (map𝐶𝑡𝑥 f Γ) (map𝐶𝑡𝑥 f Δ)
tr𝑅𝑒𝑛 f = map𝐸𝑙𝑠₁ (tr𝑉𝑎𝑟 f)

trId : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} (f : ty₁ → ty₂) (Γ : 𝐶𝑡𝑥 ty₁) →
  tr𝑅𝑒𝑛 f (id𝑅𝑒𝑛 Γ) ≡ id𝑅𝑒𝑛 (map𝐶𝑡𝑥 f Γ)
trId f ∅ = refl
trId f (Γ ⊹ A) =
  map𝐸𝑙𝑠₁ (tr𝑉𝑎𝑟 f) (map𝐸𝑙𝑠 𝑠𝑣 (id𝑅𝑒𝑛 Γ)) ⊕ 𝑧𝑣
    ≡⟨ ap (_⊕ 𝑧𝑣) (map𝐸𝑙𝑠comp₁ (tr𝑉𝑎𝑟 f) 𝑠𝑣 (id𝑅𝑒𝑛 Γ)) ⟩
  map𝐸𝑙𝑠₁ (𝑠𝑣 ∘ (tr𝑉𝑎𝑟 f)) (id𝑅𝑒𝑛 Γ) ⊕ 𝑧𝑣
    ≡⟨ ap (_⊕ 𝑧𝑣) (map𝐸𝑙𝑠comp₂ 𝑠𝑣 (tr𝑉𝑎𝑟 f) (id𝑅𝑒𝑛 Γ) ⁻¹) ⟩
  W₂𝑅𝑒𝑛 (f A) (tr𝑅𝑒𝑛 f (id𝑅𝑒𝑛 Γ))
    ≡⟨ ap (W₂𝑅𝑒𝑛 (f A)) (trId f Γ) ⟩
  W₂𝑅𝑒𝑛 (f A) (id𝑅𝑒𝑛 (map𝐶𝑡𝑥 f Γ))
    ∎

deriveMap₁ : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} {el₁ : ty₁ → Type ℓ₃} {el₂ : ty₂ → Type ℓ₄}
  {P : ty₁ → ty₂} (f : {A : ty₁} → el₁ A → el₂ (P A)) {Γ : 𝐶𝑡𝑥 ty₁} {A : ty₁} (σ : 𝐸𝑙𝑠 el₁ Γ) 
  (v : 𝑉𝑎𝑟 ty₁ Γ A) → derive (map𝐸𝑙𝑠₁ {el₁ = el₁} {el₂} f σ) (tr𝑉𝑎𝑟 P v) ≡ f (derive σ v)
deriveMap₁ f (σ ⊕ t) 𝑧𝑣 = refl
deriveMap₁ f (σ ⊕ t) (𝑠𝑣 v) = deriveMap₁ f σ v

-- The proof of this lemma is due to Amélia (@plt_amy)
transport-tm : {ty : Type ℓ₁} {tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂} {Γ₁ Γ₂ Γ₃ : 𝐶𝑡𝑥 ty} {A₁ A₂ A₃ : ty}
  (a₁ : Γ₁ ≡ Γ₂) (b₁ : A₁ ≡ A₂) (a₂ : Γ₂ ≡ Γ₃) (b₂ : A₂ ≡ A₃) (t : tm Γ₁ A₁) →
  transport (λ i → tm (a₂ i) (b₂ i)) (transport (λ i → tm (a₁ i) (b₁ i)) t)
    ≡ transport (λ i → tm ((a₁ ∙ a₂) i) ((b₁ ∙ b₂) i)) t
transport-tm {tm = tm} a₁ b₁ a₂ b₂ t i =
  transport (λ j → tm (compPath-filler' a₁ a₂ i j) (compPath-filler' b₁ b₂ i j))
    (transp (λ j → tm (a₁ (~ i ∧ j)) (b₁ (~ i ∧ j))) i t)

-- Annoying transport lemmas

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

map𝑇𝑚𝑠₁id : {ty : Type ℓ₁} {tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂} {Γ Δ : 𝐶𝑡𝑥 ty} (σ : 𝑇𝑚𝑠 tm Γ Δ) →
  map𝐸𝑙𝑠₁ (λ {A} → transport (λ i → tm (map𝐶𝑡𝑥id Γ (~ i)) A)) σ
  ≡ transport (λ i → 𝑇𝑚𝑠 tm (map𝐶𝑡𝑥id Γ (~ i)) (map𝐶𝑡𝑥id Δ (~ i))) σ
map𝑇𝑚𝑠₁id ! = fromPathP (λ i → !) ⁻¹
map𝑇𝑚𝑠₁id {tm = tm} {Γ} {Δ ⊹ A} (σ ⊕ t) =
  map𝐸𝑙𝑠₁ (λ {B} → transport (λ i → tm (map𝐶𝑡𝑥id Γ (~ i)) B)) σ
    ⊕ transport (λ i → tm (map𝐶𝑡𝑥id Γ (~ i)) A) t
    ≡⟨ (λ i → map𝑇𝑚𝑠₁id {tm = tm} σ i ⊕ transport (λ i → tm (map𝐶𝑡𝑥id Γ (~ i)) A) t) ⟩
  transport (λ i → 𝑇𝑚𝑠 tm (map𝐶𝑡𝑥id Γ (~ i)) (map𝐶𝑡𝑥id Δ (~ i))) σ
    ⊕ transport (λ i → tm (map𝐶𝑡𝑥id Γ (~ i)) A) t
    ≡⟨ transport⊕ {tm = tm} (map𝐶𝑡𝑥id Γ ⁻¹) (map𝐶𝑡𝑥id Δ ⁻¹) σ t ⁻¹ ⟩
  transport (λ i → 𝑇𝑚𝑠 tm (map𝐶𝑡𝑥id Γ (~ i)) (map𝐶𝑡𝑥id Δ (~ i) ⊹ A)) (σ ⊕ t)
    ∎

map𝑇𝑚𝑠comp₃ : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} {ty₃ : Type ℓ₃} {Γ Δ : 𝐶𝑡𝑥 ty₁}
  {tm₁ : 𝐶𝑡𝑥 ty₁ → ty₁ → Type ℓ₄} {tm₂ : 𝐶𝑡𝑥 ty₂ → ty₂ → Type ℓ₅} {tm₃ : 𝐶𝑡𝑥 ty₃ → ty₃ → Type ℓ₆}
  {P : ty₁ → ty₂} {Q : ty₂ → ty₃}
  (f : {A : ty₂} → tm₂ (map𝐶𝑡𝑥 P Γ) A → tm₃ (map𝐶𝑡𝑥 Q (map𝐶𝑡𝑥 P Γ)) (Q A))
  (g : {A : ty₁} → tm₁ Γ A → tm₂ (map𝐶𝑡𝑥 P Γ) (P A))
  (σ : 𝑇𝑚𝑠 tm₁ Γ Δ) →
  map𝐸𝑙𝑠 (λ {A} → transport (λ i → tm₃ (map𝐶𝑡𝑥comp Q P Γ i) A)) (map𝐸𝑙𝑠₁ (f ∘ g) σ)
  ≡ transport (λ i → 𝑇𝑚𝑠 tm₃ (map𝐶𝑡𝑥comp Q P Γ i) (map𝐶𝑡𝑥comp Q P Δ i)) (map𝐸𝑙𝑠₁ f (map𝐸𝑙𝑠₁ g σ))
map𝑇𝑚𝑠comp₃ f g ! = fromPathP (λ i → !) ⁻¹
map𝑇𝑚𝑠comp₃ {Γ = Δ} {Σ ⊹ A} {tm₁} {tm₂} {tm₃} {P} {Q} f g (σ ⊕ t) =
  map𝐸𝑙𝑠 (λ {B} → transport (λ i → tm₃ (map𝐶𝑡𝑥comp Q P Δ i) B)) (map𝐸𝑙𝑠₁ (f ∘ g) σ)
    ⊕ transport (λ i → tm₃ (map𝐶𝑡𝑥comp Q P Δ i) (Q (P A))) (f (g t))
    ≡⟨ (λ i → map𝑇𝑚𝑠comp₃ {tm₁ = tm₁} {tm₂} {tm₃} f g σ i
      ⊕ transport (λ i → tm₃ (map𝐶𝑡𝑥comp Q P Δ i) (Q (P A))) (f (g t))) ⟩
  transport (λ i → 𝑇𝑚𝑠 tm₃ (map𝐶𝑡𝑥comp Q P Δ i) (map𝐶𝑡𝑥comp Q P Σ i)) (map𝐸𝑙𝑠₁ f (map𝐸𝑙𝑠₁ g σ))
    ⊕ transport (λ i → tm₃ (map𝐶𝑡𝑥comp Q P Δ i) (Q (P A))) (f (g t))
    ≡⟨ transport⊕ {tm = tm₃} (map𝐶𝑡𝑥comp Q P Δ) (map𝐶𝑡𝑥comp Q P Σ)
      (map𝐸𝑙𝑠₁ f (map𝐸𝑙𝑠₁ g σ)) (f (g t)) ⁻¹ ⟩
  transport (λ i → 𝑇𝑚𝑠 tm₃ (map𝐶𝑡𝑥comp Q P Δ i) (map𝐶𝑡𝑥comp Q P Σ i ⊹ Q (P A)))
    (map𝐸𝑙𝑠₁ f (map𝐸𝑙𝑠₁ g σ) ⊕ f (g t))
    ∎


module 𝑉𝑎𝑟Path {ty : Type ℓ₁} where
  private
    ctx = 𝐶𝑡𝑥 ty
    var = 𝑉𝑎𝑟 ty

  isSet𝑉𝑎𝑟 : {Γ : ctx} {A : ty} → isSet (var Γ A)
  isSet𝑉𝑎𝑟 = {!!}

module 𝐸𝑙𝑠Path {ty : Type ℓ₁} (el : ty → Type ℓ₂)
       (isSetEl : {A : ty} → isSet (el A)) where

  private
    ctx = 𝐶𝑡𝑥 ty
    els = 𝐸𝑙𝑠 el

  isSet𝐸𝑙𝑠 : {Γ : ctx} → isSet (els Γ)
  isSet𝐸𝑙𝑠 = {!!}

module 𝑇𝑚𝑠Path {ty : Type ℓ₁} (tm : 𝐶𝑡𝑥 ty → ty → Type ℓ₂)
       (isSetTm : {Γ : 𝐶𝑡𝑥 ty} {A : ty} → isSet (tm Γ A)) where

  private
    ctx = 𝐶𝑡𝑥 ty
    tms = 𝑇𝑚𝑠 tm

  isSet𝑇𝑚𝑠 : {Γ Δ : ctx} → isSet (tms Γ Δ)
  isSet𝑇𝑚𝑠 {Γ} {Δ} σ τ = 𝐸𝑙𝑠Path.isSet𝐸𝑙𝑠 (tm Γ) isSetTm σ τ
