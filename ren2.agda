{-# OPTIONS --cubical --allow-unsolved-metas #-}

module ren2 where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Agda.Builtin.Char public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything renaming (cong to ap) public
open import Cubical.Categories.Category

infixr 20 _⇒_
data Ty : Set where
  Base : Char → Ty
  _⇒_ : Ty → Ty → Ty

infixl 20 _⊹_
data Ctx : Set where
  ∅ : Ctx
  _⊹_ : Ctx → Ty → Ctx

data Var : Ctx → Ty → Set where
  Zv : {Γ : Ctx} {A : Ty} → Var (Γ ⊹ A) A
  Sv : {Γ : Ctx} {A B : Ty} → Var Γ A → Var (Γ ⊹ B) A

infixl 20 _⊕R_
data Ren : Ctx → Ctx → Set where
  !R : {Γ : Ctx} → Ren Γ ∅
  _⊕R_ : {Γ Δ : Ctx} {A : Ty} → Ren Γ Δ → Var Γ A → Ren Γ (Δ ⊹ A)

W₁Ren : {Γ Δ : Ctx} (A : Ty) → Ren Γ Δ → Ren (Γ ⊹ A) Δ
W₁Ren A !R = !R
W₁Ren A (σ ⊕R v) = W₁Ren A σ ⊕R Sv v

W₂Ren : {Γ Δ : Ctx} (A : Ty) → Ren Γ Δ → Ren (Γ ⊹ A) (Δ ⊹ A)
W₂Ren A σ = W₁Ren A σ ⊕R Zv

idRen : (Γ : Ctx) → Ren Γ Γ
idRen ∅ = !R
idRen (Γ ⊹ A) = W₂Ren A (idRen Γ)

infix 30 _[_]R
_[_]R : {Γ Δ : Ctx} {A : Ty} → Var Δ A → Ren Γ Δ → Var Γ A
Zv [ σ ⊕R v ]R = v
Sv v [ σ ⊕R w ]R = v [ σ ]R

infixl 30 _∘Ren_
_∘Ren_ : {Γ Δ Σ : Ctx} → Ren Δ Σ → Ren Γ Δ → Ren Γ Σ
!R ∘Ren τ = !R
(σ ⊕R v) ∘Ren τ = σ ∘Ren τ ⊕R v [ τ ]R

Wlem1Ren : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Ren Γ Δ) (v : Var Γ A) →
  W₁Ren A σ ∘Ren (τ ⊕R v) ≡ σ ∘Ren τ
Wlem1Ren !R τ v = refl
Wlem1Ren (σ ⊕R w) τ v = ap (_⊕R w [ τ ]R) (Wlem1Ren σ τ v)

Wlem2Ren : {Γ Δ : Ctx} {A B : Ty} (v : Var Δ A) (σ : Ren Γ Δ) →
  v [ W₁Ren B σ ]R ≡ Sv (v [ σ ]R)
Wlem2Ren Zv (σ ⊕R v) = refl
Wlem2Ren (Sv v) (σ ⊕R w) = Wlem2Ren v σ

Wlem3Ren : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  σ ∘Ren W₁Ren A τ ≡ W₁Ren A (σ ∘Ren τ)
Wlem3Ren !R τ = refl
Wlem3Ren (σ ⊕R v) τ i = Wlem3Ren σ τ i ⊕R Wlem2Ren v τ i

Wlem4Ren : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  W₂Ren A σ ∘Ren W₂Ren A τ ≡ W₂Ren A (σ ∘Ren τ)
Wlem4Ren !R τ = refl
Wlem4Ren {A = A} (σ ⊕R v) τ =
  W₁Ren A σ ∘Ren (W₁Ren A τ ⊕R Zv) ⊕R v [ W₁Ren A τ ]R ⊕R Zv
    ≡⟨ (λ i → Wlem1Ren σ (W₁Ren A τ) Zv i ⊕R Wlem2Ren v τ i ⊕R Zv) ⟩
  σ ∘Ren W₁Ren A τ ⊕R Sv (v [ τ ]R) ⊕R Zv
    ≡⟨ (λ i → Wlem3Ren σ τ i ⊕R Sv (v [ τ ]R) ⊕R Zv) ⟩
  W₂Ren A (σ ∘Ren τ ⊕R v [ τ ]R)
    ∎

Wlem5Ren : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  W₁Ren A σ ∘Ren W₂Ren A τ ≡ W₁Ren A (σ ∘Ren τ)
Wlem5Ren !R τ = refl
Wlem5Ren (σ ⊕R v) τ i = Wlem5Ren σ τ i ⊕R Wlem2Ren v τ i

[][]Ren : {Γ Δ Σ : Ctx} {A : Ty} (v : Var Σ A) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  v [ σ ]R [ τ ]R ≡ v [ σ ∘Ren τ ]R
[][]Ren Zv (σ ⊕R v) τ = refl
[][]Ren (Sv v) (σ ⊕R w) τ = [][]Ren v σ τ

∘RenAssoc : {Γ Δ Σ Ω : Ctx} (σ : Ren Σ Ω) (τ : Ren Δ Σ) (μ : Ren Γ Δ) →
  σ ∘Ren τ ∘Ren μ ≡ σ ∘Ren (τ ∘Ren μ)
∘RenAssoc !R τ μ = refl
∘RenAssoc (σ ⊕R v) τ μ i = ∘RenAssoc σ τ μ i ⊕R [][]Ren v τ μ i

∘RenIdL : {Γ Δ : Ctx} (σ : Ren Γ Δ) → idRen Δ ∘Ren σ ≡ σ
∘RenIdL !R = refl
∘RenIdL {Γ} {Δ ⊹ A} (σ ⊕R v) =
  W₁Ren A (idRen Δ) ∘Ren (σ ⊕R v) ⊕R v
    ≡⟨ ap (_⊕R v) (Wlem1Ren (idRen Δ) σ v) ⟩
  idRen Δ ∘Ren σ ⊕R v
    ≡⟨ ap (_⊕R v) (∘RenIdL σ) ⟩
  σ ⊕R v
    ∎

[id]Ren : {Γ : Ctx} {A : Ty} (v : Var Γ A) →
  v [ idRen Γ ]R ≡ v
[id]Ren Zv = refl
[id]Ren {Γ ⊹ B} {A} (Sv v) =
  v [ W₁Ren B (idRen Γ) ]R
    ≡⟨ Wlem2Ren v (idRen Γ) ⟩
  Sv (v [ idRen Γ ]R)
    ≡⟨ ap Sv ([id]Ren v) ⟩
  Sv v
    ∎

∘RenIdR : {Γ Δ : Ctx} (σ : Ren Γ Δ) → σ ∘Ren idRen Γ ≡ σ
∘RenIdR !R = refl
∘RenIdR (σ ⊕R v) i = ∘RenIdR σ i ⊕R [id]Ren v i

isSetRen : {Γ Δ : Ctx} → isSet (Ren Γ Δ)
isSetRen = {!!}

module _ where
  open Precategory renaming (id to 𝒾𝒹)

  REN : Precategory lzero lzero
  REN .ob = Ctx
  REN .Hom[_,_] = Ren
  REN .𝒾𝒹 Γ = idRen Γ
  REN ._⋆_ σ τ = τ ∘Ren σ
  REN .⋆IdL = ∘RenIdR
  REN .⋆IdR = ∘RenIdL
  REN .⋆Assoc σ τ μ = ∘RenAssoc μ τ σ ⁻¹

  instance
    isCatREN : isCategory REN
    isCatREN .isSetHom = isSetRen
