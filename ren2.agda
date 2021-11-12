{-# OPTIONS --cubical --allow-unsolved-metas #-}

module ren2 where

open import contextual public

open import Agda.Builtin.Char public
open import Cubical.Categories.Category

-- These defenitions of Types and Contexts will be used throughout the project

infixr 20 _⇒_
data Ty : Set where
  Base : Char → Ty
  _⇒_ : Ty → Ty → Ty

Ctx = 𝐶𝑡𝑥 Ty

-- Intrinsically well-typed de Bruijn Variables

Var = 𝑉𝑎𝑟 Ty

-- A Renaming is a list of variables

Ren = 𝑇𝑚𝑠 Var

-- Now we exhibit some structure of Renamings

W₁Ren : {Γ Δ : Ctx} (A : Ty) → Ren Γ Δ → Ren (Γ ⊹ A) Δ
W₁Ren A σ = map𝑇𝑚𝑠 𝑠𝑣 σ

W₂Ren : {Γ Δ : Ctx} (A : Ty) → Ren Γ Δ → Ren (Γ ⊹ A) (Δ ⊹ A)
W₂Ren A σ = W₁Ren A σ ⊕ 𝑧𝑣

idRen : (Γ : Ctx) → Ren Γ Γ
idRen Γ = id𝑅𝑒𝑛 Γ

infix 30 _[_]R
_[_]R : {Γ Δ : Ctx} {A : Ty} → Var Δ A → Ren Γ Δ → Var Γ A
𝑧𝑣 [ σ ⊕ v ]R = v
𝑠𝑣 v [ σ ⊕ w ]R = v [ σ ]R

infixl 30 _∘Ren_
_∘Ren_ : {Γ Δ Σ : Ctx} → Ren Δ Σ → Ren Γ Δ → Ren Γ Σ
σ ∘Ren τ = map𝑇𝑚𝑠 _[ τ ]R σ

Wlem1Ren : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Ren Γ Δ) (v : Var Γ A) →
  W₁Ren A σ ∘Ren (τ ⊕ v) ≡ σ ∘Ren τ
Wlem1Ren ! τ v = refl
Wlem1Ren (σ ⊕ w) τ v = ap (_⊕ w [ τ ]R) (Wlem1Ren σ τ v)

Wlem2Ren : {Γ Δ : Ctx} {A B : Ty} (v : Var Δ A) (σ : Ren Γ Δ) →
  v [ W₁Ren B σ ]R ≡ 𝑠𝑣 (v [ σ ]R)
Wlem2Ren 𝑧𝑣 (σ ⊕ v) = refl
Wlem2Ren (𝑠𝑣 v) (σ ⊕ w) = Wlem2Ren v σ

Wlem3Ren : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  σ ∘Ren W₁Ren A τ ≡ W₁Ren A (σ ∘Ren τ)
Wlem3Ren ! τ = refl
Wlem3Ren (σ ⊕ v) τ i = Wlem3Ren σ τ i ⊕ Wlem2Ren v τ i

Wlem4Ren : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  W₂Ren A σ ∘Ren W₂Ren A τ ≡ W₂Ren A (σ ∘Ren τ)
Wlem4Ren ! τ = refl
Wlem4Ren {A = A} (σ ⊕ v) τ =
  W₁Ren A σ ∘Ren (W₁Ren A τ ⊕ 𝑧𝑣) ⊕ v [ W₁Ren A τ ]R ⊕ 𝑧𝑣
    ≡⟨ (λ i → Wlem1Ren σ (W₁Ren A τ) 𝑧𝑣 i ⊕ Wlem2Ren v τ i ⊕ 𝑧𝑣) ⟩
  σ ∘Ren W₁Ren A τ ⊕ 𝑠𝑣 (v [ τ ]R) ⊕ 𝑧𝑣
    ≡⟨ (λ i → Wlem3Ren σ τ i ⊕ 𝑠𝑣 (v [ τ ]R) ⊕ 𝑧𝑣) ⟩
  W₂Ren A (σ ∘Ren τ ⊕ v [ τ ]R)
    ∎

Wlem5Ren : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  W₁Ren A σ ∘Ren W₂Ren A τ ≡ W₁Ren A (σ ∘Ren τ)
Wlem5Ren ! τ = refl
Wlem5Ren (σ ⊕ v) τ i = Wlem5Ren σ τ i ⊕ Wlem2Ren v τ i

[][]Ren : {Γ Δ Σ : Ctx} {A : Ty} (v : Var Σ A) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  v [ σ ]R [ τ ]R ≡ v [ σ ∘Ren τ ]R
[][]Ren 𝑧𝑣 (σ ⊕ v) τ = refl
[][]Ren (𝑠𝑣 v) (σ ⊕ w) τ = [][]Ren v σ τ

∘RenAssoc : {Γ Δ Σ Ω : Ctx} (σ : Ren Σ Ω) (τ : Ren Δ Σ) (μ : Ren Γ Δ) →
  σ ∘Ren τ ∘Ren μ ≡ σ ∘Ren (τ ∘Ren μ)
∘RenAssoc ! τ μ = refl
∘RenAssoc (σ ⊕ v) τ μ i = ∘RenAssoc σ τ μ i ⊕ [][]Ren v τ μ i

∘RenIdL : {Γ Δ : Ctx} (σ : Ren Γ Δ) → idRen Δ ∘Ren σ ≡ σ
∘RenIdL ! = refl
∘RenIdL {Γ} {Δ ⊹ A} (σ ⊕ v) =
  W₁Ren A (idRen Δ) ∘Ren (σ ⊕ v) ⊕ v
    ≡⟨ ap (_⊕ v) (Wlem1Ren (idRen Δ) σ v) ⟩
  idRen Δ ∘Ren σ ⊕ v
    ≡⟨ ap (_⊕ v) (∘RenIdL σ) ⟩
  σ ⊕ v
    ∎

[id]Ren : {Γ : Ctx} {A : Ty} (v : Var Γ A) →
  v [ idRen Γ ]R ≡ v
[id]Ren 𝑧𝑣 = refl
[id]Ren {Γ ⊹ B} {A} (𝑠𝑣 v) =
  v [ W₁Ren B (idRen Γ) ]R
    ≡⟨ Wlem2Ren v (idRen Γ) ⟩
  𝑠𝑣 (v [ idRen Γ ]R)
    ≡⟨ ap 𝑠𝑣 ([id]Ren v) ⟩
  𝑠𝑣 v
    ∎

isSetVar : {Γ : Ctx} {A : Ty} → isSet (Var Γ A)
isSetVar = {!!}

module _ where
  open Contextual

  -- We define the contextual category ρεν and its ambient category REN

  ρεν : Contextual lzero lzero
  ty ρεν = Ty
  tm ρεν = Var
  _⟦_⟧ ρεν = _[_]R
  𝒾𝒹 ρεν Γ = idRen Γ
  𝒾𝒹L ρεν = ∘RenIdL
  𝒾𝒹⟦⟧ ρεν = [id]Ren
  ⟦⟧⟦⟧ ρεν = [][]Ren
  isSetTm ρεν = isSetVar

  REN : Precategory lzero lzero
  REN = ambCat ρεν

  instance
    isCatRen : isCategory REN
    isCatRen = isCatAmbCat ρεν
