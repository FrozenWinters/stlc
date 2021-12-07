{-# OPTIONS --cubical #-}

module ren where

open import contextual public

open import Agda.Builtin.Char public
open import Cubical.Categories.Category

module _ {ℓ : Level} (Ty : Type ℓ) where
  open Contextual
  
  ρεν : Contextual ℓ ℓ
  ty ρεν = Ty
  tm ρεν = 𝑉𝑎𝑟 Ty
  _⟦_⟧ ρεν = _[_]𝑅
  𝒾𝒹 ρεν Γ = id𝑅𝑒𝑛 Γ
  𝒾𝒹L ρεν = ∘𝑅𝑒𝑛IdL
  𝒾𝒹⟦⟧ ρεν = [id]𝑅𝑒𝑛
  ⟦⟧⟦⟧ ρεν = [][]𝑅𝑒𝑛
  isSetTm ρεν = 𝑉𝑎𝑟Path.isSet𝑉𝑎𝑟

  REN : Precategory ℓ ℓ
  REN = ambCat ρεν


module _ {ℓ : Level} {Ty : Type ℓ} where
  open Contextual (ρεν Ty)

  deriveρεν : {Γ Δ : ctx} {A : ty} (v : IntVar Δ A) (σ : tms Γ Δ) →
    derive σ v ≡ v ⟦ σ ⟧
  deriveρεν 𝑧𝑣 (σ ⊕ t) = refl
  deriveρεν (𝑠𝑣 v) (σ ⊕ t) = deriveρεν v σ
  
  instance
    isCat𝑅𝑒𝑛 : isCategory (REN Ty)
    isCat𝑅𝑒𝑛 = isCatAmbCat
