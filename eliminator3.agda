{-# OPTIONS --cubical #-}

module eliminator3 where

open import contextual
open import cartesian2
open import syn3
open import ren2

open import Agda.Builtin.Char
open import Cubical.Categories.Category

module Eliminator {ℓ₁ ℓ₂} (𝒞 : Contextual ℓ₁ ℓ₂) ⦃ CCC𝒞 : CCC 𝒞 ⦄
                  (base : (c : Char) → Contextual.ty 𝒞) where

  open Contextual 𝒞
  open CCC CCC𝒞

  interpTy : Ty → ty
  interpTy (Base X) = base X
  interpTy (A ⇒ B) = (interpTy A) ⇛ (interpTy B)
  
  interpCtx : Ctx → ctx
  interpCtx Γ = mapRL interpTy Γ

  interpVar : {Γ : Ctx} {A : Ty} (v : Var Γ A) → tm (interpCtx Γ) (interpTy A)
  interpVar Zv = 𝑧
  interpVar (Sv v) = interpVar v ⟦ π ⟧

  interpRen : {Γ Δ : Ctx} (σ : Ren Γ Δ) → tms (interpCtx Γ) (interpCtx Δ)
  interpRen = mapIL₁ interpVar

  interpW₁Ren : {Γ Δ : Ctx} {A : Ty} (σ : Ren Γ Δ) →
    interpRen (W₁Ren A σ) ≡ interpRen σ ⊚ π
  interpW₁Ren ! = !η (! ⊚ π)
  interpW₁Ren {A = A} (σ ⊕ v) =
    interpRen (W₁Ren A σ) ⊕ interpVar v ⟦ π ⟧
      ≡⟨ ap (_⊕ interpVar v ⟦ π ⟧) (interpW₁Ren σ)  ⟩
    interpRen σ ⊚ π ⊕ interpVar v ⟦ π ⟧
      ≡⟨ ⊕⊚ (interpRen σ) (interpVar v) π ⁻¹ ⟩
    interpRen (σ ⊕ v) ⊚ π
      ∎

  interpIdRen : {Γ : Ctx} → interpRen (idRen Γ) ≡ 𝒾𝒹 (interpCtx Γ)

  πlem : {Γ : Ctx} {A : Ty} → interpRen (W₁Ren A (idRen Γ)) ≡ π
  πlem {Γ} {A} =
    interpRen (W₁Ren A (idRen Γ))
      ≡⟨ interpW₁Ren (idRen Γ) ⟩
    interpRen (idRen Γ) ⊚ π
      ≡⟨ ap (_⊚ π) interpIdRen ⟩
    𝒾𝒹 (interpCtx Γ) ⊚ π
      ≡⟨ 𝒾𝒹L π ⟩
    π
      ∎

  interpIdRen {∅} = !η (𝒾𝒹 ∅)
  interpIdRen {Γ ⊹ A} =
    interpRen (W₁Ren A (idRen Γ)) ⊕ 𝑧
      ≡⟨ ap (_⊕ 𝑧) πlem ⟩
    π ⊕ 𝑧
      ≡⟨ 𝒾𝒹β ⟩
    𝒾𝒹 (interpCtx (Γ ⊹ A))
      ∎

  interpTm  : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → tm (interpCtx Γ) (interpTy A)

  {-# TERMINATING #-}
  interpTms : {Γ Δ : Ctx} (σ : Tms Γ Δ) → tms  (interpCtx Γ)  (interpCtx Δ)
  interpTms ! = !
  interpTms (σ ⊕ t) = interpTms σ ⊕ interpTm t

  interpVarify : {Γ Δ : Ctx} (σ : Ren Γ Δ) →
    interpTms (varify σ) ≡ interpRen σ
    
  interpId : {Γ : Ctx} → interpTms (idTms Γ) ≡ 𝒾𝒹 (interpCtx Γ)
  interpId {Γ} =
   interpTms (varify (idRen Γ))
     ≡⟨ interpVarify (idRen Γ) ⟩
   interpRen (idRen Γ)
     ≡⟨ interpIdRen ⟩
   𝒾𝒹 (interpCtx Γ)
     ∎

  interp∘Tms : {Γ Δ Σ : Ctx} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
    interpTms (σ ∘Tms τ) ≡ interpTms σ ⊚ interpTms τ

  interpW₁Tm : {Γ : Ctx} (A : Ty) {B : Ty} (t : Tm Γ B) →
    interpTm (W₁Tm A t) ≡ interpTm t ⟦ π ⟧

  interpW₁Tms : {Γ Δ : Ctx} (A : Ty) (σ : Tms Γ Δ) →
    interpTms (W₁Tms A σ) ≡ interpTms σ ⊚ π
  interpW₁Tms A ! = !η (! ⊚ π)
  interpW₁Tms A (σ ⊕ t) =
    interpTms (W₁Tms A σ) ⊕ interpTm (W₁Tm A t)
      ≡⟨ (λ i → interpW₁Tms A σ i ⊕ interpW₁Tm A t i) ⟩
    (interpTms σ ⊚ π) ⊕ (interpTm t ⟦ π ⟧)
      ≡⟨ ⊕⊚ (interpTms σ) (interpTm t) π ⁻¹ ⟩
    interpTms σ ⊕ interpTm t ⊚ π
      ∎

  private
    πlemTms : {Γ : Ctx} {A : Ty} → π ≡ interpTms (W₁Tms A (idTms Γ))
    πlemTms {Γ} {A} =
      π
        ≡⟨ πlem ⁻¹ ⟩
      interpRen (W₁Ren A (idRen Γ))
        ≡⟨ interpVarify (W₁Ren A (idRen Γ)) ⁻¹ ⟩
      interpTms (varify (W₁Ren A (idRen Γ)))
        ≡⟨ ap interpTms (Vlem2 (idRen Γ)) ⟩
      interpTms (W₁Tms A (idTms Γ))
        ∎

  interpTm (V v) =
    interpVar v
  interpTm (Lam t) =
    Λ (interpTm t)
  interpTm (App t s) =
    𝑎𝑝𝑝 (interpTm t) (interpTm s)
  interpTm (t [ σ ]) =
    interpTm t ⟦ interpTms σ ⟧
    
  interpTm (β {Γ} t s i) =
    (𝑎𝑝𝑝 (Λ (interpTm t)) (interpTm s)
      ≡⟨ 𝑎𝑝𝑝β (interpTm t) (interpTm s) ⟩
    interpTm t ⟦ 𝒾𝒹 (interpCtx Γ) ⊕ interpTm s ⟧
      ≡⟨ (λ j → interpTm t ⟦ interpId (~ j) ⊕ interpTm s ⟧) ⟩
    interpTm t ⟦ interpTms (idTms Γ) ⊕ interpTm s ⟧
      ∎) i
  interpTm (η {Γ} {A} t i) =
    (interpTm t
      ≡⟨ 𝑎𝑝𝑝η (interpTm t) ⟩
    Λ (𝑎𝑝𝑝 (interpTm t ⟦ π ⟧) 𝑧)
      ≡⟨ (λ i → Λ (𝑎𝑝𝑝 (interpTm t ⟦ πlemTms {A = A} i ⟧) 𝑧)) ⟩
    Λ (𝑎𝑝𝑝 (interpTm t ⟦ interpTms (W₁Tms A (idTms Γ)) ⟧) 𝑧)
      ∎) i
  interpTm (Zv[] σ t i) =
    𝑧β (interpTms σ) (interpTm t) i
  interpTm (Sv[] v σ t i) =
    (interpVar v ⟦ π ⟧ ⟦ interpTms (σ ⊕ t) ⟧
      ≡⟨ ⟦⟧⟦⟧ (interpVar v) π (interpTms (σ ⊕ t)) ⟩
    interpVar v ⟦ π ⊚ (interpTms σ ⊕ interpTm t) ⟧
      ≡⟨ ap (interpVar v ⟦_⟧) (πβ (interpTms σ) (interpTm t)) ⟩
    interpVar v ⟦ interpTms σ ⟧
      ∎) i
  interpTm (Lam[] {A = A} t σ i) =
    (Λ (interpTm t) ⟦ interpTms σ ⟧
      ≡⟨ Λnat (interpTm t) (interpTms σ) ⟩
    Λ (interpTm t ⟦ interpTms σ ⊚ π ⊕ 𝑧 ⟧)
      ≡⟨ (λ j → Λ (interpTm t ⟦ interpW₁Tms A σ (~ j) ⊕ 𝑧 ⟧)) ⟩
    Λ (interpTm t ⟦ interpTms (W₁Tms A σ) ⊕ 𝑧 ⟧)
      ∎) i
  interpTm (App[] t s σ i) =
    𝑎𝑝𝑝⟦⟧ (interpTm t) (interpTm s) (interpTms σ) i
  interpTm ([][] t σ τ i) =
    (interpTm t ⟦ interpTms σ ⟧ ⟦ interpTms τ ⟧
      ≡⟨ ⟦⟧⟦⟧ (interpTm t) (interpTms σ) (interpTms τ) ⟩
    interpTm t ⟦ interpTms σ ⊚ interpTms τ ⟧
      ≡⟨ ap (interpTm t ⟦_⟧) (interp∘Tms σ τ ⁻¹) ⟩
    interpTm t ⟦ interpTms (σ ∘Tms τ) ⟧
      ∎) i
  interpTm (trunc t s p q i j) =
    isSet→SquareP (λ i j → isSetTm)
      (λ k → interpTm (p k))
      (λ k → interpTm (q k))
      (λ k → interpTm t)
      (λ k → interpTm s) i j

  interpVarify ! = refl
  interpVarify (σ ⊕ v) = ap (_⊕ interpVar v) (interpVarify σ)

  interpW₁Tm {Γ} A t =
    interpTm t ⟦ interpTms (varify (W₁Ren A (idRen Γ))) ⟧
      ≡⟨ ap (interpTm t ⟦_⟧) (interpVarify (W₁Ren A (idRen Γ))) ⟩
    interpTm t ⟦ interpRen (W₁Ren A (idRen Γ)) ⟧
      ≡⟨ ap (interpTm t ⟦_⟧) πlem ⟩
    interpTm t ⟦ π ⟧
      ∎

  interp∘Tms ! τ = !η (! ⊚ interpTms τ)
  interp∘Tms (σ ⊕ t) τ = ap (_⊕ interpTm (t [ τ ])) (interp∘Tms σ τ)
