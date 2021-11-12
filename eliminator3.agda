{-# OPTIONS --cubical #-}

module eliminator3 where

open import contextual
open import cartesian2
open import syn3
open import ren2

open import Agda.Builtin.Char
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

-- We construct a canonical contextual functor from σιν to any CCC 𝒞

module Eliminator {ℓ₁ ℓ₂} (𝒞 : Contextual ℓ₁ ℓ₂) ⦃ CCC𝒞 : CCC 𝒞 ⦄
                  (base : (c : Char) → Contextual.ty 𝒞) where

  open Contextual 𝒞
  open CCC CCC𝒞

  interpTy : Ty → ty
  interpTy (Base X) = base X
  interpTy (A ⇒ B) = (interpTy A) ⇛ (interpTy B)
  
  interpCtx : Ctx → ctx
  interpCtx Γ = map𝐶𝑡𝑥 interpTy Γ

  trVar = tr𝑉𝑎𝑟 interpTy

  interpVar : {Γ : Ctx} {A : Ty} (v : Var Γ A) → tm (interpCtx Γ) (interpTy A)
  interpVar v = makeVar (tr𝑉𝑎𝑟 interpTy v)

  interpRen : {Γ Δ : Ctx} (σ : Ren Γ Δ) → tms (interpCtx Γ) (interpCtx Δ)
  interpRen = map𝑇𝑚𝑠₁ interpVar

  interpIdRen : {Γ : Ctx} → interpRen (idRen Γ) ≡ 𝒾𝒹 (interpCtx Γ)
  interpIdRen {Γ} =
    map𝑇𝑚𝑠₁ (λ v → makeVar (tr𝑉𝑎𝑟 interpTy v)) (idRen Γ)
      ≡⟨ map𝑇𝑚𝑠comp₂ makeVar (tr𝑉𝑎𝑟 interpTy) (idRen Γ) ⁻¹ ⟩
    makeRen (tr𝑅𝑒𝑛 interpTy (idRen Γ))
      ≡⟨ (λ i → makeRen (trId interpTy Γ i)) ⟩
    makeRen (id𝑅𝑒𝑛 (map𝐶𝑡𝑥 interpTy Γ))
      ≡⟨ 𝒾𝒹η₂ ⟩
    𝒾𝒹 (map𝐶𝑡𝑥 interpTy Γ)
      ∎

  interpW₁Ren : {Γ Δ : Ctx} {A : Ty} (σ : Ren Γ Δ) →
    interpRen (W₁Ren A σ) ≡ interpRen σ ⊚ π
  interpW₁Ren ! = refl
  interpW₁Ren {Γ} {Δ} {A} (σ ⊕ v) i = interpW₁Ren {A = A} σ i ⊕ make𝑠𝑣 (tr𝑉𝑎𝑟 interpTy v) i

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

  interpTm  : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → tm (interpCtx Γ) (interpTy A)

  {-# TERMINATING #-}
  interpTms : {Γ Δ : Ctx} (σ : Tms Γ Δ) → tms  (interpCtx Γ)  (interpCtx Δ)
  interpTms = map𝑇𝑚𝑠₁ interpTm

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
  interpTm (𝑧𝑣[] σ t i) =
    𝑧β (interpTms (σ ⊕ t)) i
  interpTm (𝑠𝑣[] v σ t i) =
    W₁⟦⟧ (tr𝑉𝑎𝑟 interpTy v) (interpTms σ) (interpTm t) i
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

  open ContextualFunctor

  elim : ContextualFunctor σιν 𝒞
  CF-ty elim = interpTy
  CF-tm elim = interpTm
  CF-id elim = interpId
  CF-sub elim t σ = refl

  elimAmb : Functor SYN ambCat
  elimAmb = ambFun elim
