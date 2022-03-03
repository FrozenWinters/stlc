{-# OPTIONS --cubical --allow-unsolved-metas #-}

module twgl where

open import lists
open import contextual
open import ccc
open import normal
open import psh

module TwGlCC {ℓ} (𝒞 : Contextual ℓ ℓ) ⦃ 𝒞CCC : CCC 𝒞 ⦄
                  {X : Type ℓ} (base : X → Contextual.ty 𝒞) where
  open Presheaf (Contextual.REN 𝒞)
  open Contextual 𝒞
  open Normal 𝒞 base

  open PSh
  open PShMor
  open PShMorCart

  private
    module P = Contextual 𝒫𝒮𝒽

  record GlTy : Type (lsuc ℓ) where
    constructor Gl
    field
      Gl-A : ty
      Gl-⦇A⦈ : P.ty
      Gl-u : PShMorCart (NE Gl-A) Gl-⦇A⦈
      Gl-q : PShMorCart Gl-⦇A⦈ (NF Gl-A)

    ⟪Gl-u⟫ : {Δ : ctx} → Ne Δ Gl-A → sec Gl-⦇A⦈ Δ
    ⟪Gl-u⟫ = ob Gl-u

    ⟪Gl-q⟫ : {Δ : ctx} → sec Gl-⦇A⦈ Δ → Nf Δ Gl-A
    ⟪Gl-q⟫ = ob Gl-q

    field
      Gl-comp : {Γ : ctx} (M : Ne Γ Gl-A) →
        (ιNf ∘ ⟪Gl-q⟫ ∘ ⟪Gl-u⟫) M ≡ ιNe M

  GlCtx = 𝐶𝑡𝑥 GlTy

  open GlTy
  
  Gls-Γ : GlCtx → ctx
  Gls-Γ = map𝐶𝑡𝑥 Gl-A

  Gls-⦇Γ⦈ : GlCtx → P.ctx
  Gls-⦇Γ⦈ = map𝐶𝑡𝑥 Gl-⦇A⦈

  ⟪Gls-u⟫ : (Γ : GlCtx) {Δ : ctx} → Nes Δ (Gls-Γ Γ) → secs (Gls-⦇Γ⦈ Γ) Δ
  ⟪Gls-u⟫ ∅ MS = !
  ⟪Gls-u⟫ (Γ ⊹ A) (MS ⊕ M) = ⟪Gls-u⟫ Γ MS ⊕ ob (Gl-u A) M

  ⟪Gls-q⟫ : (Γ : GlCtx) {Δ : ctx} → secs (Gls-⦇Γ⦈ Γ) Δ → Nfs Δ (Gls-Γ Γ)
  ⟪Gls-q⟫ ∅ 𝓈s = !
  ⟪Gls-q⟫ (Γ ⊹ A) (𝓈s ⊕ 𝓈) = ⟪Gls-q⟫ Γ 𝓈s ⊕ ob (Gl-q A) 𝓈

  Gls-q-nat : (Γ : GlCtx) {Δ Σ : ctx} (σ : IntRen Δ Σ) (𝓈s : secs (Gls-⦇Γ⦈ Γ) Σ) →
    ⟪Gls-q⟫ Γ (homs (Gls-⦇Γ⦈ Γ) σ 𝓈s) ≡ ⟪Gls-q⟫ Γ 𝓈s [ σ ]NFS
  Gls-q-nat ∅ σ 𝓈s = refl
  Gls-q-nat (Γ ⊹ A) σ (𝓈s ⊕ 𝓈) i = Gls-q-nat Γ σ 𝓈s i ⊕ nat (Gl-q A) σ 𝓈 i

  Gls-comp : (Γ : GlCtx) {Δ : ctx} (MS : Nes Δ (Gls-Γ Γ)) →
    (ιNfs ∘ ⟪Gls-q⟫ Γ ∘ ⟪Gls-u⟫ Γ) MS ≡ ιNes MS
  Gls-comp ∅ ! = refl
  Gls-comp (Γ ⊹ A) (MS ⊕ M) i = Gls-comp Γ MS i ⊕ Gl-comp A M i

  record GlTm (Γ : GlCtx) (A : GlTy) : Type (lsuc ℓ) where
    field
      GlTm-⦇α⦈ : P.tm (Gls-⦇Γ⦈ Γ) (Gl-⦇A⦈ A)
      GlTm-α : tm (Gls-Γ Γ) (Gl-A A)

    ⟪GlTm-⦇α⦈⟫ : {Δ : ctx} → secs (Gls-⦇Γ⦈ Γ) Δ → sec (Gl-⦇A⦈ A) Δ
    ⟪GlTm-⦇α⦈⟫ = ob GlTm-⦇α⦈

    field
      GlTm-nat : {Δ : ctx} (𝓈s : secs (Gls-⦇Γ⦈ Γ) Δ) →
        (ιNf ∘ ⟪Gl-q⟫ A ∘ ⟪GlTm-⦇α⦈⟫) 𝓈s ≡ GlTm-α ⟦ (ιNfs ∘ ⟪Gls-q⟫ Γ) 𝓈s ⟧

    GlTm-norm :  Nf (Gls-Γ Γ) (Gl-A A)
    GlTm-norm = (⟪Gl-q⟫ A ∘ ⟪GlTm-⦇α⦈⟫ ∘ ⟪Gls-u⟫ Γ) (idNes (Gls-Γ Γ))

    GlTm-correctness : ιNf GlTm-norm ≡ GlTm-α
    GlTm-correctness =
      (ιNf ∘ ⟪Gl-q⟫ A ∘ ⟪GlTm-⦇α⦈⟫) (⟪Gls-u⟫ Γ (idNes (Gls-Γ Γ)))
        ≡⟨ GlTm-nat (⟪Gls-u⟫ Γ (idNes (Gls-Γ Γ))) ⟩
      GlTm-α ⟦ (ιNfs ∘ ⟪Gls-q⟫ Γ ∘ ⟪Gls-u⟫ Γ) (idNes (Gls-Γ Γ)) ⟧
        ≡⟨ ap (GlTm-α ⟦_⟧) (Gls-comp Γ (idNes (Gls-Γ Γ))) ⟩
      GlTm-α ⟦ ιNes (idNes (Gls-Γ Γ)) ⟧
        ≡⟨ ap (GlTm-α ⟦_⟧) (ιIdNes (Gls-Γ Γ)) ⟩
      GlTm-α ⟦ 𝒾𝒹 (Gls-Γ Γ) ⟧
        ≡⟨ 𝒾𝒹⟦⟧ GlTm-α ⟩
      GlTm-α
        ∎

  GlTms = 𝑇𝑚𝑠 GlTm

  open GlTm

  GlTms-⦇αs⦈ : {Γ Δ : GlCtx} (σ : GlTms Γ Δ) → P.tms (Gls-⦇Γ⦈ Γ) (Gls-⦇Γ⦈ Δ)
  GlTms-⦇αs⦈ = map𝐸𝑙𝑠₁ GlTm-⦇α⦈

  ⟪GlTms-⦇αs⦈⟫ : {Γ Δ : GlCtx} (σ : GlTms Γ Δ) {Σ : ctx} →
    secs (Gls-⦇Γ⦈ Γ) Σ → secs (Gls-⦇Γ⦈ Δ) Σ
  ⟪GlTms-⦇αs⦈⟫ σ = obs (GlTms-⦇αs⦈ σ)

  GlTms-αs : {Γ Δ : GlCtx} (σ : GlTms Γ Δ) → tms (Gls-Γ Γ) (Gls-Γ Δ)
  GlTms-αs = map𝐸𝑙𝑠₁ GlTm-α

  GlTms-nat : {Γ Δ : GlCtx} (σ : GlTms Γ Δ) {Σ : ctx} (𝓈s : secs (Gls-⦇Γ⦈ Γ) Σ) →
    (ιNfs ∘ ⟪Gls-q⟫ Δ ∘ ⟪GlTms-⦇αs⦈⟫ σ) 𝓈s ≡ GlTms-αs σ ⊚ (ιNfs ∘ ⟪Gls-q⟫ Γ) 𝓈s
  GlTms-nat ! 𝓈s = refl
  GlTms-nat (σ ⊕ t) 𝓈s i = GlTms-nat σ 𝓈s i ⊕ GlTm-nat t 𝓈s i

  _[_]Gl : {Γ Δ : GlCtx} {A : GlTy} (t : GlTm Δ A) (σ : GlTms Γ Δ) → GlTm Γ A
  GlTm-⦇α⦈ (t [ σ ]Gl) = GlTm-⦇α⦈ t P.⟦ GlTms-⦇αs⦈ σ ⟧
  GlTm-α (t [ σ ]Gl) = GlTm-α t ⟦ GlTms-αs σ ⟧
  GlTm-nat (_[_]Gl {Γ} {Δ} {A} t σ) 𝓈s =
    ιNf (⟪Gl-q⟫ A (⟪GlTm-⦇α⦈⟫ t (⟪GlTms-⦇αs⦈⟫ σ 𝓈s)))
      ≡⟨ GlTm-nat t (⟪GlTms-⦇αs⦈⟫ σ 𝓈s) ⟩
    GlTm-α t ⟦ ιNfs (⟪Gls-q⟫ Δ (⟪GlTms-⦇αs⦈⟫ σ 𝓈s)) ⟧
      ≡⟨ ap (GlTm-α t ⟦_⟧) (GlTms-nat σ 𝓈s) ⟩
    GlTm-α t ⟦ GlTms-αs σ ⊚ ιNfs (⟪Gls-q⟫ Γ 𝓈s) ⟧
      ≡⟨ ⟦⟧⟦⟧ (GlTm-α t) (GlTms-αs σ) (ιNfs (⟪Gls-q⟫ Γ 𝓈s)) ⁻¹ ⟩
    GlTm-α t ⟦ GlTms-αs σ ⟧ ⟦ ιNfs (⟪Gls-q⟫ Γ 𝓈s) ⟧
      ∎

  _∘GlTms_ : {Γ Δ Σ : GlCtx} → GlTms Δ Σ → GlTms Γ Δ → GlTms Γ Σ
  σ ∘GlTms τ = map𝐸𝑙𝑠 _[ τ ]Gl σ

  Gl-⦇αs⦈∘ : {Γ Δ Σ : GlCtx} (σ : GlTms Δ Σ) (τ : GlTms Γ Δ) →
    GlTms-⦇αs⦈ (σ ∘GlTms τ) ≡ GlTms-⦇αs⦈ σ P.⊚ GlTms-⦇αs⦈ τ
  Gl-⦇αs⦈∘ ! τ = refl
  Gl-⦇αs⦈∘ (σ ⊕ t) τ i = Gl-⦇αs⦈∘ σ τ i ⊕ GlTm-⦇α⦈ t P.⟦ GlTms-⦇αs⦈ τ ⟧

  Gl-αs∘ : {Γ Δ Σ : GlCtx} (σ : GlTms Δ Σ) (τ : GlTms Γ Δ) →
    GlTms-αs (σ ∘GlTms τ) ≡ GlTms-αs σ ⊚ GlTms-αs τ
  Gl-αs∘ ! τ = refl
  Gl-αs∘ (σ ⊕ t) τ i = Gl-αs∘ σ τ i ⊕ GlTm-α t ⟦ GlTms-αs τ ⟧

  𝑧GlTm : {Γ : GlCtx} {A : GlTy} → GlTm (Γ ⊹ A) A
  GlTm-⦇α⦈ 𝑧GlTm = 𝑧PSh
  GlTm-α 𝑧GlTm = 𝑧
  GlTm-nat (𝑧GlTm {Γ} {A}) (𝓈s ⊕ 𝓈) = 𝑧⟦⟧ (ιNfs (⟪Gls-q⟫ (Γ ⊹ A) (𝓈s ⊕ 𝓈))) ⁻¹

  W₁GlTm : {Γ : GlCtx} {B : GlTy} (A : GlTy) → GlTm Γ B → GlTm (Γ ⊹ A) B
  GlTm-⦇α⦈ (W₁GlTm A t) = W₁PSh (Gl-⦇A⦈ A) (GlTm-⦇α⦈ t)
  GlTm-α (W₁GlTm A t) = W₁tm (Gl-A A) (GlTm-α t)
  GlTm-nat (W₁GlTm {Γ} {B} A t) (𝓈s ⊕ 𝓈) =
    ιNf (⟪Gl-q⟫ B (⟪GlTm-⦇α⦈⟫ t 𝓈s))
      ≡⟨ GlTm-nat t 𝓈s ⟩
    GlTm-α t ⟦ ιNfs (⟪Gls-q⟫ Γ 𝓈s) ⟧
      ≡⟨ Wtm⟦⟧ (GlTm-α t) (ιNfs (⟪Gls-q⟫ Γ 𝓈s)) (ιNf (⟪Gl-q⟫ A 𝓈)) ⁻¹ ⟩
    W₁tm (Gl-A A) (GlTm-α t) ⟦ ιNfs (⟪Gls-q⟫ (Γ ⊹ A) (𝓈s ⊕ 𝓈)) ⟧
      ∎

  W₁GlTms : {Γ Δ : GlCtx} (A : GlTy) → GlTms Γ Δ → GlTms (Γ ⊹ A) Δ
  W₁GlTms A σ = map𝐸𝑙𝑠 (W₁GlTm A) σ

  W₂GlTms : {Γ Δ : GlCtx} (A : GlTy) → GlTms Γ Δ → GlTms (Γ ⊹ A) (Δ ⊹ A)
  W₂GlTms A σ = W₁GlTms A σ ⊕ 𝑧GlTm

  idGl : (Γ : GlCtx) → GlTms Γ Γ
  idGl ∅ = !
  idGl (Γ ⊹ A) = W₂GlTms A (idGl Γ)

  ≡GlTm : {Γ : GlCtx} {A : GlTy} {t s : GlTm Γ A} →
    GlTm-⦇α⦈ t ≡ GlTm-⦇α⦈ s → GlTm-α t ≡ GlTm-α s → t ≡ s
  GlTm-⦇α⦈ (≡GlTm p q i) = p i
  GlTm-α (≡GlTm p q i) = q i
  GlTm-nat (≡GlTm {Γ} {A} {t} {s} p q i) 𝓈s j =
    isSet→SquareP (λ i j → isSetTm)
      (GlTm-nat t 𝓈s)
      (GlTm-nat s 𝓈s)
      (λ k → (ιNf ∘ ⟪Gl-q⟫ A ∘ ob (p k)) 𝓈s)
      (λ k → q k ⟦ (ιNfs ∘ ⟪Gls-q⟫ Γ) 𝓈s ⟧) i j

  WGlLem1 : {Γ Δ : GlCtx} {A B : GlTy} (t : GlTm Δ B) (τ : GlTms Γ Δ) (s : GlTm Γ A) →
    W₁GlTm A t [ τ ⊕ s ]Gl ≡ t [ τ ]Gl
  WGlLem1 t τ s =
    ≡GlTm
      (WPShLem1 (GlTm-⦇α⦈ t) (GlTms-⦇αs⦈ τ) (GlTm-⦇α⦈ s))
      (Wtm⟦⟧ (GlTm-α t) (GlTms-αs τ) (GlTm-α s))

  WGlLem2 : {Γ Δ Σ : GlCtx} {A : GlTy} (σ : GlTms Δ Σ) (τ : GlTms Γ Δ) (s : GlTm Γ A) →
    W₁GlTms A σ ∘GlTms (τ ⊕ s) ≡ σ ∘GlTms τ
  WGlLem2 ! τ s = refl
  WGlLem2 (σ ⊕ t) τ s i = WGlLem2 σ τ s i ⊕ WGlLem1 t τ s i

  𝑧GlLem : {Γ Δ : GlCtx} {A : GlTy} (σ : GlTms Γ Δ) (t : GlTm Γ A) →
    𝑧GlTm [ σ ⊕ t ]Gl ≡ t
  𝑧GlLem σ t =
    ≡GlTm
      (𝑧PShLem (GlTms-⦇αs⦈ σ) (GlTm-⦇α⦈ t))
      (𝑧⟦⟧ (GlTms-αs (σ ⊕ t)))

  idLGl : {Γ Δ : GlCtx} (σ : GlTms Γ Δ) → idGl Δ ∘GlTms σ ≡ σ
  idLGl ! = refl
  idLGl {Δ = Δ ⊹ A} (σ ⊕ t) =
    W₂GlTms A (idGl Δ) ∘GlTms (σ ⊕ t)
      ≡⟨ (λ i → WGlLem2 (idGl Δ) σ t i ⊕ 𝑧GlLem σ t i) ⟩
    (idGl Δ ∘GlTms σ) ⊕ t
      ≡⟨ ap (_⊕ t) (idLGl σ) ⟩
    σ ⊕ t
      ∎

  idTwGl-⦇αs⦈ : (Γ : GlCtx) → GlTms-⦇αs⦈ (idGl Γ) ≡ P.𝒾𝒹 (Gls-⦇Γ⦈ Γ)
  idTwGl-⦇αs⦈ ∅ = refl
  idTwGl-⦇αs⦈ (Γ ⊹ A) =
    GlTms-⦇αs⦈ (W₁GlTms A (idGl Γ)) ⊕ 𝑧PSh
      ≡⟨ ap (_⊕ 𝑧PSh) (map𝐸𝑙𝑠comp₁ GlTm-⦇α⦈ (W₁GlTm A) (idGl Γ)) ⟩
    map𝐸𝑙𝑠₁ (W₁PSh (Gl-⦇A⦈ A) ∘ GlTm-⦇α⦈) (idGl Γ) ⊕ 𝑧PSh
      ≡⟨ ap (_⊕ 𝑧PSh) (map𝐸𝑙𝑠comp₂ (W₁PSh (Gl-⦇A⦈ A)) GlTm-⦇α⦈ (idGl Γ) ⁻¹) ⟩
    W₁PShs (Gl-⦇A⦈ A) (GlTms-⦇αs⦈ (idGl Γ)) ⊕ 𝑧PSh
      ≡⟨ (λ i → W₁PShs (Gl-⦇A⦈ A) (idTwGl-⦇αs⦈ Γ i) ⊕ 𝑧PSh) ⟩
    P.𝒾𝒹 (Gls-⦇Γ⦈ (Γ ⊹ A))
      ∎

  idTwGl-αs : (Γ : GlCtx) → GlTms-αs (idGl Γ) ≡ 𝒾𝒹 (Gls-Γ Γ)
  idTwGl-αs ∅ = !η (𝒾𝒹 ∅)
  idTwGl-αs (Γ ⊹ A) =
    GlTms-αs (W₁GlTms A (idGl Γ)) ⊕ 𝑧
      ≡⟨ ap (_⊕ 𝑧) (map𝐸𝑙𝑠comp₁ GlTm-α (W₁GlTm A) (idGl Γ)) ⟩
    map𝐸𝑙𝑠₁ (W₁tm (Gl-A A) ∘ GlTm-α) (idGl Γ) ⊕ 𝑧
      ≡⟨ ap (_⊕ 𝑧) (map𝐸𝑙𝑠comp₂ (W₁tm (Gl-A A)) GlTm-α (idGl Γ) ⁻¹) ⟩
    W₁tms (Gl-A A) (GlTms-αs (idGl Γ)) ⊕ 𝑧
      ≡⟨ (λ i → W₁tms (Gl-A A) (idTwGl-αs Γ i) ⊕ 𝑧) ⟩
    W₁tms (Gl-A A) (𝒾𝒹 (Gls-Γ Γ)) ⊕ 𝑧
      ≡⟨ ap (_⊕ 𝑧) (𝒾𝒹L π) ⟩
    π ⊕ 𝑧
      ≡⟨ 𝒾𝒹η₁ ⟩
    𝒾𝒹 (Gls-Γ (Γ ⊹ A))
      ∎

  id[]Gl : {Γ : GlCtx} {A : GlTy} (t : GlTm Γ A) → t [ idGl Γ ]Gl ≡ t
  id[]Gl {Γ} t =
    ≡GlTm
      (GlTm-⦇α⦈ t P.⟦ GlTms-⦇αs⦈ (idGl Γ) ⟧
        ≡⟨ ap (GlTm-⦇α⦈ t P.⟦_⟧) (idTwGl-⦇αs⦈ Γ) ⟩
      GlTm-⦇α⦈ t P.⟦ P.𝒾𝒹 (Gls-⦇Γ⦈ Γ) ⟧
        ≡⟨ P.𝒾𝒹⟦⟧ (GlTm-⦇α⦈ t) ⟩
      GlTm-⦇α⦈ t
        ∎)
      (GlTm-α t ⟦ GlTms-αs (idGl Γ) ⟧
        ≡⟨ ap (GlTm-α t ⟦_⟧) (idTwGl-αs Γ) ⟩
      GlTm-α t ⟦ 𝒾𝒹 (Gls-Γ Γ) ⟧
        ≡⟨ 𝒾𝒹⟦⟧ (GlTm-α t) ⟩
      GlTm-α t
        ∎)

  [][]TwGl : {Γ Δ Σ : GlCtx} {A : GlTy} (t : GlTm Σ A) (σ : GlTms Δ Σ) (τ : GlTms Γ Δ) →
    t [ σ ]Gl [ τ ]Gl ≡ t [ σ ∘GlTms τ ]Gl
  [][]TwGl t σ τ =
    ≡GlTm
      (GlTm-⦇α⦈ t P.⟦ GlTms-⦇αs⦈ σ ⟧ P.⟦ GlTms-⦇αs⦈ τ ⟧
        ≡⟨ P.⟦⟧⟦⟧ (GlTm-⦇α⦈ t) (GlTms-⦇αs⦈ σ) (GlTms-⦇αs⦈ τ) ⟩
      GlTm-⦇α⦈ t P.⟦ GlTms-⦇αs⦈ σ P.⊚ GlTms-⦇αs⦈ τ ⟧
        ≡⟨ ap (GlTm-⦇α⦈ t P.⟦_⟧) (Gl-⦇αs⦈∘ σ τ ⁻¹) ⟩
      GlTm-⦇α⦈ t P.⟦ GlTms-⦇αs⦈ (σ ∘GlTms τ) ⟧
        ∎)
      (GlTm-α t ⟦ GlTms-αs σ ⟧ ⟦ GlTms-αs τ ⟧
        ≡⟨ ⟦⟧⟦⟧ (GlTm-α t) (GlTms-αs σ) (GlTms-αs τ) ⟩
      GlTm-α t ⟦ GlTms-αs σ ⊚ GlTms-αs τ ⟧
        ≡⟨ ap (GlTm-α t ⟦_⟧) (Gl-αs∘ σ τ ⁻¹) ⟩
      GlTm-α t ⟦ GlTms-αs (σ ∘GlTms τ) ⟧
        ∎)

  isSetGlTm : {Γ : GlCtx} {A : GlTy} → isSet (GlTm Γ A)
  isSetGlTm = {!!}

  private
    module D = Contextual

  TwGl : Contextual (lsuc ℓ) (lsuc ℓ)
  D.ty TwGl = GlTy
  D.tm TwGl = GlTm
  D._⟦_⟧ TwGl = _[_]Gl
  D.𝒾𝒹 TwGl = idGl
  D.𝒾𝒹L TwGl = idLGl
  D.𝒾𝒹⟦⟧ TwGl = id[]Gl
  D.⟦⟧⟦⟧ TwGl = [][]TwGl
  D.isSetTm TwGl = isSetGlTm

  
