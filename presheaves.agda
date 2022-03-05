{-# OPTIONS --cubical #-}

module presheaves where

open import lists
open import contextual
open import ccc
open import normal
open import psh

private
  variable
    ℓ : Level

module Presheaves (𝒞 : Contextual ℓ ℓ) ⦃ 𝒞CCC : CCC 𝒞 ⦄
                  {X : Type ℓ} (base : X → Contextual.ty 𝒞) where
  open Normal 𝒞 base
  open Contextual 𝒞
  open Presheaf REN
  --open PShWeave REN
  open PSh
  open PShMor
  open PShMorCart

  𝑃𝑆ℎ = 𝒫𝒮𝒽

  private
    module P = Contextual 𝒫𝒮𝒽

  TM : (A : ty) → PSh
  sec (TM A) Γ = tm Γ A
  isSetSec (TM A) = isSetTm
  hom (TM A) σ t = t ⟦ makeRen σ ⟧
  id-hom (TM A) t = ap (t ⟦_⟧) 𝒾𝒹η₂ ∙ 𝒾𝒹⟦⟧ t
  ⊚-hom (TM A) σ τ t = ap (t ⟦_⟧) (make∘𝑅𝑒𝑛 σ τ) ∙ ⟦⟧⟦⟧ t (makeRen σ) (makeRen τ) ⁻¹

  {-TMS = plurify TM

  TMよ : {Γ : ctx} {A : ty} → tm Γ A → PShMor (TMS Γ) (TM A)
  ob (TMよ t) 𝓈s = t ⟦ ⇓ 𝓈s ⟧
  nat (TMよ {Γ} t) σ 𝓈s =
    t ⟦ ⇓ (homs (TMS Γ) σ 𝓈s) ⟧
      ≡⟨ ap (t ⟦_⟧) (⇓hom σ 𝓈s) ⟩
    t ⟦ ⇓ 𝓈s ⊚ makeRen σ ⟧
      ≡⟨ ⟦⟧⟦⟧ t (⇓ 𝓈s) (makeRen σ) ⁻¹ ⟩
    t ⟦ ⇓ 𝓈s ⟧ ⟦ makeRen σ ⟧
      ∎

  TMSよ : {Γ Δ : ctx} → tms Γ Δ → PShMors (TMS Γ) (TMS Δ)
  TMSよ = map𝐸𝑙𝑠₁ TMよ

  ⇓TMSよ : {Γ Δ Σ : ctx} (σ : tms Γ Δ) (𝓈s : secs (TMS Γ) Σ) →
    ⇓ (obs (TMSよ σ) 𝓈s) ≡ σ ⊚ ⇓ 𝓈s
  ⇓TMSよ ! 𝓈s = refl
  ⇓TMSよ (σ ⊕ t) 𝓈s i  = ⇓TMSよ σ 𝓈s i ⊕ t ⟦ ⇓ 𝓈s ⟧

  TMよ⟦⟧ : {Γ Δ : ctx} {A : ty} (t : tm Δ A) (σ : tms Γ Δ) →
    TMよ (t ⟦ σ ⟧) ≡ TMよ t P.⟦ TMSよ σ ⟧
  TMよ⟦⟧ t σ =
    ≡PShMor
      (λ 𝓈s →
        t ⟦ σ ⟧ ⟦ ⇓ 𝓈s ⟧
          ≡⟨ ⟦⟧⟦⟧ t σ (⇓ 𝓈s) ⟩
        t ⟦ σ ⊚ ⇓ 𝓈s ⟧
          ≡⟨ ap (t ⟦_⟧) (⇓TMSよ σ 𝓈s ⁻¹) ⟩
        t ⟦ ⇓ (obs (TMSよ σ) 𝓈s) ⟧
          ∎)-}

  NE : ty → PSh
  sec (NE A) Γ = Ne Γ A
  isSetSec (NE A) = isSetNeutral
  hom (NE A) σ M = M [ σ ]NE
  id-hom (NE A) = [id]NE
  ⊚-hom (NE A) σ τ M = [][]NE M σ τ ⁻¹

  NF : ty → PSh
  sec (NF A) Γ = Nf Γ A
  isSetSec (NF A) = isSetNormal
  hom (NF A) σ N = N [ σ ]NF
  id-hom (NF A) = [id]NF
  ⊚-hom (NF A) σ τ N = [][]NF N σ τ ⁻¹

  ιNE : (A : ty) → PShMorCart (NE A) (TM A)
  ob (ιNE A) = ιNe
  nat (ιNE A) σ M = ιNeLem M σ

  ιNF : (A : ty) → PShMorCart (NF A) (TM A)
  ob (ιNF A) = ιNf
  nat (ιNF A) σ N = ιNfLem N σ

  
