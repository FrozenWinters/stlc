{-# OPTIONS --cubical #-}

module presheaves where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Data.Unit as ⊤ renaming (Unit to ⊤)
open import Cubical.Categories.Instances.Sets

open import contextual
open import ccc
open import cart
open import normal
open import psh

module Presheaves {ℓ} (𝒞 : Contextual ℓ ℓ) ⦃ 𝒞CCC : CCC 𝒞 ⦄ (base : Char → Contextual.ty 𝒞) where
  module _ where
    open Contextual

    instance
      isCatTMS : isCategory (ambCat 𝒞)
      isCatTMS = isCatAmbCat 𝒞
      
      isCatREN : isCategory (REN 𝒞)
      isCatREN = isCatAmbCat (ρεν 𝒞)

  module _ where
    open Contextual 𝒞

    𝑅𝐸𝑁 = REN

    infixr 20 _𝒩∘_
    _𝒩∘_ = comp' (PSh REN)

    𝑃𝑆ℎ = PSh REN

  -- Re-binding names to force instance argument resolution and speed up type-checking
  
  module _ where
    open Enveloping 𝑃𝑆ℎ

    𝒫𝒮𝒽 : Contextual (lsuc ℓ) ℓ
    𝒫𝒮𝒽 = envCC

    𝒫𝒮𝒽CCC : CCC 𝒫𝒮𝒽
    𝒫𝒮𝒽CCC = envCCC

    open Contextual 𝒫𝒮𝒽
    open Precategory 𝑃𝑆ℎ renaming (_∘_ to _𝒞∘_; id to 𝑖𝑑)
    open Cartesian (PShCart {𝒞 = 𝑅𝐸𝑁})

    ⇓PShCtx : ctx → ob
    ⇓PShCtx = ⇓EnvCtx

    ⇓PShTms : {Γ Δ : ctx} → tms Γ Δ → 𝑃𝑆ℎ [ ⇓PShCtx Γ , ⇓PShCtx Δ ]
    ⇓PShTms = ⇓EnvTms

    ⇓PShπ : {Γ : ctx} {A : ty} → ⇓PShTms {Δ = Γ} π ≡ C-π₁ (⇓PShCtx Γ) A
    ⇓PShπ {Γ} = ⇓Envπ {Γ}

    ⇓PSh∘ : {Γ Δ Σ : ctx} (σ : tms Δ Σ) (τ : tms Γ Δ) →
      ⇓PShTms (σ ⊚ τ) ≡ ⇓PShTms σ 𝒞∘ ⇓PShTms τ
    ⇓PSh∘ = ⇓Env∘

    ⇓PSh𝒾𝒹 : (Γ : ctx) → ⇓PShTms (𝒾𝒹 Γ) ≡ 𝑖𝑑 (⇓PShCtx Γ)
    ⇓PSh𝒾𝒹 = ⇓Env𝒾𝒹

    _×PSh_ : {Γ Δ : ctx} {A B : ty} → tms Γ Δ → Hom[ A , B ] → tms (Γ ⊹ A) (Δ ⊹ B)
    _×PSh_ = _×tm_

    ×PShLem1 : {Γ Δ Σ : ctx} {A B : ty} (σ : tms Δ Σ) (t : Hom[ A , B ])
      (τ : tms Γ Δ) (s : tm Γ A ) →
      (σ ×tm t) ⊚ (τ ⊕ s) ≡ (σ ⊚ τ) ⊕ (t 𝒞∘ s)
    ×PShLem1 = ×tmLem1

    ×PShLem2 : {Γ Δ Σ : ctx} {A B C : ty} (σ : tms Δ Σ) (t : Hom[ B , C ])
      (τ : tms Γ Δ) (s : Hom[ A , B ]) →
      (σ ×tm t) ⊚ (τ ×tm s) ≡ (σ ⊚ τ) ×tm (t 𝒞∘ s)
    ×PShLem2 = ×tmLem2

    ×PShInd : {Γ Δ : ctx} {A B : ty} (σ : tms Γ Δ) (s : Hom[ A , B ]) →
      ⇓PShTms (σ ×tm s) ≡ C-pair (⇓PShTms σ 𝒞∘ C-π₁ (⇓PShCtx Γ) A) (s 𝒞∘ C-π₂ (⇓PShCtx Γ) A)
    ×PShInd = ×IndLem

    plurifyPSh = plurify
    weaveHomPSh = weaveHom

  open Contextual 𝒞
  open Precategory
  open Functor

  private
    module P = Contextual 𝒫𝒮𝒽
  
  𝒯ℳ : (A : ty) → ob (PSh ambCat)
  F-ob (𝒯ℳ A) Γ = tm Γ A , isSetTm
  F-hom (𝒯ℳ A) σ t = t ⟦ σ ⟧
  F-id (𝒯ℳ A) i t = 𝒾𝒹⟦⟧ t i
  F-seq (𝒯ℳ A) σ τ i t = ⟦⟧⟦⟧ t σ τ (~ i)

  TM : (A : ty) → ob 𝑃𝑆ℎ
  TM A = funcComp (𝒯ℳ A) (ιREN 𝒞 ^opF)

  TMS = plurifyPSh TM

  ⇓TMS : {Γ Δ : ctx} → fst (F-ob (⇓PShCtx (TMS Δ)) Γ) → tms Γ Δ
  ⇓TMS {Γ} {∅} 𝓈 = !
  ⇓TMS {Γ} {Δ ⊹ A} (𝓈 , t) = ⇓TMS 𝓈 ⊕ t

  ⇓TMSHom : {Γ Δ Σ : ctx} (σ : IntRen Σ Δ) (𝓈 : fst (F-ob (⇓PShCtx (TMS Γ)) Δ)) →
    ⇓TMS {Σ} {Γ} (F-hom (⇓PShCtx (TMS Γ)) σ 𝓈) ≡ ⇓TMS 𝓈 ⊚ makeRen σ
  ⇓TMSHom {∅} σ 𝓈 = refl
  ⇓TMSHom {Γ ⊹ A} σ (𝓈 , t) i = ⇓TMSHom σ 𝓈 i ⊕ t ⟦ makeRen σ ⟧

  open NatTrans

  TMよ : {Γ : ctx} {A : ty} → tm Γ A → P.tm (TMS Γ) (TM A)
  N-ob (TMよ t) Γ 𝓈 = t ⟦ ⇓TMS 𝓈 ⟧
  N-hom (TMよ {Γ} t) σ i 𝓈 =
    (t ⟦ ⇓TMS (F-hom (⇓PShCtx (TMS Γ)) σ 𝓈) ⟧
      ≡⟨ ap (t ⟦_⟧) (⇓TMSHom σ 𝓈) ⟩
    t ⟦ ⇓TMS 𝓈 ⊚ makeRen σ ⟧
      ≡⟨ ⟦⟧⟦⟧ t (⇓TMS 𝓈) (makeRen σ) ⁻¹ ⟩
    t ⟦ ⇓TMS 𝓈 ⟧ ⟦ makeRen σ ⟧
      ∎) i

  TMSよ : {Γ Δ : ctx} → tms Γ Δ → P.tms (TMS Γ) (TMS Δ)
  TMSよ = map𝑇𝑚𝑠₁ TMよ

  ⇓TMSよOb : {Γ Δ Σ : ctx} (σ : tms Γ Δ) (𝓈 : fst (F-ob (⇓PShCtx (TMS Γ)) Σ)) →
    ⇓TMS (N-ob (⇓PShTms (TMSよ σ)) Σ 𝓈) ≡ σ ⊚ (⇓TMS 𝓈)
  ⇓TMSよOb ! 𝓈 = refl
  ⇓TMSよOb (σ ⊕ t) 𝓈 i = ⇓TMSよOb σ 𝓈 i ⊕ t ⟦ ⇓TMS 𝓈 ⟧

  private
    TMよ⟦⟧lem : {Γ Δ : ctx} {A : ty} (t : tm Δ A) (σ : tms Γ Δ) →
      N-ob (TMよ (t ⟦ σ ⟧)) ≡ N-ob (TMよ t P.⟦ TMSよ σ ⟧)
    TMよ⟦⟧lem t σ i Γ 𝓈 =
      (t ⟦ σ ⟧ ⟦ ⇓TMS 𝓈 ⟧
          ≡⟨ ⟦⟧⟦⟧ t σ (⇓TMS 𝓈) ⟩
        t ⟦ σ ⊚ ⇓TMS 𝓈 ⟧
          ≡⟨ ap (t ⟦_⟧) (⇓TMSよOb σ 𝓈 ⁻¹) ⟩
        N-ob (TMよ t P.⟦ TMSよ σ ⟧) Γ 𝓈
          ∎) i

  TMよ⟦⟧ : {Γ Δ : ctx} {A : ty} (t : tm Δ A) (σ : tms Γ Δ) →
    TMよ (t ⟦ σ ⟧) ≡ TMよ t P.⟦ TMSよ σ ⟧
  TMよ⟦⟧ t σ = makeNatTransPath (TMよ⟦⟧lem t σ)

  open Normal 𝒞 base public

  NE : ty → ob 𝑃𝑆ℎ
  F-ob (NE A) Γ = Ne Γ A , isSetNeutral
  F-hom (NE A) σ M = M [ σ ]NE
  F-id (NE A) i M = [id]NE M i
  F-seq (NE A) σ τ i M = [][]NE M σ τ (~ i)

  NF : ty → ob 𝑃𝑆ℎ
  F-ob (NF A) Γ = Nf Γ A , isSetNormal
  F-hom (NF A) σ N = N [ σ ]NF
  F-id (NF A) i N = [id]NF N i
  F-seq (NF A) σ τ i N = [][]NF N σ τ (~ i)

  NES = plurifyPSh NE
  NFS = plurifyPSh NF

  ιNE : (A : ty) → 𝑃𝑆ℎ [ NE A , TM A ]
  N-ob (ιNE A) Γ M = ιNe M
  N-hom (ιNE A) σ i M = ιNeLem M σ i

  ιNF : (A : ty) → 𝑃𝑆ℎ [ NF A , TM A ]
  N-ob (ιNF A) Γ N = ιNf N
  N-hom (ιNF A) σ i N = ιNfLem N σ i

  ιNES = weaveHomPSh ιNE
  ιNFS = weaveHomPSh ιNF

  Nes = 𝑇𝑚𝑠 Ne

  ⇓NES : {Γ Δ : ctx} → fst (F-ob (⇓PShCtx (NES Δ)) Γ) → Nes Γ Δ
  ⇓NES {Γ} {∅} 𝓈 = !
  ⇓NES {Γ} {Δ ⊹ A} (𝓈 , M) = ⇓NES 𝓈 ⊕ M

  ⇑NES : {Γ Δ : ctx} → Nes Γ Δ → fst (F-ob (⇓PShCtx (NES Δ)) Γ)
  ⇑NES ! = lift tt
  ⇑NES (MS ⊕ M) = ⇑NES MS , M

  idNeu' : (Γ : ctx) → Nes Γ Γ
  idNeu' Γ = map𝑇𝑚𝑠 VN (id𝑅𝑒𝑛 Γ)

  idNeu : (Γ : ctx) → fst (F-ob (⇓PShCtx (NES Γ)) Γ)
  idNeu Γ = ⇑NES (idNeu' Γ)

  ιNFSlem : {Γ Δ : ctx} (σ : Nes Γ Δ) →
    ⇓TMS (N-ob (⇓PShTms (ιNES Δ)) Γ (⇑NES σ)) ≡ map𝑇𝑚𝑠 ιNe σ
  ιNFSlem ! = refl
  ιNFSlem {Γ} {Δ ⊹ A} (σ ⊕ M) =
    ⇓TMS (N-ob (⇓PShTms (ιNES (Δ ⊹ A))) Γ (⇑NES (σ ⊕ M)))
      ≡⟨ (λ i → ⇓TMS (N-ob (×PShInd (ιNES Δ) (ιNE A) i) Γ (⇑NES (σ ⊕ M)))) ⟩
    ⇓TMS (N-ob (⇓PShTms (ιNES Δ)) Γ (⇑NES σ)) ⊕ ιNe M
      ≡⟨ (λ i → ιNFSlem σ i ⊕ ιNe M) ⟩
    map𝑇𝑚𝑠 ιNe (σ ⊕ M)
      ∎

  ιNFSid : (Γ : ctx) → ⇓TMS (N-ob (⇓PShTms (ιNES Γ)) Γ (idNeu Γ)) ≡ 𝒾𝒹 Γ
  ιNFSid Γ =
    ⇓TMS (N-ob (⇓PShTms (ιNES Γ)) Γ (idNeu Γ))
      ≡⟨ ιNFSlem (idNeu' Γ) ⟩
    map𝑇𝑚𝑠 ιNe (map𝑇𝑚𝑠 VN (id𝑅𝑒𝑛 Γ))
      ≡⟨ map𝑇𝑚𝑠comp ιNe VN (id𝑅𝑒𝑛 Γ) ⟩
    makeRen (id𝑅𝑒𝑛 Γ)
      ≡⟨ 𝒾𝒹η₂ ⟩
    𝒾𝒹 Γ
      ∎
