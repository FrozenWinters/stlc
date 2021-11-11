{-# OPTIONS --cubical --allow-unsolved-metas #-}

module twglue where

open import psh
open import ren2
open import syn3
--open import eliminator3
open import normal

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Categories.Instances.Sets

module _ where
  open Precategory (PSh REN) hiding (_∘_)
  open Contextual (𝒫𝒮𝒽 REN  ⦃ isCatRen ⦄ ⦃ PShCat ⦄)

  private
    infixr 20 _𝒩∘_
    _𝒩∘_ = comp' (PSh REN)

    module C = Contextual σιν

  record Glueing : Type (lsuc lzero) where
    constructor Gl
    field
      Gl-A : Ty
      Gl-⦇A⦈ : ob
      Gl-u : Hom[ NE Gl-A , Gl-⦇A⦈ ]
      Gl-q : Hom[ Gl-⦇A⦈ , NF Gl-A ]
      Gl-comp : ιNF Gl-A 𝒩∘ Gl-q 𝒩∘ Gl-u ≡ ιNE Gl-A

  Glueings = RL Glueing

  open Glueing
  open PShFam

  Gls-Γ : Glueings → Ctx
  Gls-Γ = mapRL Gl-A

  Gls-⦇Γ⦈ : Glueings → ctx
  Gls-⦇Γ⦈ = mapRL Gl-⦇A⦈

  Gls-u : (Γ : Glueings) → tms (plurify NE (Gls-Γ Γ)) (Gls-⦇Γ⦈ Γ)
  Gls-u ∅ = !
  Gls-u (Γ ⊹ A) = Gls-u Γ ×tm (Gl-u A)

  Gls-q : (Γ : Glueings) → tms (Gls-⦇Γ⦈ Γ) (plurify NF (Gls-Γ Γ))
  Gls-q ∅ = !
  Gls-q (Γ ⊹ A) = Gls-q Γ ×tm (Gl-q A)

  record GlTm (Γ : Glueings) (A : Glueing) : Type (lsuc lzero) where
    field
      GlTm-⦇α⦈ : tm (Gls-⦇Γ⦈ Γ) (Gl-⦇A⦈ A)
      GlTm-α : Tm (Gls-Γ Γ) (Gl-A A)
      GlTm-nat : (ιNF (Gl-A A) 𝒩∘ Gl-q A) 𝒩∘ GlTm-⦇α⦈
                ≡ TMよ GlTm-α ⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧

  GlTms = IL GlTm

  open GlTm
  open NatTrans

  GlTms-⦇αs⦈ : {Γ Δ : Glueings} (σ : GlTms Γ Δ) → tms (Gls-⦇Γ⦈ Γ) (Gls-⦇Γ⦈ Δ)
  GlTms-⦇αs⦈ = mapIL₁ GlTm-⦇α⦈

  GlTms-αs : {Γ Δ : Glueings} (σ : GlTms Γ Δ) → Tms (Gls-Γ Γ) (Gls-Γ Δ)
  GlTms-αs = mapIL₁ GlTm-α

  GlTms-nat : {Γ Δ : Glueings} (σ : GlTms Γ Δ) →
    ιNFS (Gls-Γ Δ) ⊚ Gls-q Δ ⊚ GlTms-⦇αs⦈ σ
    ≡ TMSよ (GlTms-αs σ) ⊚ (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)
  GlTms-nat ! = refl
  GlTms-nat {Γ} {Δ ⊹ A} (σ ⊕ t) =
    ιNFS (Gls-Γ (Δ ⊹ A)) ⊚ Gls-q (Δ ⊹ A) ⊚ GlTms-⦇αs⦈ (σ ⊕ t)
      ≡⟨ (λ i → (×tmLem2 (ιNFS (Gls-Γ Δ)) (ιNF (Gl-A A)) (Gls-q Δ) (Gl-q A) i)
        ⊚ GlTms-⦇αs⦈ (σ ⊕ t)) ⟩
    (ιNFS (Gls-Γ Δ) ⊚ Gls-q Δ) ×tm (ιNF (Gl-A A) 𝒩∘ Gl-q A) ⊚ GlTms-⦇αs⦈ (σ ⊕ t)
      ≡⟨ ×tmLem1 (ιNFS (Gls-Γ Δ) ⊚ Gls-q Δ) (ιNF (Gl-A A) 𝒩∘ Gl-q A)
        (GlTms-⦇αs⦈ σ) (GlTm-⦇α⦈ t) ⟩
    (ιNFS (Gls-Γ Δ) ⊚ Gls-q Δ ⊚ GlTms-⦇αs⦈ σ) ⊕ ((ιNF (Gl-A A) 𝒩∘ Gl-q A) 𝒩∘ GlTm-⦇α⦈ t)
      ≡⟨ (λ i → GlTms-nat σ i ⊕ GlTm-nat t i) ⟩
    TMSよ (GlTms-αs (σ ⊕ t)) ⊚ (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)
      ∎

  _[_]Gl : {Γ Δ : Glueings} {A : Glueing} (t : GlTm Δ A) (σ : GlTms Γ Δ) → GlTm Γ A
  GlTm-⦇α⦈ (t [ σ ]Gl) = GlTm-⦇α⦈ t ⟦ GlTms-⦇αs⦈ σ ⟧
  GlTm-α (t [ σ ]Gl) = GlTm-α t [ GlTms-αs σ ]
  GlTm-nat (_[_]Gl {Γ} {Δ} {A} t σ) =
    (ιNF (Gl-A A) 𝒩∘ Gl-q A) 𝒩∘ GlTm-⦇α⦈ (t [ σ ]Gl)
      ≡⟨ ⋆Assoc (⇓PShMor (GlTms-⦇αs⦈ σ)) (GlTm-⦇α⦈ t) (ιNF (Gl-A A) 𝒩∘ Gl-q A) ⟩
    ((ιNF (Gl-A A) 𝒩∘ Gl-q A) 𝒩∘ GlTm-⦇α⦈ t) ⟦ GlTms-⦇αs⦈ σ ⟧
      ≡⟨ ap _⟦ GlTms-⦇αs⦈ σ ⟧ (GlTm-nat t) ⟩
    TMよ (GlTm-α t) ⟦ ιNFS (Gls-Γ Δ) ⊚ Gls-q Δ ⟧ ⟦ GlTms-⦇αs⦈ σ ⟧
      ≡⟨ ⟦⟧⟦⟧ (TMよ (GlTm-α t)) (ιNFS (Gls-Γ Δ) ⊚ Gls-q Δ) (GlTms-⦇αs⦈ σ) ⟩
    TMよ (GlTm-α t) ⟦ ιNFS (Gls-Γ Δ) ⊚ Gls-q Δ ⊚ GlTms-⦇αs⦈ σ ⟧
      ≡⟨ ap (TMよ (GlTm-α t) ⟦_⟧) (GlTms-nat σ) ⟩
    TMよ (GlTm-α t) ⟦ TMSよ (GlTms-αs σ) ⊚ (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ) ⟧
      ≡⟨ ⟦⟧⟦⟧ (TMよ (GlTm-α t)) (TMSよ (GlTms-αs σ)) (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ) ⁻¹ ⟩
    TMよ (GlTm-α t) ⟦ TMSよ (GlTms-αs σ) ⟧ ⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧
      ≡⟨ ap _⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧ (TMよ⟦⟧ (GlTm-α t) (GlTms-αs σ) ⁻¹) ⟩
    TMよ (GlTm-α t [ GlTms-αs σ ]) ⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧
      ∎

  _∘GlTms_ : {Γ Δ Σ : Glueings} → GlTms Δ Σ → GlTms Γ Δ → GlTms Γ Σ
  σ ∘GlTms τ = mapIL _[ τ ]Gl σ

  Gl-⦇αs⦈∘ : {Γ Δ Σ : Glueings} (σ : GlTms Δ Σ) (τ : GlTms Γ Δ) →
    GlTms-⦇αs⦈ (σ ∘GlTms τ) ≡ GlTms-⦇αs⦈ σ ⊚ GlTms-⦇αs⦈ τ
  Gl-⦇αs⦈∘ ! τ = refl
  Gl-⦇αs⦈∘ (σ ⊕ t) τ i = Gl-⦇αs⦈∘ σ τ i ⊕ GlTm-⦇α⦈ t ⟦ GlTms-⦇αs⦈ τ ⟧

  Gl-αs∘ : {Γ Δ Σ : Glueings} (σ : GlTms Δ Σ) (τ : GlTms Γ Δ) →
    GlTms-αs (σ ∘GlTms τ) ≡ GlTms-αs σ ∘Tms GlTms-αs τ
  Gl-αs∘ ! τ = refl
  Gl-αs∘ (σ ⊕ t) τ i = Gl-αs∘ σ τ i ⊕ GlTm-α t [ GlTms-αs τ ]

  open Functor

  indLem : (Γ : Glueings) (A B : Glueing) (t : Tm (Gls-Γ (Γ ⊹ A)) (Gl-A B)) {Δ : Ctx}
    (MS : fst (F-ob (⇓PSh (Gls-⦇Γ⦈ Γ)) Δ)) (M : fst (F-ob (Gl-⦇A⦈ A) Δ)) →
    N-ob ((TMよ t) ⟦ ιNFS (Gls-Γ (Γ ⊹ A)) ⊚ Gls-q (Γ ⊹ A) ⟧) Δ (MS , M)
    ≡ t [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ MS) ⊕ ιNf (N-ob (Gl-q A) Δ M) ]
  indLem Γ A B t {Δ} MS M =
    N-ob (TMよ t ⟦ ιNFS (Gls-Γ (Γ ⊹ A)) ⊚ Gls-q Γ ×tm Gl-q A ⟧) Δ (MS , M)
      ≡⟨ (λ i → N-ob (TMよ t
        ⟦ ×tmLem2 (ιNFS (Gls-Γ Γ)) (ιNF (Gl-A A)) (Gls-q Γ) (Gl-q A) i ⟧) Δ (MS , M)) ⟩
    t [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⊚ π)) Δ (MS , M))
      ⊕ ιNf (N-ob (Gl-q A) Δ M) ]
      ≡⟨ (λ i → t [ ⇓TMS (N-ob (⇓∘PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)
        (π {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A}) i) Δ (MS , M)) ⊕ ιNf (N-ob (Gl-q A) Δ M) ]) ⟩
    t [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ
      (N-ob (⇓PShMor (π {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A})) Δ (MS , M))) ⊕ ιNf (N-ob (Gl-q A) Δ M) ]
      ≡⟨ (λ i → t [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ
        (N-ob (⇓πPSh {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A} i) Δ (MS , M))) ⊕ ιNf (N-ob (Gl-q A) Δ M) ]) ⟩
    t [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ MS) ⊕ ιNf (N-ob (Gl-q A) Δ M) ]
      ∎
      
  private
    ExtVar = 𝑉𝑎𝑟 Glueing
    ExtRen = 𝑅𝑒𝑛 Glueing
    TmVar = tr𝑉𝑎𝑟 Gl-A
    TmRen = tr𝑅𝑒𝑛 Gl-A
    PShVar = tr𝑉𝑎𝑟 Gl-⦇A⦈
    PShRen = tr𝑅𝑒𝑛 Gl-⦇A⦈

    Var-nat-ob : {Γ : Glueings} {A : Glueing} (v : ExtVar Γ A) →
      N-ob ((ιNF (Gl-A A) 𝒩∘ Gl-q A) 𝒩∘ (makeVar (PShVar v)))
      ≡ N-ob (TMよ (C.makeVar (TmVar v)) ⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧)
    Var-nat-ob {Γ ⊹ B} {A} 𝑧𝑣 i Δ (MS , M) =
      Zv[]
        (⇓TMS {Δ = Gls-Γ Γ} (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ π ⊚ Gls-q (Γ ⊹ B))) Δ (MS , M)))
        (ιNf (N-ob (Gl-q A) Δ M)) (~ i)
    Var-nat-ob {Γ ⊹ B} {A} (𝑠𝑣 v) i Δ (MS , M) =
      (N-ob ((ιNF (Gl-A A) 𝒩∘ Gl-q A) 𝒩∘ makeVar (𝑠𝑣 (PShVar v))) Δ (MS , M)
        ≡⟨ (λ i → N-ob ((ιNF (Gl-A A) 𝒩∘ Gl-q A) 𝒩∘
          make𝑠𝑣 {B = Gl-⦇A⦈ B} (PShVar v) i) Δ (MS , M)) ⟩
      ιNf (N-ob (Gl-q A) Δ (N-ob (makeVar (PShVar v)) Δ
        (N-ob (⇓PShMor (π {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ B})) Δ (MS , M))))
        ≡⟨ (λ i → ιNf (N-ob (Gl-q A) Δ
          (N-ob (makeVar (PShVar v)) Δ (N-ob (⇓πPSh {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ B} i) Δ (MS , M))))) ⟩
      ιNf (N-ob (Gl-q A) Δ (N-ob (makeVar (PShVar v)) Δ MS))
        ≡⟨ (λ i → Var-nat-ob v i Δ MS) ⟩
      C.makeVar (TmVar v) [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ MS) ]
        ≡⟨ Wlem0 (C.makeVar (TmVar v))
           (⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ MS)) (ιNf (Gl-q B .N-ob Δ M)) ⁻¹ ⟩
      W₁Tm (Gl-A B) (C.makeVar (TmVar v))
        [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ MS)
          ⊕ ιNf (Gl-q B .N-ob Δ M) ]
        ≡⟨ (λ i → lem (~ i)  [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ MS)
          ⊕ ιNf (Gl-q B .N-ob Δ M) ]) ⟩
      C.makeVar (𝑠𝑣 (TmVar v))
        [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ MS) ⊕ ιNf (Gl-q B .N-ob Δ M) ]
        ≡⟨ indLem Γ B A (C.makeVar (𝑠𝑣 (TmVar v))) MS M ⁻¹ ⟩
      N-ob (TMよ (C.makeVar (𝑠𝑣 (TmVar v))) ⟦ ιNFS (Gls-Γ (Γ ⊹ B)) ⊚ Gls-q (Γ ⊹ B) ⟧) Δ (MS , M)
        ∎) i where
        lem : C.makeVar (𝑠𝑣 (TmVar v)) ≡ W₁Tm (Gl-A B) (C.makeVar (TmVar v))
        lem =
          C.derive (varify (W₁Ren (Gl-A B) (idRen (Gls-Γ Γ)))) (TmVar v)
            ≡⟨ (λ i → C.derive (Vlem2 {A = Gl-A B} (idRen (Gls-Γ Γ)) i) (TmVar v)) ⟩
          C.derive (W₁Tms (Gl-A B) (idTms (Gls-Γ Γ))) (TmVar v)
            ≡⟨ C.deriveMap (W₁Tm (Gl-A B)) (idTms (Gls-Γ Γ)) (TmVar v) ⟩
          W₁Tm (Gl-A B) (C.makeVar (TmVar v))
            ∎

  makeTwGlVar : {Γ : Glueings} {A : Glueing} → ExtVar Γ A → GlTm Γ A
  GlTm-⦇α⦈ (makeTwGlVar v) = makeVar (PShVar v)
  GlTm-α (makeTwGlVar v) = C.makeVar (TmVar v)
  GlTm-nat (makeTwGlVar v) = makeNatTransPath (Var-nat-ob v)

  makeTwGlRen : {Γ Δ : Glueings} → ExtRen Γ Δ → GlTms Γ Δ
  makeTwGlRen = mapIL makeTwGlVar

  idTwGl : (Γ : Glueings) → GlTms Γ Γ
  idTwGl Γ = makeTwGlRen (id𝑅𝑒𝑛 Γ)

  idTwGl-⦇αs⦈ : {Γ : Glueings} → GlTms-⦇αs⦈ (idTwGl Γ) ≡ 𝒾𝒹 (Gls-⦇Γ⦈ Γ)
  idTwGl-⦇αs⦈ {Γ} =
    mapIL₁ GlTm-⦇α⦈ (mapIL makeTwGlVar (id𝑅𝑒𝑛 Γ))
      ≡⟨ mapILcomp₁ GlTm-⦇α⦈ makeTwGlVar (id𝑅𝑒𝑛 Γ) ⟩
    mapIL₁ (makeVar ∘ PShVar) (id𝑅𝑒𝑛 Γ)
      ≡⟨ mapILcomp₂ makeVar PShVar (id𝑅𝑒𝑛 Γ) ⁻¹ ⟩
    makeRen (PShRen (id𝑅𝑒𝑛 Γ))
      ≡⟨ ap makeRen (trId Gl-⦇A⦈ Γ) ⟩
    makeRen (id𝑅𝑒𝑛 (Gls-⦇Γ⦈ Γ))
      ≡⟨ 𝒾𝒹η₂ ⟩
    𝒾𝒹 (Gls-⦇Γ⦈ Γ)
      ∎

  idTwGl-αs : {Γ : Glueings} → GlTms-αs (idTwGl Γ) ≡ idTms (Gls-Γ Γ)
  idTwGl-αs {Γ} =
    mapIL₁ GlTm-α (mapIL makeTwGlVar (id𝑅𝑒𝑛 Γ))
      ≡⟨ mapILcomp₁ GlTm-α makeTwGlVar (id𝑅𝑒𝑛 Γ) ⟩
    mapIL₁ (C.makeVar ∘ TmVar) (id𝑅𝑒𝑛 Γ)
      ≡⟨ mapILcomp₂ C.makeVar TmVar (id𝑅𝑒𝑛 Γ) ⁻¹ ⟩
    C.makeRen (TmRen (id𝑅𝑒𝑛 Γ))
      ≡⟨ ap C.makeRen (trId Gl-A Γ) ⟩
    C.makeRen (id𝑅𝑒𝑛 (Gls-Γ Γ))
      ≡⟨ C.𝒾𝒹η₂ ⟩
    idTms (Gls-Γ Γ)
      ∎

  idTwGl[] : {Γ : Glueings} {A : Glueing} (t : GlTm Γ A) → t [ idTwGl Γ ]Gl ≡ t
  GlTm-⦇α⦈ (idTwGl[] {Γ} t i) =
    (GlTm-⦇α⦈ t ⟦ GlTms-⦇αs⦈ (idTwGl Γ) ⟧
      ≡⟨ ap (GlTm-⦇α⦈ t ⟦_⟧) (idTwGl-⦇αs⦈ {Γ}) ⟩
    GlTm-⦇α⦈ t ⟦ 𝒾𝒹 (Gls-⦇Γ⦈ Γ) ⟧
      ≡⟨ 𝒾𝒹⟦⟧ {Gls-⦇Γ⦈ Γ} (GlTm-⦇α⦈ t) ⟩
    GlTm-⦇α⦈ t
      ∎) i
  GlTm-α (idTwGl[] {Γ} t i) =
    (GlTm-α t [ GlTms-αs (idTwGl Γ) ]
      ≡⟨ ap (GlTm-α t [_]) (idTwGl-αs {Γ}) ⟩
    GlTm-α t [ idTms (Gls-Γ Γ) ]
      ≡⟨ C.𝒾𝒹⟦⟧ (GlTm-α t) ⟩
    GlTm-α t
      ∎) i
  GlTm-nat (idTwGl[] {Γ} {A} t i) j =
    isSet→SquareP (λ i j → isSetNat)
      (GlTm-nat (t [ idTwGl Γ ]Gl))
      (GlTm-nat t)
      (λ k → (ιNF (Gl-A A) 𝒩∘ Gl-q A) 𝒩∘ GlTm-⦇α⦈ (idTwGl[] t k))
      (λ k → TMよ (GlTm-α (idTwGl[] t k)) ⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧) i j

  𝑧𝑣TwGlLem : {Γ Δ : Glueings} {A : Glueing} (τ : GlTms Γ Δ) (t : GlTm Γ A) →
    makeTwGlVar 𝑧𝑣 [ τ ⊕ t ]Gl ≡ t
  GlTm-⦇α⦈ (𝑧𝑣TwGlLem τ t i) = 𝑧β (GlTms-⦇αs⦈ (τ ⊕ t)) i
  GlTm-α (𝑧𝑣TwGlLem τ t i) = C.𝑧β (GlTms-αs (τ ⊕ t)) i
  GlTm-nat (𝑧𝑣TwGlLem {Γ} {Δ} {A} τ t i) j =
    isSet→SquareP (λ i j → isSetNat)
      (GlTm-nat (makeTwGlVar 𝑧𝑣 [ τ ⊕ t ]Gl))
      (GlTm-nat t)
      (λ k → (ιNF (Gl-A A) 𝒩∘ Gl-q A) 𝒩∘ GlTm-⦇α⦈ (𝑧𝑣TwGlLem τ t k))
      (λ k → TMよ (GlTm-α (𝑧𝑣TwGlLem τ t k)) ⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧) i j

  𝑠𝑣TwGlLem : {Γ Δ : Glueings} {A B : Glueing} (v : ExtVar Δ B) (τ : GlTms Γ Δ)
    (t : GlTm Γ A) → makeTwGlVar (𝑠𝑣 v) [ τ ⊕ t ]Gl ≡ makeTwGlVar v [ τ ]Gl
  GlTm-⦇α⦈ (𝑠𝑣TwGlLem v τ t i) = W₁⟦⟧ (PShVar v) (GlTms-⦇αs⦈ τ) (GlTm-⦇α⦈ t) i
  GlTm-α (𝑠𝑣TwGlLem v τ t i) = C.W₁⟦⟧ (TmVar v) (GlTms-αs τ) (GlTm-α t) i
  GlTm-nat (𝑠𝑣TwGlLem {Γ} {Δ} {A} {B} v τ t i) j =
    isSet→SquareP (λ i j → isSetNat)
      (GlTm-nat (makeTwGlVar (𝑠𝑣 v) [ τ ⊕ t ]Gl))
      (GlTm-nat (makeTwGlVar v [ τ ]Gl))
      (λ k → (ιNF (Gl-A B) 𝒩∘ Gl-q B) 𝒩∘ GlTm-⦇α⦈ (𝑠𝑣TwGlLem v τ t k))
      (λ k → TMよ (GlTm-α (𝑠𝑣TwGlLem v τ t k)) ⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧) i j

  𝑠𝑣TwGlRenLem : {Γ Δ Σ : Glueings} {A : Glueing} (σ : ExtRen Δ Σ) (τ : GlTms Γ Δ)
    (t : GlTm Γ A) → makeTwGlRen (W₁𝑅𝑒𝑛 σ) ∘GlTms (τ ⊕ t) ≡ makeTwGlRen σ ∘GlTms τ
  𝑠𝑣TwGlRenLem ! τ t = refl
  𝑠𝑣TwGlRenLem (σ ⊕ v) τ t i = 𝑠𝑣TwGlRenLem σ τ t i ⊕ 𝑠𝑣TwGlLem v τ t i

  idTwGlL : {Γ Δ : Glueings} (σ : GlTms Γ Δ) → idTwGl Δ ∘GlTms σ ≡ σ
  idTwGlL ! = refl
  idTwGlL {Γ} {Δ ⊹ A} (σ ⊕ t) i =
    ((makeTwGlRen (W₁𝑅𝑒𝑛 (id𝑅𝑒𝑛 Δ)) ∘GlTms (σ ⊕ t)) ⊕ (makeTwGlVar 𝑧𝑣 [ σ ⊕ t ]Gl)
      ≡⟨ (λ k → 𝑠𝑣TwGlRenLem (id𝑅𝑒𝑛 Δ) σ t k ⊕ 𝑧𝑣TwGlLem σ t k) ⟩
    (makeTwGlRen (id𝑅𝑒𝑛 Δ) ∘GlTms σ) ⊕ t
      ≡⟨ (λ k → idTwGlL σ k ⊕ t) ⟩
    σ ⊕ t
      ∎) i

  [][]TwGl : {Γ Δ Σ : Glueings} {A : Glueing} (t : GlTm Σ A) (σ : GlTms Δ Σ) (τ : GlTms Γ Δ) →
    t [ σ ]Gl [ τ ]Gl ≡ t [ σ ∘GlTms τ ]Gl
  GlTm-⦇α⦈ ([][]TwGl t σ τ i) =
    (GlTm-⦇α⦈ t ⟦ GlTms-⦇αs⦈ σ ⟧ ⟦ GlTms-⦇αs⦈ τ ⟧
      ≡⟨ ⟦⟧⟦⟧ (GlTm-⦇α⦈ t) (GlTms-⦇αs⦈ σ) (GlTms-⦇αs⦈ τ) ⟩
    GlTm-⦇α⦈ t ⟦ GlTms-⦇αs⦈ σ ⊚ GlTms-⦇αs⦈ τ ⟧
      ≡⟨ ap (GlTm-⦇α⦈ t ⟦_⟧) (Gl-⦇αs⦈∘ σ τ ⁻¹) ⟩
    GlTm-⦇α⦈ t ⟦ GlTms-⦇αs⦈ (σ ∘GlTms τ) ⟧
      ∎) i
  GlTm-α ([][]TwGl t σ τ i) =
    (GlTm-α t [ GlTms-αs σ ] [ GlTms-αs τ ]
      ≡⟨ [][] (GlTm-α t) (GlTms-αs σ) (GlTms-αs τ) ⟩
    GlTm-α t [ GlTms-αs σ ∘Tms GlTms-αs τ ]
      ≡⟨ ap (GlTm-α t [_]) (Gl-αs∘ σ τ ⁻¹) ⟩
    GlTm-α t [ GlTms-αs (σ ∘GlTms τ) ]
      ∎) i
  GlTm-nat ([][]TwGl {Γ} {Δ} {Σ} {A} t σ τ i) j =
    isSet→SquareP (λ i j → isSetNat)
      (GlTm-nat ((t [ σ ]Gl) [ τ ]Gl))
      (GlTm-nat (t [ σ ∘GlTms τ ]Gl))
      (λ k → (ιNF (Gl-A A) 𝒩∘ Gl-q A) 𝒩∘ GlTm-⦇α⦈ ([][]TwGl t σ τ k))
      (λ k → TMよ (GlTm-α ([][]TwGl t σ τ k)) ⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧) i j

  isSetGlTm : {Γ : Glueings} {A : Glueing} → isSet (GlTm Γ A)
  isSetGlTm = {!!}
  
  private
    module D = Contextual

  TwGl : Contextual (lsuc lzero) (lsuc lzero)
  D.ty TwGl = Glueing
  D.tm TwGl = GlTm
  D._⟦_⟧ TwGl = _[_]Gl
  D.𝒾𝒹 TwGl = idTwGl
  D.𝒾𝒹L TwGl = idTwGlL
  D.𝒾𝒹⟦⟧ TwGl = idTwGl[]
  D.⟦⟧⟦⟧ TwGl = [][]TwGl
  D.isSetTm TwGl = isSetGlTm
