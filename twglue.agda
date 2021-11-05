{-# OPTIONS --cubical #-}

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
  open Contextual (𝒫𝒮𝒽 REN)

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
      Gl-comp : (ιNF Gl-A) 𝒩∘ Gl-q 𝒩∘ Gl-u ≡ (ιNE Gl-A)

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
      
  private
    data ExtVar : Glueings → Glueing → Type (lsuc lzero) where
      𝑍V : {Γ : Glueings} {A : Glueing} → ExtVar (Γ ⊹ A) A
      𝑆V : {Γ : Glueings} {A B : Glueing} → ExtVar Γ A → ExtVar (Γ ⊹ B) A

    TmVar : {Γ : Glueings} {A : Glueing} → ExtVar Γ A → C.IntVar (Gls-Γ Γ) (Gl-A A)
    TmVar 𝑍V = C.𝑧V
    TmVar (𝑆V v) = C.𝑠V (TmVar v)

    PShVar : {Γ : Glueings} {A : Glueing} → ExtVar Γ A → IntVar (Gls-⦇Γ⦈ Γ) (Gl-⦇A⦈ A)
    PShVar 𝑍V = 𝑧V
    PShVar (𝑆V v) = 𝑠V (PShVar v)

    Var-nat-ob : {Γ : Glueings} {A : Glueing} (v : ExtVar Γ A) →
      N-ob ((ιNF (Gl-A A) 𝒩∘ Gl-q A) 𝒩∘ (makeVar (PShVar v)))
      ≡ N-ob (TMよ (C.makeVar (TmVar v)) ⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧)
    Var-nat-ob {Γ ⊹ B} {A} 𝑍V i Δ (MS , M) =
      Zv[]
        (⇓TMS {Δ = Gls-Γ Γ} (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ π ⊚ Gls-q (Γ ⊹ B))) Δ (MS , M)))
        (ιNf (N-ob (Gl-q A) Δ M)) (~ i)
    Var-nat-ob {Γ ⊹ B} {A} (𝑆V v) i Δ (MS , M) =
      (N-ob ((ιNF (Gl-A A) 𝒩∘ Gl-q A) 𝒩∘ makeVar (𝑠V (PShVar v))) Δ (MS , M)
        ≡⟨ (λ i → N-ob ((ιNF (Gl-A A) 𝒩∘ Gl-q A) 𝒩∘
          make𝑠V {B = Gl-⦇A⦈ B} (PShVar v) i) Δ (MS , M)) ⟩
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
        ≡⟨ (λ i → C.deriveMap (W₁Tm (Gl-A B)) (idTms (mapRL Gl-A Γ)) (TmVar v) (~ i)
          [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ
                     (N-ob (⇓πPSh {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ B} (~ i)) Δ (MS , M)))
            ⊕ ιNf (Gl-q B .N-ob Δ M) ]) ⟩
      C.derive (W₁Tms (Gl-A B) (idTms (mapRL Gl-A Γ))) (TmVar v)
        [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ
                     (N-ob (⇓PShMor (π {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ B})) Δ (MS , M)))
          ⊕ ιNf (Gl-q B .N-ob Δ M) ]
        ≡⟨ (λ i → C.derive (Vlem2 {A = Gl-A B} (idRen (mapRL Gl-A Γ)) (~ i)) (TmVar v)
          [ ⇓TMS (N-ob (⇓∘PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)
            (π {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ B}) (~ i)) Δ (MS , M)) ⊕ ιNf (Gl-q B .N-ob Δ M) ] ) ⟩
      C.derive (varify (W₁Ren (Gl-A B) (idRen (mapRL Gl-A Γ)))) (TmVar v)
        [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⊚ π)) Δ (MS , M))
          ⊕ ιNf (Gl-q B .N-ob Δ M) ]
        ≡⟨ (λ i →
          N-ob (TMよ (C.makeVar (C.𝑠V (TmVar v)))
            ⟦ ×tmLem2 (ιNFS (Gls-Γ Γ)) (ιNF (Gl-A B)) (Gls-q Γ) (Gl-q B) (~ i) ⟧) Δ (MS , M)) ⟩
      N-ob (TMよ (C.makeVar (C.𝑠V (TmVar v))) ⟦ ιNFS (Gls-Γ (Γ ⊹ B)) ⊚ Gls-q (Γ ⊹ B) ⟧)
        Δ (MS , M)
        ∎) i

  makeTwGlVar : {Γ : Glueings} {A : Glueing} → ExtVar Γ A → GlTm Γ A
  GlTm-⦇α⦈ (makeTwGlVar v) = makeVar (PShVar v)
  GlTm-α (makeTwGlVar v) = C.makeVar (TmVar v)
  GlTm-nat (makeTwGlVar v) = makeNatTransPath (Var-nat-ob v)
