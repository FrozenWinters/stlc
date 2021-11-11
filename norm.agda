{-# OPTIONS --cubical #-}

module norm where

open import ren2
open import syn3
open import normal
open import cartesian2
open import eliminator3
open import contextual
open import twglue
open import twglccc
open import psh

open import Cubical.Data.Nat renaming (zero to Z; suc to S) hiding (elim)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)

open Glueing
open GlTm

ηNe : {Γ : Ctx} {A : Ty} → Ne Γ A → Nf Γ A
ηNe {Γ} {Base X} M = NEU M
ηNe {Γ} {A ⇒ B} M = LAM (ηNe (APP (SNe Z M) (ηNe (VN Zv))))

NEULem : {Γ Δ : Ctx} {X : Char} (M : Ne Δ (Base X)) (σ : Ren Γ Δ) →
  NEU (M [ σ ]NE) ≡ NEU M [ σ ]NF
NEULem (VN v) σ = refl
NEULem (APP M N) σ = refl

open NatTrans
open Precategory (PSh REN) hiding (_∘_)
open Contextual (𝒫𝒮𝒽 REN)
open Functor

private
  infixr 20 _𝒩∘_
  _𝒩∘_ = comp' (PSh REN)

base : (X : Char) → Glueing
Gl-A (base X) = Base X
Gl-⦇A⦈ (base X) = NF (Base X)
N-ob (Gl-u (base X)) Γ M = NEU M
N-hom (Gl-u (base X)) σ i M = NEULem M σ i
Gl-q (base X) = idTrans (NF (Base X))
N-ob (Gl-comp (base X) i) Γ M = ιNe M
N-hom (Gl-comp (base X) i) {Γ} {Δ} σ j M =
  isSet→SquareP (λ i j → snd (F-ob (TM (Base X)) Δ))
    (λ k → N-hom (ιNF (Gl-A (base X)) 𝒩∘ (Gl-q (base X) 𝒩∘ Gl-u (base X))) σ k M)
    (ιNeLem M σ)
    (λ k → ιNe (M [ σ ]NE))
    (λ k → ιNe M [ varify σ ]) i j

open Eliminator TwGl ⦃ isCCCTwGl ⦄ base

open ContextualFunctor
open PShFam

interpTyLem : (A : Ty) → Gl-A (interpTy A) ≡ A
interpTyLem (Base X) = refl
interpTyLem (A ⇒ B) i = interpTyLem A i ren2.⇒ interpTyLem B i

𝑧NE : {Γ : Ctx} {A : Ty} → Ne (Γ ⊹ A) (Gl-A (interpTy A))
𝑧NE {Γ} {A} = transp (λ i → Ne (Γ ⊹ A) (interpTyLem A (~ i))) i0 (VN Zv)

W₁NES : {Γ Δ : Ctx} {A : Ty} → fst (F-ob (⇓PSh (NES Γ)) Δ) → fst (F-ob (⇓PSh (NES Γ)) (Δ ⊹ A))
W₁NES {∅} MS = lift tt
W₁NES {Γ ⊹ B} {Δ} {A} (MS , M) = W₁NES {Γ} {Δ} {A} MS , SNe Z M

idNeu : (Γ : Ctx) → fst (F-ob (⇓PSh (NES (Gls-Γ (CF-ctx elim Γ)))) Γ)
idNeu ∅ = lift tt
idNeu (Γ ⊹ A) = W₁NES {Gls-Γ (interpCtx Γ)} {Γ} {A} (idNeu Γ) , 𝑧NE

norm : {Γ : Ctx} {A : Ty} → Tm Γ A → Nf Γ A
norm {Γ} {A} t =
  transp (λ i → Nf Γ (interpTyLem A i)) i0
    (N-ob (Gl-q (interpTy A) 𝒩∘ GlTm-⦇α⦈ (interpTm t) 𝒩∘ (⇓PShMor (Gls-u (interpCtx Γ)))) Γ
      (idNeu Γ))

correctness : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → t ≡ ιNf (norm t)
correctness {Γ} {A} t =
  {!ιNFS (Gls-Γ (interpCtx Γ)) ⊚ Gls-q (interpCtx Γ)!}

{-



  --ιNFS (Gls-Γ (interpCtx Γ)) ⊚ Gls-q (interpCtx Γ)
  --⇓PShMor (ιNFS (Gls-Γ (interpCtx Γ)) ⊚ Gls-q (interpCtx Γ)) --𝒩∘ ⇓PShMor (Gls-u (interpCtx Γ))
  {-ιNf (N-ob (Gl-q (interpTy A)) Γ (N-ob (GlTm-⦇α⦈ (interpTm t)) Γ
    (N-ob (⇓PShMor (Gls-u (interpCtx Γ))) Γ (idNeu Γ))))
    ≡⟨ (λ i →  N-ob (GlTm-nat (interpTm t) i) Γ
      (N-ob (⇓PShMor (Gls-u (interpCtx Γ))) Γ (idNeu Γ))) ⟩
  GlTm-α (interpTm t)
    [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ (interpCtx Γ)) ⊚ Gls-q (interpCtx Γ)) 𝒩∘ ⇓PShMor (Gls-u (interpCtx Γ))) Γ (idNeu Γ))]
    ∎-}
    -}
