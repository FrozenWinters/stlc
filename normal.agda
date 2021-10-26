{-# OPTIONS --cubical --allow-unsolved-metas #-}

module normal where

open import ren2
open import syn3
open import psh

open import Cubical.Data.Nat renaming (zero to Z; suc to S)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

data Nf : (Γ : Ctx) (A : Ty) → Set

data Ne : (Γ : Ctx) (A : Ty) → Set where
  VN : {Γ : Ctx} {A : Ty} → Var Γ A → Ne Γ A
  APP : {Γ : Ctx} {A B : Ty} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

data Nf where
  NEU : {Γ : Ctx} {c : Char} → Ne Γ (Base c) → Nf Γ (Base c)
  LAM : {Γ : Ctx} {A B : Ty} → Nf (Γ ⊹ A) B → Nf Γ (A ⇒ B)

insertCtx : (Γ : Ctx) (A : Ty) (n : ℕ) → Ctx
insertCtx Γ A Z = Γ ⊹ A
insertCtx ∅ A (S n) = ∅ ⊹ A
insertCtx (Γ ⊹ B) A (S n) = insertCtx Γ A n ⊹ B

SVar : {Γ : Ctx} {A B : Ty} (n : ℕ) → Var Γ A → Var (insertCtx Γ B n) A
SNe : {Γ : Ctx} {A B : Ty} (n : ℕ) → Ne Γ A → Ne (insertCtx Γ B n) A
SNf : {Γ : Ctx} {A B : Ty} (n : ℕ) → Nf Γ A → Nf (insertCtx Γ B n) A

SVar Z v = Sv v
SVar (S n) Zv = Zv
SVar (S n) (Sv v) = Sv (SVar n v)

SNe n (VN v) = VN (SVar n v)
SNe n (APP M N) = APP (SNe n M) (SNf n N)

SNf n (NEU M) = NEU (SNe n M)
SNf n (LAM N) = LAM (SNf (S n) N)

infix 30 _[_]NE _[_]NF
_[_]NE : {Γ Δ : Ctx} {A : Ty} → Ne Δ A → Ren Γ Δ → Ne Γ A
_[_]NF : {Γ Δ : Ctx} {A : Ty} → Nf Δ A → Ren Γ Δ → Nf Γ A

APP M N [ σ ]NE = APP (M [ σ ]NE) (N [ σ ]NF)
VN v [ σ ]NE = VN (v [ σ ]R)

NEU M [ σ ]NF = NEU (M [ σ ]NE)
LAM {A = A} N [ σ ]NF = LAM (N [ W₂Ren A σ ]NF)

[id]NE : {Γ : Ctx} {A : Ty} → (M : Ne Γ A) →
  M [ idRen Γ ]NE ≡ M
[id]NF : {Γ : Ctx} {A : Ty} → (N : Nf Γ A) →
  N [ idRen Γ ]NF ≡ N

[id]NE (VN Zv) = refl
[id]NE (VN (Sv v)) =
  VN (v [ W₁Ren _ (idRen _) ]R)
    ≡⟨ ap VN (Wlem2Ren v (idRen _)) ⟩
  VN (Sv (v [ idRen _ ]R))
    ≡⟨ ap VN (ap Sv ([id]Ren v)) ⟩
  VN (Sv v)
    ∎
[id]NE (APP M N) i = APP ([id]NE M i) ([id]NF N i)

[id]NF (NEU M) = ap NEU ([id]NE M)
[id]NF (LAM N) = ap LAM ([id]NF N)

[][]NE : {Γ Δ Σ : Ctx} {A : Ty} (M : Ne Σ A) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  M [ σ ]NE [ τ ]NE ≡ M [ σ ∘Ren τ ]NE
[][]NF : {Γ Δ Σ : Ctx} {A : Ty} (N : Nf Σ A) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  N [ σ ]NF [ τ ]NF ≡ N [ σ ∘Ren τ ]NF

[][]NE (VN v) σ τ = ap VN ([][]Ren v σ τ)
[][]NE (APP M N) σ τ i = APP ([][]NE M σ τ i) ([][]NF N σ τ i)

[][]NF (NEU M) σ τ = ap NEU ([][]NE M σ τ)
[][]NF (LAM N) σ τ =
  LAM (N [ W₂Ren _ σ ]NF [ W₂Ren _ τ ]NF)
    ≡⟨ ap LAM ([][]NF N (W₂Ren _ σ) (W₂Ren _ τ) ) ⟩
  LAM (N [ W₂Ren _ σ ∘Ren W₂Ren _ τ ]NF)
    ≡⟨ (λ i → LAM (N [ Wlem4Ren σ τ i ]NF)) ⟩
  LAM (N [ W₂Ren _ (σ ∘Ren τ) ]NF)
    ∎

isSetNeutral : {Γ : Ctx} {A : Ty} → isSet (Ne Γ A)
isSetNeutral = {!!}

isSetNormal : {Γ : Ctx} {A : Ty} → isSet (Nf Γ A)
isSetNormal = {!!}

module _ where
  open Functor
  open Precategory

  NE : Ty → ob (PSh REN)
  F-ob (NE A) Δ = Ne Δ A , isSetNeutral
  F-hom (NE A) σ M = M [ σ ]NE
  F-id (NE A) i M = [id]NE M i
  F-seq (NE A) σ τ i M = [][]NE M σ τ (~ i)

  NF : Ty → ob (PSh REN)
  F-ob (NF A) Δ = Nf Δ A , isSetNormal
  F-hom (NF A) σ N = N [ σ ]NF
  F-id (NF A) i N = [id]NF N i
  F-seq (NF A) σ τ i N = [][]NF N σ τ (~ i)
