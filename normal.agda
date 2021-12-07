{-# OPTIONS --cubical --allow-unsolved-metas #-}

module normal where

open import psh
open import contextual
open import ccc

open import Cubical.Data.Nat renaming (zero to Z; suc to S) hiding (elim)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private
  variable
    ℓ₁ ℓ₂ : Level

-- We define normal and neutral terms and use them to construct presheaves on REN

module Normal (𝒞 : Contextual ℓ₁ ℓ₂) ⦃ 𝒞CCC : CCC 𝒞 ⦄ (base : Char → Contextual.ty 𝒞) where
  open Contextual 𝒞
  open CCC 𝒞CCC

  private
    module R = Contextual ρεν

  data Nf : (Γ : ctx) (A : ty) → Type ℓ₁

  data Ne : (Γ : ctx) (A : ty) → Type ℓ₁ where
    VN : {Γ : ctx} {A : ty} → IntVar Γ A → Ne Γ A
    APP : {Γ : ctx} {A B : ty} → Ne Γ (A ⇛ B) → Nf Γ A → Ne Γ B

  data Nf where
    NEU : {Γ : ctx} {c : Char} → Ne Γ (base c) → Nf Γ (base c)
    LAM : {Γ : ctx} {A B : ty} → Nf (Γ ⊹ A) B → Nf Γ (A ⇛ B)

  insertCtx : (Γ : ctx) (A : ty) (n : ℕ) → ctx
  insertCtx Γ A Z = Γ ⊹ A
  insertCtx ∅ A (S n) = ∅ ⊹ A
  insertCtx (Γ ⊹ B) A (S n) = insertCtx Γ A n ⊹ B

  SVar : {Γ : ctx} {A B : ty} (n : ℕ) → IntVar Γ A → IntVar (insertCtx Γ B n) A
  SNe : {Γ : ctx} {A B : ty} (n : ℕ) → Ne Γ A → Ne (insertCtx Γ B n) A
  SNf : {Γ : ctx} {A B : ty} (n : ℕ) → Nf Γ A → Nf (insertCtx Γ B n) A

  SVar Z v = 𝑠𝑣 v
  SVar (S n) 𝑧𝑣 = 𝑧𝑣
  SVar (S n) (𝑠𝑣 v) = 𝑠𝑣 (SVar n v)

  SNe n (VN v) = VN (SVar n v)
  SNe n (APP M N) = APP (SNe n M) (SNf n N)

  SNf n (NEU M) = NEU (SNe n M)
  SNf n (LAM N) = LAM (SNf (S n) N)

  infix 30 _[_]NE _[_]NF
  _[_]NE : {Γ Δ : ctx} {A : ty} → Ne Δ A → IntRen Γ Δ → Ne Γ A
  _[_]NF : {Γ Δ : ctx} {A : ty} → Nf Δ A → IntRen Γ Δ → Nf Γ A

  APP M N [ σ ]NE = APP (M [ σ ]NE) (N [ σ ]NF)
  VN v [ σ ]NE = VN (v R.⟦ σ ⟧)

  NEU M [ σ ]NF = NEU (M [ σ ]NE)
  LAM {A = A} N [ σ ]NF = LAM (N [ W₂𝑅𝑒𝑛 A σ ]NF)

  [id]NE : {Γ : ctx} {A : ty} → (M : Ne Γ A) →
    M [ R.𝒾𝒹 Γ ]NE ≡ M
  [id]NF : {Γ : ctx} {A : ty} → (N : Nf Γ A) →
    N [ R.𝒾𝒹 Γ ]NF ≡ N

  [id]NE (VN 𝑧𝑣) = refl
  [id]NE (VN (𝑠𝑣 v)) =
    VN (v R.⟦ W₁𝑅𝑒𝑛 _ (R.𝒾𝒹 _) ⟧)
      ≡⟨ ap VN (Wlem2𝑅𝑒𝑛 v (R.𝒾𝒹 _)) ⟩
    VN (𝑠𝑣 (v R.⟦ R.𝒾𝒹 _ ⟧))
      ≡⟨ ap VN (ap 𝑠𝑣 (R.𝒾𝒹⟦⟧ v)) ⟩
    VN (𝑠𝑣 v)
      ∎
  [id]NE (APP M N) i = APP ([id]NE M i) ([id]NF N i)

  [id]NF (NEU M) = ap NEU ([id]NE M)
  [id]NF (LAM N) = ap LAM ([id]NF N)

  [][]NE : {Γ Δ Σ : ctx} {A : ty} (M : Ne Σ A) (σ : IntRen Δ Σ) (τ : IntRen Γ Δ) →
    M [ σ ]NE [ τ ]NE ≡ M [ σ R.⊚ τ ]NE
  [][]NF : {Γ Δ Σ : ctx} {A : ty} (N : Nf Σ A) (σ : IntRen Δ Σ) (τ : IntRen Γ Δ) →
    N [ σ ]NF [ τ ]NF ≡ N [ σ R.⊚ τ ]NF

  [][]NE (VN v) σ τ = ap VN (R.⟦⟧⟦⟧ v σ τ)
  [][]NE (APP M N) σ τ i = APP ([][]NE M σ τ i) ([][]NF N σ τ i)

  [][]NF (NEU M) σ τ = ap NEU ([][]NE M σ τ)
  [][]NF (LAM N) σ τ =
    LAM (N [ W₂𝑅𝑒𝑛 _ σ ]NF [ W₂𝑅𝑒𝑛 _ τ ]NF)
      ≡⟨ ap LAM ([][]NF N (W₂𝑅𝑒𝑛 _ σ) (W₂𝑅𝑒𝑛 _ τ) ) ⟩
    LAM (N [ W₂𝑅𝑒𝑛 _ σ R.⊚ W₂𝑅𝑒𝑛 _ τ ]NF)
      ≡⟨ (λ i → LAM (N [ Wlem4𝑅𝑒𝑛 σ τ i ]NF)) ⟩
    LAM (N [ W₂𝑅𝑒𝑛 _ (σ R.⊚ τ) ]NF)
      ∎

  isSetNeutral : {Γ : ctx} {A : ty} → isSet (Ne Γ A)
  isSetNeutral = {!!}

  isSetNormal : {Γ : ctx} {A : ty} → isSet (Nf Γ A)
  isSetNormal = {!!}

  ιNe : {Γ : ctx} {A : ty} → Ne Γ A → tm Γ A
  ιNf : {Γ : ctx} {A : ty} → Nf Γ A → tm Γ A

  ιNe (VN v) = makeVar v
  ιNe (APP M N) = 𝑎𝑝𝑝 (ιNe M) (ιNf N)

  ιNf (NEU M) = ιNe M
  ιNf (LAM N) = Λ (ιNf N)

  ιNeLem : {Γ Δ : ctx} {A : ty} (M : Ne Δ A) (σ : IntRen Γ Δ) →
    ιNe (M [ σ ]NE) ≡ ιNe M ⟦ makeRen σ ⟧
  ιNfLem : {Γ Δ : ctx} {A : ty} (N : Nf Δ A) (σ : IntRen Γ Δ) →
    ιNf (N [ σ ]NF) ≡ ιNf N ⟦ makeRen σ ⟧

  ιNeLem (VN v) σ = make[]𝑅 v σ
  ιNeLem (APP M N) σ =
    𝑎𝑝𝑝 (ιNe (M [ σ ]NE)) (ιNf (N [ σ ]NF))
      ≡⟨ (λ i → 𝑎𝑝𝑝 (ιNeLem M σ i) (ιNfLem N σ i)) ⟩
    𝑎𝑝𝑝 (ιNe M ⟦ makeRen σ ⟧) (ιNf N ⟦ makeRen σ ⟧)
      ≡⟨ 𝑎𝑝𝑝⟦⟧ (ιNe M) (ιNf N) (makeRen σ) ⁻¹ ⟩
    𝑎𝑝𝑝 (ιNe M) (ιNf N) ⟦ makeRen σ ⟧
      ∎

  ιNfLem (NEU M) σ = ιNeLem M σ
  ιNfLem (LAM {Γ} {A} N) σ =
    Λ (ιNf (N [ W₂𝑅𝑒𝑛 A σ ]NF))
      ≡⟨ ap Λ (ιNfLem N (W₂𝑅𝑒𝑛 A σ)) ⟩
    Λ (ιNf N ⟦ makeRen (W₂𝑅𝑒𝑛 A σ) ⟧)
      ≡⟨ (λ i → Λ (ιNf N ⟦ makeW₁ σ i ⊕ 𝑧 ⟧)) ⟩
    Λ (ιNf N ⟦ W₂tms A (makeRen σ) ⟧)
      ≡⟨ Λnat (ιNf N) (makeRen σ) ⁻¹ ⟩
    Λ (ιNf N) ⟦ makeRen σ ⟧
      ∎

{-
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

SVar Z v = 𝑠𝑣 v
SVar (S n) 𝑧𝑣 = 𝑧𝑣
SVar (S n) (𝑠𝑣 v) = 𝑠𝑣 (SVar n v)

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

[id]NE (VN 𝑧𝑣) = refl
[id]NE (VN (𝑠𝑣 v)) =
  VN (v [ W₁Ren _ (idRen _) ]R)
    ≡⟨ ap VN (Wlem2Ren v (idRen _)) ⟩
  VN (𝑠𝑣 (v [ idRen _ ]R))
    ≡⟨ ap VN (ap 𝑠𝑣 ([id]Ren v)) ⟩
  VN (𝑠𝑣 v)
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
  F-ob (NE A) Γ = Ne Γ A , isSetNeutral
  F-hom (NE A) σ M = M [ σ ]NE
  F-id (NE A) i M = [id]NE M i
  F-seq (NE A) σ τ i M = [][]NE M σ τ (~ i)

  NF : Ty → ob (PSh REN)
  F-ob (NF A) Γ = Nf Γ A , isSetNormal
  F-hom (NF A) σ N = N [ σ ]NF
  F-id (NF A) i N = [id]NF N i
  F-seq (NF A) σ τ i N = [][]NF N σ τ (~ i)

ιNe : {Γ : Ctx} {A : Ty} → Ne Γ A → Tm Γ A
ιNf : {Γ : Ctx} {A : Ty} → Nf Γ A → Tm Γ A

ιNe (VN v) = V v
ιNe (APP M N) = App (ιNe M) (ιNf N)

ιNf (NEU M) = ιNe M
ιNf (LAM N) = Lam (ιNf N)

ιNeLem : {Γ Δ : Ctx} {A : Ty} (M : Ne Δ A) (σ : Ren Γ Δ) →
  ιNe (M [ σ ]NE) ≡ ιNe M [ varify σ ]
ιNfLem : {Γ Δ : Ctx} {A : Ty} (N : Nf Δ A) (σ : Ren Γ Δ) →
  ιNf (N [ σ ]NF) ≡ ιNf N [ varify σ ]

ιNeLem (VN v) σ = Vlem0 v σ
ιNeLem (APP M N) σ =
  App (ιNe (M [ σ ]NE)) (ιNf (N [ σ ]NF))
    ≡⟨ (λ i → App (ιNeLem M σ i) (ιNfLem N σ i)) ⟩
  App (ιNe M [ varify σ ]) (ιNf N [ varify σ ])
    ≡⟨ App[] (ιNe M) (ιNf N) (varify σ) ⁻¹ ⟩
  App (ιNe M) (ιNf N) [ varify σ ]
    ∎

ιNfLem (NEU M) σ = ιNeLem M σ
ιNfLem (LAM {Γ} {A} N) σ =
  Lam (ιNf (N [ W₂Ren A σ ]NF))
    ≡⟨ ap Lam (ιNfLem N (W₂Ren A σ)) ⟩
  Lam (ιNf N [ varify (W₁Ren A σ) ⊕ V 𝑧𝑣 ])
    ≡⟨ (λ i → Lam (ιNf N [ Vlem2 σ i ⊕ V 𝑧𝑣 ])) ⟩
  Lam (ιNf N [ W₂Tms A (varify σ) ])
    ≡⟨ Lam[] (ιNf N) (varify σ) ⁻¹ ⟩
  Lam (ιNf N) [ varify σ ]
    ∎

-- imported here because I know of no way to hide the syntax _⇒_
open import Cubical.Categories.NaturalTransformation

module _ where
  open NatTrans
  open Precategory (PSh REN)
  open Contextual (𝒫𝒮𝒽 REN)

  ιNE : (A : Ty) → Hom[ NE A , TM A ]
  N-ob (ιNE A) Γ = ιNe
  N-hom (ιNE A) σ i M = ιNeLem M σ i

  ιNF : (A : Ty) → Hom[ NF A , TM A ]
  N-ob (ιNF A) Γ = ιNf
  N-hom (ιNF A) σ i N = ιNfLem N σ i

  NES = plurify NE
  NFS = plurify NF

  ιNES : (Γ : Ctx) → tms (NES Γ) (TMS Γ)
  ιNES = weaveTrans ιNE

  ιNFS : (Γ : Ctx) → tms (NFS Γ) (TMS Γ)
  ιNFS = weaveTrans ιNF
-}
