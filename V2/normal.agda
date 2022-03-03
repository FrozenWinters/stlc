{-# OPTIONS --cubical --allow-unsolved-metas #-}

module normal where

open import lists
open import contextual
open import ccc
open import psh

open import Cubical.Data.Nat renaming (zero to Z; suc to S) hiding (elim)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private
  variable
    ℓ : Level

-- We define normal and neutral terms

module Normal (𝒞 : Contextual ℓ ℓ) ⦃ 𝒞CCC : CCC 𝒞 ⦄
              {X : Type ℓ} (base : X → Contextual.ty 𝒞) where
  open Contextual 𝒞
  open CCC 𝒞CCC
  open Presheaf REN

  private
    module R = Contextual ρεν

  data Ne : (Γ : ctx) (A : ty) → Type ℓ
  data Nf : (Γ : ctx) (A : ty) → Type ℓ

  data Ne where
    VN : {Γ : ctx} {A : ty} → IntVar Γ A → Ne Γ A
    APP : {Γ : ctx} {A B : ty} → Ne Γ (A ⇛ B) → Nf Γ A → Ne Γ B

  data Nf where
    NEU : {Γ : ctx} {x : X} → Ne Γ (base x) → Nf Γ (base x)
    LAM : {Γ : ctx} {A B : ty} → Nf (Γ ⊹ A) B → Nf Γ (A ⇛ B)

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
      ≡⟨ (λ i → Λ (ιNf N ⟦ makeW σ i ⊕ 𝑧 ⟧)) ⟩
    Λ (ιNf N ⟦ W₂tms A (makeRen σ) ⟧)
      ≡⟨ Λnat (ιNf N) (makeRen σ) ⁻¹ ⟩
    Λ (ιNf N) ⟦ makeRen σ ⟧
      ∎

  Nes = 𝑇𝑚𝑠 Ne
  Nfs = 𝑇𝑚𝑠 Nf

  _[_]NFS : {Γ Δ Σ : ctx} → Nfs Δ Σ → IntRen Γ Δ → Nfs Γ Σ
  NS [ σ ]NFS = map𝐸𝑙𝑠 _[ σ ]NF NS

  ιNes : {Γ Δ : ctx} → Nes Γ Δ → tms Γ Δ
  ιNes = map𝐸𝑙𝑠 ιNe

  ιNfs : {Γ Δ : ctx} → Nfs Γ Δ → tms Γ Δ
  ιNfs = map𝐸𝑙𝑠 ιNf

  ιNfsLem : {Γ Δ Σ : ctx} (NS : Nfs Δ Σ) (σ : IntRen Γ Δ) →
    ιNfs (NS [ σ ]NFS) ≡ ιNfs NS ⊚ (makeRen σ)
  ιNfsLem ! σ = refl
  ιNfsLem (NS ⊕ N) σ i = ιNfsLem NS σ i ⊕ ιNfLem N σ i

  idNes : (Γ : ctx) → Nes Γ Γ
  idNes Γ = map𝐸𝑙𝑠 VN (id𝑅𝑒𝑛 Γ)

  ιIdNes : (Γ : ctx) → ιNes (idNes Γ) ≡ 𝒾𝒹 Γ
  ιIdNes Γ =
    map𝐸𝑙𝑠 ιNe (map𝐸𝑙𝑠 VN (id𝑅𝑒𝑛 Γ))
      ≡⟨ map𝐸𝑙𝑠comp ιNe VN (id𝑅𝑒𝑛 Γ) ⟩
    makeRen (id𝑅𝑒𝑛 Γ)
      ≡⟨ 𝒾𝒹η₂ ⟩
    𝒾𝒹 Γ
      ∎

  open PSh
  open PShMorCart

  TM : (A : ty) → PSh
  sec (TM A) Γ = tm Γ A
  isSetSec (TM A) = isSetTm
  hom (TM A) σ t = t ⟦ makeRen σ ⟧
  id-hom (TM A) t = ap (t ⟦_⟧) 𝒾𝒹η₂ ∙ 𝒾𝒹⟦⟧ t
  ⊚-hom (TM A) σ τ t = ap (t ⟦_⟧) (make∘𝑅𝑒𝑛 σ τ) ∙ ⟦⟧⟦⟧ t (makeRen σ) (makeRen τ) ⁻¹

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
