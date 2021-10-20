{-# OPTIONS --cubical #-}

module twglue where

open import cartesian
open import ren
open import syn2
open import eliminator2

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything renaming (cong to ap)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Agda.Builtin.Char
open import Cubical.Categories.Presheaf
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.Unit as ⊤ renaming (Unit to ⊤)
open import Cubical.Data.Empty as ⊥

module _ where
  open Precategory (PSh REN) hiding (_∘_)
  open NatTrans
  open Cartesian (PShCart {𝒞 = REN})

  record Glueing (A : Ty) : Set (lsuc lzero) where
    constructor Gl
    field
      Gl-⦇A⦈ : ob
      Gl-u : Hom[ NE A , Gl-⦇A⦈ ]
      Gl-q : Hom[ Gl-⦇A⦈ , NF A ]
      Gl-comp : {Δ : Ctx} → includeNormal ∘ N-ob Gl-q Δ ∘ N-ob Gl-u Δ ≡ includeNeutral

  data Glueings : (Γ : Ctx) → Set (lsuc lzero) where
    !Glu : Glueings ∅
    _⊕Gl_ : {Γ : Ctx} {A : Ty} → Glueings Γ → Glueing A → Glueings (Γ ⊹ A)

  open Glueing

  Gls-⦇Γ⦈ : {Γ : Ctx} → Glueings Γ → ob
  Gls-⦇Γ⦈ !Glu = C-1
  Gls-⦇Γ⦈ (𝒢𝒮 ⊕Gl 𝒢) = C-× (Gls-⦇Γ⦈ 𝒢𝒮) (Gl-⦇A⦈ 𝒢)

  Gls-u : {Γ : Ctx} → (𝒢 : Glueings Γ) → Hom[ NES Γ , Gls-⦇Γ⦈ 𝒢 ]
  Gls-u !Glu = C-!
  N-ob (Gls-u (𝒢𝒮 ⊕Gl 𝒢)) Δ (MS ⊕NE M) =
    N-ob (Gls-u 𝒢𝒮) Δ MS , N-ob (Gl-u 𝒢) Δ M
  N-hom (Gls-u (𝒢𝒮 ⊕Gl 𝒢)) σ i (MS ⊕NE M) =
    N-hom (Gls-u 𝒢𝒮) σ i MS , N-hom (Gl-u 𝒢) σ i M

  Gls-q : {Γ : Ctx} → (𝒢 : Glueings Γ) → Hom[ Gls-⦇Γ⦈ 𝒢 , NFS Γ ]
  N-ob (Gls-q !Glu) Δ _ = !NF
  N-hom (Gls-q !Glu) σ = refl
  N-ob (Gls-q (𝒢𝒮 ⊕Gl 𝒢)) Δ (𝓈𝒮 , 𝓈) =
    N-ob (Gls-q 𝒢𝒮) Δ 𝓈𝒮 ⊕NF N-ob (Gl-q 𝒢) Δ 𝓈
  N-hom (Gls-q (𝒢𝒮 ⊕Gl 𝒢)) σ i (𝓈𝒮 , 𝓈) =
    N-hom (Gls-q 𝒢𝒮) σ i 𝓈𝒮 ⊕NF N-hom (Gl-q 𝒢) σ i 𝓈

  {-record Glueings (Γ : Ctx) : Set (lsuc lzero) where
    constructor Gls
    field
      Gls-Γ : Ctx
      Gls-⦇Γ⦈ : ob
      Gls-u : Hom-}

  {-record GlueMor (𝒢 ℋ : Glueing): Set (lsuc lzero) where
    constructor GlMor

    open Glueing
    field
      GlMor-⦇α⦈ : Hom[ Gl-⦇Γ⦈ 𝒢 , Gl-⦇Γ⦈ ℋ ]
      GlMor-α : Tms (Gl-Γ 𝒢) (Gl-Γ ℋ)
      GlMot-nat : includeNormals ∘ N-ob (Gl-q ℋ) (Gl-Γ ℋ) ∘ N-ob GlMor-⦇α⦈ ≡ ?-}
