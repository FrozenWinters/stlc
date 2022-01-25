{-# OPTIONS --cubical --allow-unsolved-metas #-}

module norm where

open import contextual
open import ccc
open import presheaves
open import twgl
open import twglccc

open import Cubical.Data.Nat renaming (zero to Z; suc to S) hiding (elim)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Categories.Instances.Sets

module Norm {ℓ} (𝒞 : Contextual ℓ ℓ) ⦃ 𝒞CCC : CCC 𝒞 ⦄ (base : Char → Contextual.ty 𝒞)
                (init : ∀ {ℓ₁ ℓ₂} → InitialCCC 𝒞 ⦃ 𝒞CCC ⦄ base {ℓ₁} {ℓ₂}) where
  open Presheaves 𝒞 base
  open TwGlCC 𝒞 base
  open TwGlCCC 𝒞 base
  open Glueing
  open GlTm
  open Contextual 𝒞
  open CCC 𝒞CCC

  private
    module T = Contextual TwGl
    module Tc = CCC isCCCTwGl

  NEULem : {Γ Δ : ctx} {X : Char} (M : Ne Δ (base X)) (σ : IntRen Γ Δ) →
    NEU (M [ σ ]NE) ≡ NEU M [ σ ]NF
  NEULem (VN v) σ = refl
  NEULem (APP M N) σ = refl

  open NatTrans

  baseGl : (X : Char) → Glueing
  Gl-A (baseGl X) = base X
  Gl-⦇A⦈ (baseGl X) = NF (base X)
  N-ob (Gl-u (baseGl X)) Γ M = NEU M
  N-hom (Gl-u (baseGl X)) σ i M = NEULem M σ i
  Gl-q (baseGl X) = idTrans (NF (base X))
  Gl-comp (baseGl X) = makeNatTransPath (λ i Σ M → ιNe M)

  module _ where
    open InitialInstance (init TwGl baseGl)

    ⟪elim⟫ : ContextualFunctor 𝒞 TwGl
    ⟪elim⟫ = elim

    ⟪elim⟫-cp = ccc-pres
    ⟪elim⟫-bp = base-pres

  module _ where
    open InitialInstance (init 𝒞 base)
    ⟪elim⟫-UP = UP

  open ContextualFunctor
  open CCCPreserving

  ⟪GlTm-α⟫ : ContextualFunctor TwGl 𝒞
  CF-ty ⟪GlTm-α⟫ A = Gl-A A
  CF-tm ⟪GlTm-α⟫ t = GlTm-α t
  CF-id ⟪GlTm-α⟫ = idTwGl-αs
  CF-sub ⟪GlTm-α⟫ t σ = refl


  ⟪GlTm-α⟫-cp : CCCPreserving ⟪GlTm-α⟫
  pres-⇛ ⟪GlTm-α⟫-cp A B = refl
  pres-𝐴𝑝𝑝 ⟪GlTm-α⟫-cp {Γ} {A} {B} t =
    𝑎𝑝𝑝 (GlTm-α (t T.⟦ T.π ⟧)) 𝑧
      ≡⟨ (λ i → 𝑎𝑝𝑝 (GlTm-α t ⟦ π𝑇𝑚𝑠 (idTwGl-αs {Γ ⊹ A} i) ⟧) 𝑧) ⟩
    𝐴𝑝𝑝 (TwGlCC.GlTm.GlTm-α t)
      ≡⟨ ap 𝐴𝑝𝑝 (transportRefl (GlTm-α t)) ⁻¹ ⟩
    𝐴𝑝𝑝 (transport refl (GlTm-α t))
      ∎ 

  ⟪F⟫ : ContextualFunctor 𝒞 𝒞
  ⟪F⟫ = ⟪GlTm-α⟫ ∘CF ⟪elim⟫

  ⟪id⟫ : ContextualFunctor 𝒞 𝒞
  ⟪id⟫ = idCF 𝒞

  transport𝐴𝑝𝑝 : {Γ Δ : ctx} {A B : ty} (a : Γ ≡ Δ) (t : tm Γ (A ⇛ B)) →
    transport (λ i → tm (a i ⊹ A) B) (𝐴𝑝𝑝 t) ≡ 𝐴𝑝𝑝 (transport (λ i → tm (a i) (A ⇛ B)) t)
  transport𝐴𝑝𝑝 {Γ} {Δ} {A} {B} a t =
    J (λ Δ a → transport (λ i → tm (a i ⊹ A) B) (𝐴𝑝𝑝 t)
      ≡ 𝐴𝑝𝑝 (transport (λ i → tm (a i) (A ⇛ B)) t))
      (transportRefl (𝐴𝑝𝑝 t) ∙ ap 𝐴𝑝𝑝 (transportRefl t ⁻¹)) a

  ⟪id⟫-cp : CCCPreserving ⟪id⟫
  pres-⇛ ⟪id⟫-cp A B = refl
  pres-𝐴𝑝𝑝 ⟪id⟫-cp {Γ} t =
    CF-tm ⟪id⟫ (𝐴𝑝𝑝 t)
      ≡⟨ transport𝐴𝑝𝑝 (map𝐶𝑡𝑥id Γ ⁻¹) t ⟩
    𝐴𝑝𝑝 (CF-tm ⟪id⟫ t)
          ≡⟨ (λ i → 𝐴𝑝𝑝 (transportRefl (CF-tm ⟪id⟫ t) (~ i))) ⟩
    𝐴𝑝𝑝 (transport refl (CF-tm ⟪id⟫ t))
      ∎

  ⟪F⟫≡⟪id⟫ : ⟪F⟫ ≡ ⟪id⟫
  ⟪F⟫≡⟪id⟫ =
    ⟪elim⟫-UP ⟪F⟫ (∘CF-CCCPres ⟪GlTm-α⟫-cp ⟪elim⟫-cp) (λ c → ap Gl-A (⟪elim⟫-bp c))
    ∙ ⟪elim⟫-UP ⟪id⟫ ⟪id⟫-cp (λ c → refl) ⁻¹

  interpTy = CF-ty ⟪elim⟫
  interpCtx = CF-ctx ⟪elim⟫

  interpTyLem : (A : ty) → Gl-A (CF-ty ⟪elim⟫ A) ≡ A
  interpTyLem A i = CF-ty (⟪F⟫≡⟪id⟫ i) A

  interpCtxLem' : (Γ : ctx) → CF-ctx ⟪F⟫ Γ ≡ CF-ctx ⟪id⟫ Γ
  interpCtxLem' Γ i = CF-ctx (⟪F⟫≡⟪id⟫ i) Γ

  interpCtxLem : (Γ : ctx) → Gls-Γ (CF-ctx ⟪elim⟫ Γ) ≡ Γ
  interpCtxLem Γ =
    map𝐶𝑡𝑥comp Gl-A (CF-ty ⟪elim⟫) Γ
    ∙ interpCtxLem' Γ
    ∙ map𝐶𝑡𝑥id Γ

  sem : {Γ : ctx} {A : ty} → tm Γ A → GlTm (interpCtx Γ) (interpTy A)
  sem = CF-tm ⟪elim⟫

  interpTmLem : {Γ : ctx} {A : ty} (t : tm Γ A) →
    transport (λ i → tm (interpCtxLem Γ i) (interpTyLem A i)) (GlTm-α (sem t)) ≡ t
  interpTmLem {Γ} {A} t =
    transport (λ i → tm (interpCtxLem Γ i) (interpTyLem A i)) (GlTm-α (sem t))
      ≡⟨ (λ j → transport (λ i → tm (interpCtxLem Γ i) (lUnit (rUnit (interpTyLem A) j) j i))
        (GlTm-α (sem t))) ⟩
    transport (λ i → tm (interpCtxLem Γ i) ((refl ∙ interpTyLem A ∙ refl) i)) (GlTm-α (sem t))
      ≡⟨ transport-tm (map𝐶𝑡𝑥comp Gl-A (CF-ty ⟪elim⟫) Γ) refl
        (interpCtxLem' Γ ∙ map𝐶𝑡𝑥id Γ) (interpTyLem A ∙ refl) (GlTm-α (sem t)) ⁻¹ ⟩
    transport (λ i → tm ((interpCtxLem' Γ ∙ map𝐶𝑡𝑥id Γ) i) ((interpTyLem A ∙ refl) i))
      (CF-tm ⟪F⟫ t)
      ≡⟨ transport-tm (interpCtxLem' Γ ) (interpTyLem A) (map𝐶𝑡𝑥id Γ) refl (CF-tm ⟪F⟫ t) ⁻¹ ⟩
    transport (λ i → tm (map𝐶𝑡𝑥id Γ i) A)
      (transport (λ i → tm (interpCtxLem' Γ i) (interpTyLem A i)) (CF-tm ⟪F⟫ t))
      ≡⟨ ap (transport (λ i → tm (map𝐶𝑡𝑥id Γ i) A)) (fromPathP (λ i → CF-tm (⟪F⟫≡⟪id⟫ i) t)) ⟩
    transport (λ i → tm (map𝐶𝑡𝑥id Γ i) A) (transport (λ i → tm (map𝐶𝑡𝑥id Γ (~ i)) A) t)
      ≡⟨ substComposite (λ Γ → tm Γ A) (map𝐶𝑡𝑥id Γ ⁻¹) (map𝐶𝑡𝑥id Γ) t ⁻¹ ⟩
    transport (λ i → tm ((map𝐶𝑡𝑥id Γ ⁻¹ ∙ map𝐶𝑡𝑥id Γ) i) A) t
      ≡⟨ (λ j → transport (λ i → tm (lCancel (map𝐶𝑡𝑥id Γ) j i) A) t) ⟩
    transport (λ i → tm (refl i) A) t
      ≡⟨ transportRefl t ⟩
    t
      ∎

  norm : {Γ : ctx} {A : ty} → tm Γ A → Nf Γ A
  norm {Γ} {A} t =
    transport (λ i → Nf (interpCtxLem Γ i) (interpTyLem A i)) (GlTm-norm (sem t))

  transportFibrewise : ∀ {ℓ₁ ℓ₂} {A₁ A₂ : Type ℓ₁} {B₁ B₂ : Type ℓ₂} {p : A₁ ≡ A₂}
    {q : B₁ ≡ B₂} {f : A₁ → B₁} {g : A₂ → B₂} (a : PathP (λ i → p i → q i) f g) (x : A₁) →
    transport q (f x) ≡ g (transport p x)
  transportFibrewise {A₁ = A₁} {p = p} {q} {f} {g} a x =
    transport (λ i → transport (λ j → q (i ∧ j)) (f x) ≡ a i (transport (λ j → p (i ∧ j)) x))
      (transportRefl (f x) ∙ (λ i →  f (transportRefl x (~ i))))

  correctness : {Γ : ctx} {A : ty} (t : tm Γ A) → ιNf (norm t) ≡ t
  correctness {Γ} {A} t =
    ιNf (norm t)
      ≡⟨ transportFibrewise
        (λ i → ιNf {interpCtxLem Γ i} {interpTyLem A i}) (GlTm-norm (sem t)) ⁻¹ ⟩
    transport (λ i → tm (interpCtxLem Γ i) (interpTyLem A i)) (ιNf (GlTm-norm (sem t)))
      ≡⟨ ap (transport (λ i → tm (interpCtxLem Γ i) (interpTyLem A i)))
        (GlTm-correctness (sem t)) ⟩
    transport (λ i → tm (interpCtxLem Γ i) (interpTyLem A i)) (GlTm-α (sem t))
      ≡⟨ interpTmLem t ⟩
    t
      ∎
