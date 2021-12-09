{-# OPTIONS --cubical --allow-unsolved-metas #-}

module twglccc where

open import contextual
open import ccc
open import cart
open import psh
open import presheaves
open import twgl

open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Categories.Instances.Sets

module TwGlCCC {ℓ} (𝒞 : Contextual ℓ ℓ) ⦃ 𝒞CCC : CCC 𝒞 ⦄ (base : Char → Contextual.ty 𝒞) where
  open Presheaves 𝒞 base
  open TwGlCC 𝒞 base
  open CCC 𝒞CCC
  open Contextual 𝒞
  private
    module P = Contextual 𝒫𝒮𝒽
    module R = Contextual ρεν
    module T = Contextual TwGl
  open Cartesian (PShCart {𝒞 = REN})
  open Glueing
  open GlTm
  open Precategory 𝑃𝑆ℎ hiding (_∘_)
  open NatTrans
  open Functor

  A-A⇒B : (A B : Glueing) → ty
  A-A⇒B A B = Gl-A A ⇛ Gl-A B

  q-A⇒B : (A B : Glueing) →
    Hom[ C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B) , NF (A-A⇒B A B) ]
  N-ob (q-A⇒B A B) Γ α =
    LAM (N-ob (Gl-q B) (Γ ⊹ 𝐴) (N-ob α (Γ ⊹ 𝐴)
      (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Γ) , N-ob (Gl-u A) (Γ ⊹ 𝐴) (VN 𝑧𝑣)))) where
        𝐴 = (Gl-A A)
  N-hom (q-A⇒B A B) {Δ} {Σ} σ i α =
    (LAM (N-ob (Gl-q B) (Σ ⊹ 𝐴) (N-ob α (Σ ⊹ 𝐴)
      (σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Σ) , N-ob (Gl-u A) (Σ ⊹ 𝐴) (VN 𝑧𝑣))))
      ≡⟨ (λ j → LAM (N-ob (Gl-q B) (Σ ⊹ 𝐴) (N-ob α (Σ ⊹ 𝐴)
        (lem j , N-hom (Gl-u A) (W₂𝑅𝑒𝑛 𝐴 σ) j (VN 𝑧𝑣))))) ⟩
    LAM (N-ob (Gl-q B) (Σ ⊹ 𝐴) (N-ob α (Σ ⊹ 𝐴) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ) ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 𝐴 σ ,
      (F-hom (Gl-⦇A⦈ A) (W₂𝑅𝑒𝑛 𝐴 σ) (N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣))))))
      ≡⟨ (λ j → LAM (N-ob (Gl-q B) (Σ ⊹ 𝐴) (N-hom α (W₂𝑅𝑒𝑛 𝐴 σ) j
        (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ) , N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣))))) ⟩
    LAM (N-ob (Gl-q B) (Σ ⊹ 𝐴) (F-hom (Gl-⦇A⦈ B) (W₂𝑅𝑒𝑛 𝐴 σ)
      (N-ob α (Δ ⊹ 𝐴) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ) , N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣)))))
      ≡⟨ (λ j → LAM (N-hom (Gl-q B) (W₂𝑅𝑒𝑛 𝐴 σ) j
        (N-ob α (Δ ⊹ 𝐴) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ) , N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣))))) ⟩
    LAM (N-ob (Gl-q B) (Δ ⊹ 𝐴)
      (N-ob α (Δ ⊹ 𝐴) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ) , N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣))) [ W₂𝑅𝑒𝑛 𝐴 σ ]NF)
      ∎) i where
      𝐴 = (Gl-A A)
      lem : σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Σ) ≡ W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ) ∘𝑅𝑒𝑛 (W₂𝑅𝑒𝑛 𝐴 σ)
      lem =
        σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Σ)
          ≡⟨ Wlem3𝑅𝑒𝑛 σ (id𝑅𝑒𝑛 Σ) ⟩
        W₁𝑅𝑒𝑛 𝐴 (σ ∘𝑅𝑒𝑛 id𝑅𝑒𝑛 Σ)
          ≡⟨ ap (W₁𝑅𝑒𝑛 𝐴) (R.𝒾𝒹R σ) ⟩
        W₁𝑅𝑒𝑛 𝐴 σ
          ≡⟨ ap (W₁𝑅𝑒𝑛 𝐴) (∘𝑅𝑒𝑛IdL σ ⁻¹) ⟩
        W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ ∘𝑅𝑒𝑛 σ)
          ≡⟨ Wlem5𝑅𝑒𝑛 (id𝑅𝑒𝑛 Δ) σ ⁻¹ ⟩
        W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ) ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 𝐴 σ
          ∎

  u-A⇒B : (A B : Glueing) →
    Hom[ NE (A-A⇒B A B) , C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B) ]
  N-ob (N-ob (u-A⇒B A B) Γ M) Δ (σ , 𝓈) =
    N-ob (Gl-u B) Δ (APP (M [ σ ]NE) (N-ob (Gl-q A) Δ 𝓈))
  N-hom (N-ob (u-A⇒B A B) Γ M) {Δ} {Σ} σ i (τ , 𝓈) =
    (N-ob (Gl-u B) Σ (APP (M [ τ ∘𝑅𝑒𝑛 σ ]NE) (N-ob (Gl-q A) Σ (F-hom (Gl-⦇A⦈ A) σ 𝓈)))
      ≡⟨ (λ j → N-ob (Gl-u B) Σ (APP ([][]NE M τ σ (~ j)) (N-hom (Gl-q A) σ j 𝓈))) ⟩
    N-ob (Gl-u B) Σ (APP (M [ τ ]NE) (N-ob (Gl-q A) Δ 𝓈) [ σ ]NE)
      ≡⟨ (λ j → N-hom (Gl-u B) σ j (APP (M [ τ ]NE) (N-ob (Gl-q A) Δ 𝓈))) ⟩
    F-hom (Gl-⦇A⦈ B) σ (N-ob (Gl-u B) Δ (APP (M [ τ ]NE) (N-ob (Gl-q A) Δ 𝓈)))
      ∎) i
  N-ob (N-hom (u-A⇒B A B) σ i M) Γ (τ , 𝓈) =
    N-ob (Gl-u B) Γ (APP ([][]NE M σ τ i) (N-ob (Gl-q A) Γ 𝓈))
  N-hom (N-hom (u-A⇒B A B) {Σ} {Ω} σ i M) {Γ} {Δ} τ j (μ , 𝓈) =
    isSet→SquareP (λ i j → snd (F-ob (Gl-⦇A⦈ B) Δ))
      (λ k → N-hom (N-ob (u-A⇒B A B) Ω (M [ σ ]NE)) τ k (μ , 𝓈))
      (λ k → N-hom (F-hom (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B)) σ (N-ob (u-A⇒B A B) Σ M)) τ k (μ , 𝓈))
      (λ k → N-ob (N-hom (u-A⇒B A B) σ k M) Δ (μ ∘𝑅𝑒𝑛 τ , F-hom (Gl-⦇A⦈ A) τ 𝓈))
      (λ k → F-hom (Gl-⦇A⦈ B) τ (N-ob (N-hom (u-A⇒B A B) σ k M) Γ (μ , 𝓈))) i j

  private
    comp-A⇒B-ob : (A B : Glueing) →
      N-ob (ιNF (A-A⇒B A B) 𝒩∘ (q-A⇒B A B) 𝒩∘ (u-A⇒B A B)) ≡ N-ob (ιNE (A-A⇒B A B))
    comp-A⇒B-ob A B i Γ M =
      (Λ (N-ob (ιNF 𝐵 𝒩∘ Gl-q B 𝒩∘ Gl-u B) (Γ ⊹ 𝐴)
        (APP (M [ W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Γ) ]NE) (N-ob (Gl-q A 𝒩∘ Gl-u A) (Γ ⊹ 𝐴) (VN 𝑧𝑣))))
        ≡⟨ (λ j → Λ (N-ob (Gl-comp B j) (Γ ⊹ 𝐴)
          (APP (M [ W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Γ) ]NE) (N-ob (Gl-q A 𝒩∘ Gl-u A) (Γ ⊹ 𝐴) (VN 𝑧𝑣))))) ⟩
      Λ (𝑎𝑝𝑝 (ιNe (M [ W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Γ) ]NE)) (N-ob (ιNF 𝐴 𝒩∘ Gl-q A 𝒩∘ Gl-u A) (Γ ⊹ 𝐴) (VN 𝑧𝑣)))
        ≡⟨ (λ j → Λ (𝑎𝑝𝑝 (ιNe (M [ W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Γ) ]NE)) (N-ob (Gl-comp A j) (Γ ⊹ 𝐴) (VN 𝑧𝑣)))) ⟩
      Λ (𝑎𝑝𝑝 (ιNe (M [ W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Γ) ]NE)) 𝑧)
        ≡⟨ (λ j → Λ (𝑎𝑝𝑝 (N-hom (ιNE (𝐴 ⇛ 𝐵)) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Γ)) j M) 𝑧)) ⟩
      Λ (𝑎𝑝𝑝 (ιNe M ⟦ makeRen (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Γ)) ⟧) 𝑧)
        ≡⟨ (λ j → Λ (𝑎𝑝𝑝 (ιNe M ⟦ πη j ⟧) 𝑧)) ⟩
      Λ (𝑎𝑝𝑝 (ιNe M ⟦ π ⟧) 𝑧)
        ≡⟨ 𝑎𝑝𝑝η (ιNe M) ⁻¹ ⟩
      ιNe M
        ∎) i where
        𝐴 = Gl-A A
        𝐵 = Gl-A B

  comp-A⇒B : (A B : Glueing) →
    ιNF (A-A⇒B A B) 𝒩∘ (q-A⇒B A B) 𝒩∘ (u-A⇒B A B) ≡ ιNE (A-A⇒B A B)
  comp-A⇒B A B = makeNatTransPath (comp-A⇒B-ob A B)

  record Subset {ℓ₁ ℓ₂ : Level} : Type (lsuc (ℓ₁ ⊔ ℓ₂))  where
    field
      Sub-A : Type ℓ₁
      Sub-q : isSet Sub-A
      Sub-B : Sub-A → Type ℓ₂
      Sub-p : (x : Sub-A) → (isProp (Sub-B x))
      
    type = Σ Sub-A Sub-B

    isSetType : isSet type
    isSetType = isSetΣ Sub-q (λ x → isProp→isSet (Sub-p x))
    
    subtypeLem : (x y : type) → fst x ≡ fst y → x ≡ y
    subtypeLem x y a i = a i , isOfHLevel→isOfHLevelDep 1 (λ z → Sub-p z) (snd x) (snd y) a i

  open Subset

  ⦇A⇒B⦈-ob : (A B : Glueing) (Γ : ctx) → Subset
  Sub-A (⦇A⇒B⦈-ob A B Γ) = fst (F-ob (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B)) Γ)
  Sub-q (⦇A⇒B⦈-ob A B Γ) = snd (F-ob (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B)) Γ)
  Sub-B (⦇A⇒B⦈-ob A B Γ) α = (Δ : ctx) (σ : IntRen Δ Γ) (x : fst (F-ob (Gl-⦇A⦈ A) Δ)) →
    ιNf (N-ob (Gl-q B) Δ (N-ob α Δ (σ , x)))
      ≡ 𝑎𝑝𝑝 (ιNf (N-ob (q-A⇒B A B) Γ α [ σ ]NF)) (ιNf (N-ob (Gl-q A) Δ x))
  Sub-p (⦇A⇒B⦈-ob A B Γ) α = isPropΠ3 (λ Δ σ y → isSetTm _ _)

  _⇒TwGl_ : Glueing → Glueing → Glueing
  Gl-A (A ⇒TwGl B) = A-A⇒B A B
  
  F-ob (Gl-⦇A⦈ (A ⇒TwGl B)) Γ = type (⦇A⇒B⦈-ob A B Γ) , isSetType (⦇A⇒B⦈-ob A B Γ)
  F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) {Γ} {Δ} σ (α , p) =
    F-hom (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B)) σ α ,
      λ Σ τ x →
        ιNf (N-ob (Gl-q B) Σ (N-ob α Σ (σ ∘𝑅𝑒𝑛 τ , x)))
          ≡⟨ p Σ (σ ∘𝑅𝑒𝑛 τ) x ⟩
        𝑎𝑝𝑝 (ιNf (N-ob (q-A⇒B A B) Γ α [ σ ∘𝑅𝑒𝑛 τ ]NF)) (ιNf (N-ob (Gl-q A) Σ x))
          ≡⟨ (λ i → 𝑎𝑝𝑝 (ιNf ([][]NF (N-ob (q-A⇒B A B) Γ α) σ τ (~ i)))
            (ιNf (N-ob (Gl-q A) Σ x))) ⟩
        𝑎𝑝𝑝 (ιNf (N-ob (q-A⇒B A B) Γ α [ σ ]NF [ τ ]NF)) (ιNf (N-ob (Gl-q A) Σ x))
          ≡⟨ (λ i → 𝑎𝑝𝑝 (ιNf (N-hom (q-A⇒B A B) σ (~ i) α [ τ ]NF))
            (ιNf (N-ob (Gl-q A) Σ x))) ⟩
        𝑎𝑝𝑝 (ιNf (N-ob (q-A⇒B A B) Δ (F-hom (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B)) σ α) [ τ ]NF))
          (ιNf (N-ob (Gl-q A) Σ x))
          ∎
  F-id (Gl-⦇A⦈ (A ⇒TwGl B)) {Γ} i (α , p) =
    (subtypeLem (⦇A⇒B⦈-ob A B Γ)
      (F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) (id𝑅𝑒𝑛 Γ) (α , p)) (α , p)
      (λ j → F-id (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B)) j α)) i
  F-seq (Gl-⦇A⦈ (A ⇒TwGl B)) {Γ} {Δ} {Σ} σ τ i (α , p) =
    (subtypeLem (⦇A⇒B⦈-ob A B Σ)
      (F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) (σ ∘𝑅𝑒𝑛 τ) (α , p))
      (F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) τ (F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) σ (α , p)))
      (λ j → F-seq (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B)) σ τ j α)) i
  
  N-ob (Gl-u (A ⇒TwGl B)) Γ M = N-ob (u-A⇒B A B) Γ M ,
    λ Δ σ x →
      ιNf (N-ob (Gl-q B) Δ (N-ob (Gl-u B) Δ (APP (M [ σ ]NE) (N-ob (Gl-q A) Δ x))))
        ≡⟨ (λ i → N-ob (Gl-comp B i) Δ (APP (M [ σ ]NE) (N-ob (Gl-q A) Δ x))) ⟩
      𝑎𝑝𝑝 (ιNe (M [ σ ]NE)) (ιNf (N-ob (Gl-q A) Δ x))
        ≡⟨ (λ i → 𝑎𝑝𝑝 (ιNeLem M σ i) (ιNf (N-ob (Gl-q A) Δ x))) ⟩
      𝑎𝑝𝑝 (ιNe M ⟦ makeRen σ ⟧) (ιNf (N-ob (Gl-q A) Δ x))
        ≡⟨ (λ i → 𝑎𝑝𝑝 (N-ob (comp-A⇒B A B (~ i)) Γ M ⟦ makeRen σ ⟧)
          (ιNf (N-ob (Gl-q A) Δ x))) ⟩
      𝑎𝑝𝑝 (ιNf (N-ob (q-A⇒B A B) Γ (N-ob (u-A⇒B A B) Γ M)) ⟦ makeRen σ ⟧)
        (ιNf (N-ob (Gl-q A) Δ x))
        ≡⟨ (λ i → 𝑎𝑝𝑝 (ιNfLem (N-ob (q-A⇒B A B) Γ (N-ob (u-A⇒B A B) Γ M)) σ (~ i))
          (ιNf (N-ob (Gl-q A) Δ x))) ⟩
      𝑎𝑝𝑝 (ιNf (N-ob (q-A⇒B A B) Γ (N-ob (u-A⇒B A B) Γ M) [ σ ]NF))
         (ιNf (N-ob (Gl-q A) Δ x))
        ∎
  N-hom (Gl-u (A ⇒TwGl B)) {Γ} {Δ} σ i M =
    (subtypeLem (⦇A⇒B⦈-ob A B Δ)
      (N-ob (Gl-u (A ⇒TwGl B)) Δ (F-hom (NE (Gl-A (A ⇒TwGl B))) σ M))
      (F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) σ (N-ob (Gl-u (A ⇒TwGl B)) Γ M))
      (λ j → N-hom (u-A⇒B A B) σ j M)) i
  
  N-ob (Gl-q (A ⇒TwGl B)) Γ (α , p) = N-ob (q-A⇒B A B) Γ α
  N-hom (Gl-q (A ⇒TwGl B)) σ i (α , p) = N-hom (q-A⇒B A B) σ i α
  
  Gl-comp (A ⇒TwGl B) = makeNatTransPath (λ i → N-ob (comp-A⇒B A B i))

  ΛTwGl-nat-ob : {Γ : Glueings} {A B : Glueing} → (t : GlTm (Γ ⊹ A) B) →
    N-ob ((ιNF (A-A⇒B A B) 𝒩∘ q-A⇒B A B) 𝒩∘ C-Λ _ _ _ (GlTm-⦇α⦈ t))
    ≡ N-ob (TMよ (Λ (GlTm-α t)) P.⟦ ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ ⟧)
  ΛTwGl-nat-ob {Γ} {A} {B} t i Δ 𝓈 =
    (Λ (N-ob (ιNF 𝐵 𝒩∘ Gl-q B 𝒩∘ GlTm-⦇α⦈ t) (Δ ⊹ 𝐴)
      (F-hom (⇓PShCtx (Gls-⦇Γ⦈ Γ)) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ)) 𝓈 , N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣)))
      ≡⟨ (λ j → Λ (N-ob (GlTm-nat t j) (Δ ⊹ 𝐴)
        (F-hom (⇓PShCtx (Gls-⦇Γ⦈ Γ)) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ)) 𝓈 , N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣)))) ⟩
    Λ (GlTm-α t ⟦ ⇓TMS (N-ob (⇓PShTms (ιNFS (Gls-Γ (Γ ⊹ A)) P.⊚ Gls-q (Γ ⊹ A))) (Δ ⊹ 𝐴)
      (F-hom (⇓PShCtx (Gls-⦇Γ⦈ Γ)) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ)) 𝓈 , N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣))) ⟧)
      ≡⟨ (λ j → Λ (GlTm-α t ⟦ ⇓TMS (IndLem Γ A (Δ ⊹ 𝐴)
        (F-hom (⇓PShCtx (Gls-⦇Γ⦈ Γ)) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ)) 𝓈)
        (N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣)) j) ⟧)) ⟩
    Λ (GlTm-α t ⟦ ⇓TMS (N-ob (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ)) (Δ ⊹ 𝐴)
      (F-hom (⇓PShCtx (Gls-⦇Γ⦈ Γ)) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ)) 𝓈))
      ⊕ N-ob (ιNF 𝐴 𝒩∘ Gl-q A 𝒩∘ Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣)⟧)
      ≡⟨ (λ j → Λ (GlTm-α t ⟦ ⇓TMS (N-hom (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ))
        (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ)) j 𝓈) ⊕ N-ob (Gl-comp A j) (Δ ⊹ 𝐴) (VN 𝑧𝑣) ⟧)) ⟩
    Λ (GlTm-α t ⟦ ⇓TMS (F-hom (⇓PShCtx (TMS (Gls-Γ Γ))) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ))
      (N-ob (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ)) Δ 𝓈)) ⊕ 𝑧 ⟧)
      ≡⟨ (λ j → Λ (GlTm-α t ⟦ ⇓TMSHom (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ))
        (N-ob (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ)) Δ 𝓈) j ⊕ 𝑧 ⟧)) ⟩
    Λ (GlTm-α t ⟦ (⇓TMS (N-ob (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ)) Δ 𝓈)
      ⊚ makeRen (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ))) ⊕ 𝑧 ⟧)
      ≡⟨ (λ j → Λ (GlTm-α t ⟦ (⇓TMS (N-ob (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ)) Δ 𝓈)
        ⊚ πη j) ⊕ 𝑧 ⟧)) ⟩
    Λ (GlTm-α t ⟦ W₂tms 𝐴 (⇓TMS (N-ob (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ)) Δ 𝓈)) ⟧)
      ≡⟨ Λnat (GlTm-α t) (⇓TMS (N-ob (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ)) Δ 𝓈)) ⁻¹ ⟩
    N-ob (TMよ (Λ (GlTm-α t)) P.⟦ ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ ⟧) Δ 𝓈
      ∎) i where
        𝐴 = Gl-A A
        𝐵 = Gl-A B

  ΛTwGl : {Γ : Glueings} {A B : Glueing} → GlTm (Γ ⊹ A) B → GlTm Γ (A ⇒TwGl B)
  N-ob (GlTm-⦇α⦈ (ΛTwGl {Γ} {A} {B} t)) Δ 𝓈 = N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t)) Δ 𝓈 ,
    λ Σ σ x →
      N-ob (ιNF 𝐵 𝒩∘ Gl-q B 𝒩∘ GlTm-⦇α⦈ t) Σ (F-hom (⇓PShCtx (Gls-⦇Γ⦈ Γ)) σ 𝓈 , x)
        ≡⟨ (λ i → N-ob (GlTm-nat t i) Σ (F-hom (⇓PShCtx (Gls-⦇Γ⦈ Γ)) σ 𝓈 , x)) ⟩
      GlTm-α t ⟦ ⇓TMS (N-ob (⇓PShTms (ιNFS (Gls-Γ (Γ ⊹ A)) P.⊚ Gls-q (Γ ⊹ A)))
        Σ (F-hom (⇓PShCtx (Gls-⦇Γ⦈ Γ)) σ 𝓈 , x)) ⟧
        ≡⟨ (λ i → GlTm-α t ⟦ ⇓TMS (IndLem Γ A Σ (F-hom (⇓PShCtx (Gls-⦇Γ⦈ Γ)) σ 𝓈) x i) ⟧) ⟩
      GlTm-α t ⟦ ⇓TMS (N-ob (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ))
        Σ (F-hom (⇓PShCtx (Gls-⦇Γ⦈ Γ)) σ 𝓈)) ⊕ ιNf (N-ob (Gl-q A) Σ x) ⟧
        ≡⟨ (λ i → GlTm-α t ⟦ ⇓TMS (N-hom (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ)) σ i 𝓈)
          ⊕ ιNf (N-ob (Gl-q A) Σ x) ⟧) ⟩
      GlTm-α t ⟦ ⇓TMS (F-hom (⇓PShCtx (TMS (Gls-Γ Γ))) σ
        (N-ob (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ)) Δ 𝓈)) ⊕ ιNf (N-ob (Gl-q A) Σ x) ⟧
        ≡⟨ (λ i → GlTm-α t ⟦ ⇓TMSHom σ (N-ob (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ)) Δ 𝓈) i
          ⊕ ιNf (N-ob (Gl-q A) Σ x) ⟧) ⟩
      GlTm-α t ⟦ ⇓TMS (N-ob (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ)) Δ 𝓈) ⊚ makeRen σ
        ⊕ ιNf (N-ob (Gl-q A) Σ x) ⟧
        ≡⟨ lem (GlTm-α t) (⇓TMS (N-ob (⇓PShTms (ιNFS 𝐺 P.⊚ Gls-q Γ)) Δ 𝓈) ⊚ (makeRen σ))
          (ιNf (N-ob (Gl-q A) Σ x)) ⁻¹ ⟩
      GlTm-α t ⟦ W₂tms 𝐴 (⇓TMS (N-ob (⇓PShTms (ιNFS 𝐺 P.⊚ Gls-q Γ)) Δ 𝓈) ⊚ (makeRen σ)) ⟧
        ⟦ 𝒾𝒹 Σ ⊕ ιNf (N-ob (Gl-q A) Σ x) ⟧
        ≡⟨ 𝑎𝑝𝑝β (GlTm-α t ⟦ W₂tms 𝐴 (⇓TMS (N-ob (⇓PShTms (ιNFS 𝐺 P.⊚ Gls-q Γ)) Δ 𝓈)
          ⊚ (makeRen σ)) ⟧) (ιNf (N-ob (Gl-q A) Σ x)) ⁻¹ ⟩
      𝑎𝑝𝑝 (Λ (GlTm-α t ⟦ W₂tms 𝐴 (⇓TMS (N-ob (⇓PShTms (ιNFS 𝐺 P.⊚ Gls-q Γ)) Δ 𝓈) ⊚ (makeRen σ)) ⟧))
        (ιNf (N-ob (Gl-q A) Σ x))
        ≡⟨ (λ i → 𝑎𝑝𝑝 (Λnat (GlTm-α t) (⇓TMS (N-ob (⇓PShTms (ιNFS 𝐺 P.⊚ Gls-q Γ)) Δ 𝓈)
          ⊚ (makeRen σ)) (~ i)) (ιNf (N-ob (Gl-q A) Σ x))) ⟩
      𝑎𝑝𝑝 (Λ (GlTm-α t) ⟦ ⇓TMS (N-ob (⇓PShTms (ιNFS 𝐺 P.⊚ Gls-q Γ)) Δ 𝓈) ⊚ (makeRen σ) ⟧)
        (ιNf (N-ob (Gl-q A) Σ x))
        ≡⟨ (λ i → 𝑎𝑝𝑝 (⟦⟧⟦⟧ (Λ (GlTm-α t)) (⇓TMS (N-ob (⇓PShTms (ιNFS 𝐺 P.⊚ Gls-q Γ)) Δ 𝓈))
          (makeRen σ) (~ i)) (ιNf (N-ob (Gl-q A) Σ x))) ⟩
      𝑎𝑝𝑝 (Λ (GlTm-α t) ⟦ ⇓TMS (N-ob (⇓PShTms (ιNFS 𝐺 P.⊚ Gls-q Γ)) Δ 𝓈) ⟧ ⟦ makeRen σ ⟧)
        (ιNf (N-ob (Gl-q A) Σ x))
        ≡⟨ (λ i → 𝑎𝑝𝑝 (ΛTwGl-nat-ob t (~ i) Δ 𝓈 ⟦ makeRen σ ⟧) (ιNf (N-ob (Gl-q A) Σ x))) ⟩
      𝑎𝑝𝑝 (N-ob ((ιNF (A-A⇒B A B) 𝒩∘ q-A⇒B A B) 𝒩∘ C-Λ _ _ _ (GlTm-⦇α⦈ t)) Δ 𝓈 ⟦ makeRen σ ⟧)
        (ιNf (N-ob (Gl-q A) Σ x))
        ≡⟨ (λ i → 𝑎𝑝𝑝 (N-hom (ιNF (A-A⇒B A B)) σ (~ i) (N-ob (q-A⇒B A B 𝒩∘ C-Λ _ _ _ (GlTm-⦇α⦈ t))
          Δ 𝓈)) (ιNf (N-ob (Gl-q A) Σ x))) ⟩
      𝑎𝑝𝑝 (ιNf (N-ob (q-A⇒B A B 𝒩∘ C-Λ _ _ _ (GlTm-⦇α⦈ t)) Δ 𝓈 [ σ ]NF))
        (ιNf (N-ob (Gl-q A) Σ x))
        ∎ where
        𝐴 = Gl-A A
        𝐵 = Gl-A B
        𝐺 = Gls-Γ Γ
        lem : {Γ Δ : ctx} {A B : ty} (t : tm (Δ ⊹ A) B) (σ : tms Γ Δ) (s : tm Γ A) →
          t ⟦ W₂tms A σ ⟧ ⟦ 𝒾𝒹 Γ ⊕ s ⟧ ≡ t ⟦ σ ⊕ s ⟧
        lem {Γ} {Δ} {A} t σ s =
          t ⟦ W₂tms A σ ⟧ ⟦ 𝒾𝒹 Γ ⊕ s ⟧
            ≡⟨ ⟦⟧⟦⟧ t (W₂tms A σ) (𝒾𝒹 Γ ⊕ s) ⟩
          t ⟦ W₁tms A σ ⊚ (𝒾𝒹 Γ ⊕ s) ⊕ 𝑧 ⟦ 𝒾𝒹 Γ ⊕ s ⟧ ⟧
            ≡⟨ (λ i → t ⟦ W₁lem2 σ (𝒾𝒹 Γ) s i ⊕ 𝑧β (𝒾𝒹 Γ ⊕ s) i ⟧) ⟩
          t ⟦ σ ⊚ 𝒾𝒹 Γ ⊕ s ⟧
            ≡⟨ (λ i → t ⟦ 𝒾𝒹R σ i ⊕ s ⟧)⟩
          t ⟦ σ ⊕ s ⟧
            ∎
  N-hom (GlTm-⦇α⦈ (ΛTwGl {Γ} {A} {B} t)) {Δ} {Σ} σ i α =
    (subtypeLem (⦇A⇒B⦈-ob A B Σ)
      (N-ob (GlTm-⦇α⦈ (ΛTwGl t)) Σ (F-hom (⇓PShCtx (Gls-⦇Γ⦈ Γ)) σ α))
      (F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) σ (N-ob (GlTm-⦇α⦈ (ΛTwGl t)) Δ α))
      (λ j → N-hom (C-Λ _ _ _ (GlTm-⦇α⦈ t)) σ j α)) i
  GlTm-α (ΛTwGl t) = Λ (GlTm-α t)
  GlTm-nat (ΛTwGl {Γ} {A} {B} t) = makeNatTransPath (ΛTwGl-nat-ob t)

  GlTm-⦇α⦈forget : {Γ : Glueings} {A B : Glueing} → GlTm Γ (A ⇒TwGl B) →
    P.tm (Gls-⦇Γ⦈ Γ) (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B))
  N-ob (GlTm-⦇α⦈forget t) Γ 𝓈 = fst (N-ob (GlTm-⦇α⦈ t) Γ 𝓈)
  N-hom (GlTm-⦇α⦈forget t) σ i 𝓈 = fst (N-hom (GlTm-⦇α⦈ t) σ i 𝓈)

  AppTwGl-nat-ob : {Γ : Glueings} {A B : Glueing} (t : GlTm Γ (A ⇒TwGl B)) (s : GlTm Γ A) →
    N-ob ((ιNF (Gl-A B) 𝒩∘ Gl-q B) 𝒩∘ C-App _ _ _ (GlTm-⦇α⦈forget t) (GlTm-⦇α⦈ s))
    ≡ N-ob (TMよ (𝑎𝑝𝑝 (GlTm-α t) (GlTm-α s)) P.⟦ ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ ⟧)
  AppTwGl-nat-ob {Γ} {A} {B} t s i Δ 𝓈 =
    (ιNf (N-ob (Gl-q B) Δ (N-ob (fst (N-ob (GlTm-⦇α⦈ t) Δ 𝓈)) Δ
      (id𝑅𝑒𝑛 Δ , N-ob (GlTm-⦇α⦈ s) Δ 𝓈)))
      ≡⟨ snd ((N-ob (GlTm-⦇α⦈ t)) Δ 𝓈) Δ (id𝑅𝑒𝑛 Δ) (N-ob (GlTm-⦇α⦈ s) Δ 𝓈) ⟩
    𝑎𝑝𝑝 (ιNf (N-ob (Gl-q (A ⇒TwGl B)) Δ (N-ob (GlTm-⦇α⦈ t) Δ 𝓈) [ id𝑅𝑒𝑛 Δ ]NF))
      (ιNf (N-ob (Gl-q A) Δ (N-ob (GlTm-⦇α⦈ s) Δ 𝓈)))
      ≡⟨ (λ j → 𝑎𝑝𝑝 (ιNf ([id]NF (N-ob (Gl-q (A ⇒TwGl B)) Δ (N-ob (GlTm-⦇α⦈ t) Δ 𝓈)) j))
        (ιNf (N-ob (Gl-q A) Δ (N-ob (GlTm-⦇α⦈ s) Δ 𝓈)))) ⟩
    𝑎𝑝𝑝 (ιNf (N-ob (Gl-q (A ⇒TwGl B)) Δ (N-ob (GlTm-⦇α⦈ t) Δ 𝓈)))
      (ιNf (N-ob (Gl-q A) Δ (N-ob (GlTm-⦇α⦈ s) Δ 𝓈)))
      ≡⟨ (λ j → 𝑎𝑝𝑝 (N-ob (GlTm-nat t j) Δ 𝓈) (N-ob (GlTm-nat s j) Δ 𝓈)) ⟩
    𝑎𝑝𝑝 (GlTm-α t ⟦ ⇓TMS (N-ob (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ)) Δ 𝓈) ⟧)
        (GlTm-α s ⟦ ⇓TMS (N-ob (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ)) Δ 𝓈) ⟧)
      ≡⟨ 𝑎𝑝𝑝⟦⟧ (GlTm-α t) (GlTm-α s) (⇓TMS (N-ob (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ)) Δ 𝓈)) ⁻¹ ⟩
    𝑎𝑝𝑝 (GlTm-α t) (GlTm-α s) ⟦ ⇓TMS (N-ob (⇓PShTms (ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ)) Δ 𝓈) ⟧
      ∎) i

  AppTwGl : {Γ : Glueings} {A B : Glueing} → GlTm Γ (A ⇒TwGl B) → GlTm Γ A → GlTm Γ B
  GlTm-⦇α⦈ (AppTwGl t s) = C-App _ _ _ (GlTm-⦇α⦈forget t) (GlTm-⦇α⦈ s)
  GlTm-α (AppTwGl t s) = 𝑎𝑝𝑝 (GlTm-α t) (GlTm-α s)
  GlTm-nat (AppTwGl t s) = makeNatTransPath (AppTwGl-nat-ob t s)

  -- This finishes up the basic cartesian closed structure of TwGl
  -- We now verify that the required coherence laws hold

  ≡GlTm : {Γ : Glueings} {A : Glueing} {t s : GlTm Γ A} →
    N-ob (GlTm-⦇α⦈ t) ≡ N-ob (GlTm-⦇α⦈ s) → GlTm-α t ≡ GlTm-α s → t ≡ s
  GlTm-⦇α⦈ (≡GlTm {t = t} {s} p q i) = makeNatTransPath {α = GlTm-⦇α⦈ t} {β = GlTm-⦇α⦈ s} p i
  GlTm-α (≡GlTm {t = t} {s} p q i) = q i
  GlTm-nat (≡GlTm {Γ} {A} {t} {s} p q i) j =
    isSet→SquareP (λ i j → isSetNat)
      (GlTm-nat t)
      (GlTm-nat s)
      (λ k → (ιNF (Gl-A A) 𝒩∘ Gl-q A) 𝒩∘ (GlTm-⦇α⦈ (≡GlTm {t = t} {s} p q k)))
      (λ k → TMよ (GlTm-α (≡GlTm {t = t} {s} p q k)) P.⟦ ιNFS (Gls-Γ Γ) P.⊚ Gls-q Γ ⟧) i j

  ≡GlTm⇒ : {Γ : Glueings} {A B : Glueing} {t s : GlTm Γ (A ⇒TwGl B)} →
    ((Δ : ctx) → (𝓈 : fst (F-ob (⇓PShCtx (Gls-⦇Γ⦈ Γ)) Δ))
      → fst (N-ob (GlTm-⦇α⦈ t) Δ 𝓈) ≡ fst (N-ob (GlTm-⦇α⦈ s) Δ 𝓈)) →
    GlTm-α t ≡ GlTm-α s → t ≡ s
  ≡GlTm⇒ {Γ} {A} {B} {t} {s} p q =
    ≡GlTm
      (λ i Δ 𝓈 →
        (subtypeLem (⦇A⇒B⦈-ob A B Δ)
          (N-ob (GlTm-⦇α⦈ t) Δ 𝓈)
          (N-ob (GlTm-⦇α⦈ s) Δ 𝓈)
          (p Δ 𝓈)) i) q

  𝑧TwGl-⦇α⦈ : {Γ : Glueings} {A : Glueing} → GlTm-⦇α⦈ (T.𝑧 {Γ} {A}) ≡ P.𝑧 {Gls-⦇Γ⦈ Γ}
  𝑧TwGl-⦇α⦈ {Γ} {A} = ap 𝑧𝑇𝑚𝑠 (idTwGl-⦇αs⦈ {Γ ⊹ A})

  πTwGl-⦇αs⦈ : {Γ : Glueings} {A : Glueing} → GlTms-⦇αs⦈ (T.π {Γ} {A}) ≡ P.π
  πTwGl-⦇αs⦈ {Γ} {A} = ap π𝑇𝑚𝑠 (idTwGl-⦇αs⦈ {Γ ⊹ A})

  ΛTwGl-nat-⦇α⦈-ob : {Γ Δ : Glueings} {A B : Glueing} (t : GlTm (Δ ⊹ A) B) (σ : GlTms Γ Δ)
    (Σ : ctx) (𝓈 : fst (F-ob (⇓PShCtx (Gls-⦇Γ⦈ Γ)) Σ)) →
    fst (N-ob (GlTm-⦇α⦈ (ΛTwGl t T.⟦ σ ⟧)) Σ 𝓈)
    ≡ fst (N-ob (GlTm-⦇α⦈ (ΛTwGl (t T.⟦ σ T.⊚ T.π ⊕ T.𝑧 ⟧))) Σ 𝓈)
  ΛTwGl-nat-⦇α⦈-ob {Γ} {Δ} {A} {B} t σ Σ 𝓈 =
    {!fst (N-ob (GlTm-⦇α⦈ (ΛTwGl t T.⟦ σ ⟧)) Σ 𝓈)
      ≡⟨ refl ⟩
    N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t)) Σ (N-ob (⇓PShTms (GlTms-⦇αs⦈ σ)) Σ 𝓈)
      ≡⟨ (λ i → N-ob (C-Λnat _ _ _ _ (⇓PShTms (GlTms-⦇αs⦈ σ)) (GlTm-⦇α⦈ t) (~ i)) Σ 𝓈) ⟩
    N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t 𝒩∘ (C-pair (⇓PShTms (GlTms-⦇αs⦈ σ) 𝒩∘ C-π₁ _ _) P.𝑧))) Σ 𝓈
      ≡⟨ (λ i → N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t 𝒩∘
        (C-pair (⇓PShTms (GlTms-⦇αs⦈ σ) 𝒩∘ ⇓PShπ {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A} (~ i)) P.𝑧))) Σ 𝓈) ⟩
    N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t 𝒩∘
      (C-pair (⇓PShTms (GlTms-⦇αs⦈ σ) 𝒩∘ ⇓PShTms (P.π {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A})) P.𝑧))) Σ 𝓈
      ≡⟨ (λ i → N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t 𝒩∘
        (C-pair (⇓PSh∘ (GlTms-⦇αs⦈ σ) (P.π {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A}) (~ i)) P.𝑧))) Σ 𝓈) ⟩
    N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t P.⟦ GlTms-⦇αs⦈ σ P.⊚ P.π {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A}
      ⊕ P.𝑧 {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A} ⟧)) Σ 𝓈
      ≡⟨ (λ i → N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t P.⟦ GlTms-⦇αs⦈ σ P.⊚ πTwGl-⦇αs⦈ {Γ} {A} (~ i)
        ⊕ 𝑧TwGl-⦇α⦈ {Γ} {A} (~ i) ⟧))  Σ 𝓈) ⟩
    N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t P.⟦ GlTms-⦇αs⦈ σ P.⊚ GlTms-⦇αs⦈ (T.π {Γ} {A})
      ⊕ GlTm-⦇α⦈ (T.𝑧 {Γ} {A}) ⟧)) Σ 𝓈
      ≡⟨ (λ i → N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t P.⟦ Gl-⦇αs⦈∘ σ (T.π {Γ} {A}) (~ i)
        ⊕ GlTm-⦇α⦈ (T.𝑧 {Γ} {A}) ⟧)) Σ 𝓈) ⟩
    N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ (t T.⟦ σ T.⊚ T.π {Γ} {A} ⊕ (T.𝑧 {Γ} {A}) ⟧))) Σ 𝓈
      ≡⟨ refl ⟩
    fst (N-ob (GlTm-⦇α⦈ (ΛTwGl (t T.⟦ σ T.⊚ T.π ⊕ T.𝑧 ⟧))) Σ 𝓈)
      ∎!}

  𝑧TwGl-α : {Γ : Glueings} {A : Glueing} → GlTm-α (T.𝑧 {Γ} {A}) ≡ 𝑧
  𝑧TwGl-α {Γ} {A} = ap 𝑧𝑇𝑚𝑠 (idTwGl-αs {Γ ⊹ A})

  πTwGl-αs : {Γ : Glueings} {A : Glueing} → GlTms-αs (T.π {Γ} {A}) ≡ π
  πTwGl-αs {Γ} {A} = ap π𝑇𝑚𝑠 (idTwGl-αs {Γ ⊹ A})

  ΛTwGl-nat : {Γ Δ : Glueings} {A B : Glueing} (t : GlTm (Δ ⊹ A) B) (σ : GlTms Γ Δ) →
    ΛTwGl t [ σ ]Gl ≡ ΛTwGl (t T.⟦ σ T.⊚ T.π ⊕ T.𝑧 ⟧)
  ΛTwGl-nat {Γ} {Δ} {A} {B} t σ =
    ≡GlTm⇒
      (ΛTwGl-nat-⦇α⦈-ob t σ)
      (Λ (GlTm-α t) ⟦ GlTms-αs σ ⟧
        ≡⟨ Λnat (GlTm-α t) (GlTms-αs σ) ⟩
      Λ (GlTm-α t ⟦ W₂tms (Gl-A A) (GlTms-αs σ) ⟧)
        ≡⟨ (λ i → Λ (GlTm-α t ⟦ GlTms-αs σ ⊚ πTwGl-αs {Γ} {A} (~ i)
          ⊕ 𝑧TwGl-α {Γ} {A} (~ i) ⟧)) ⟩
      Λ (GlTm-α t ⟦ GlTms-αs σ ⊚ GlTms-αs (T.π {Γ} {A}) ⊕ GlTm-α (T.𝑧 {Γ} {A}) ⟧)
        ≡⟨ (λ i → Λ (GlTm-α t ⟦ Gl-αs∘ σ (T.π {Γ} {A}) (~ i) ⊕ GlTm-α (T.𝑧 {Γ} {A}) ⟧)) ⟩
      Λ (GlTm-α t ⟦ GlTms-αs (σ T.⊚ (T.π {Γ} {A})) ⊕ GlTm-α (T.𝑧 {Γ} {A}) ⟧)
        ∎)

{-  open Glueing
  open Functor
  open Contextual (𝒫𝒮𝒽 REN) 
  open Cartesian (PShCart {𝒞 = REN})
  open Precategory (PSh REN) hiding (_∘_)
  open NatTrans
  module R = Contextual ρεν
  module G = Contextual TwGl

  A-A⇒B : (A B : Glueing) → Ty
  A-A⇒B A B = Gl-A A ren.⇒ Gl-A B

  q-A⇒B : (A B : Glueing) →
    Hom[ C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B) , NF (A-A⇒B A B) ]
  N-ob (q-A⇒B A B) Γ α =
    LAM (N-ob (Gl-q B) (Γ ⊹ 𝐴) (N-ob α (Γ ⊹ 𝐴)
      (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Γ) , N-ob (Gl-u A) (Γ ⊹ 𝐴) (VN 𝑧𝑣)))) where
        𝐴 = (Gl-A A)
  N-hom (q-A⇒B A B) {Δ} {Σ} σ i α =
    (LAM (N-ob (Gl-q B) (Σ ⊹ 𝐴) (N-ob α (Σ ⊹ 𝐴)
      (σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Σ) , N-ob (Gl-u A) (Σ ⊹ 𝐴) (VN 𝑧𝑣))))
      ≡⟨ (λ j → LAM (N-ob (Gl-q B) (Σ ⊹ 𝐴) (N-ob α (Σ ⊹ 𝐴)
        (lem j , N-hom (Gl-u A) (W₂𝑅𝑒𝑛 𝐴 σ) j (VN 𝑧𝑣))))) ⟩
    LAM (N-ob (Gl-q B) (Σ ⊹ 𝐴) (N-ob α (Σ ⊹ 𝐴) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ) ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 𝐴 σ ,
      (F-hom (Gl-⦇A⦈ A) (W₂𝑅𝑒𝑛 𝐴 σ) (N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣))))))
      ≡⟨ (λ j → LAM (N-ob (Gl-q B) (Σ ⊹ 𝐴) (N-hom α (W₂𝑅𝑒𝑛 𝐴 σ) j
        (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ) , N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣))))) ⟩
    LAM (N-ob (Gl-q B) (Σ ⊹ 𝐴) (F-hom (Gl-⦇A⦈ B) (W₂𝑅𝑒𝑛 𝐴 σ)
      (N-ob α (Δ ⊹ 𝐴) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ) , N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣)))))
      ≡⟨ (λ j → LAM (N-hom (Gl-q B) (W₂𝑅𝑒𝑛 𝐴 σ) j
        (N-ob α (Δ ⊹ 𝐴) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ) , N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣))))) ⟩
    LAM (N-ob (Gl-q B) (Δ ⊹ 𝐴)
      (N-ob α (Δ ⊹ 𝐴) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ) , N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣))) [ W₂𝑅𝑒𝑛 𝐴 σ ]NF)
      ∎) i where
      𝐴 = (Gl-A A)
      lem : σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Σ) ≡ W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ) ∘𝑅𝑒𝑛 (W₂𝑅𝑒𝑛 𝐴 σ)
      lem =
        σ ∘𝑅𝑒𝑛 W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Σ)
          ≡⟨ Wlem3𝑅𝑒𝑛 σ (id𝑅𝑒𝑛 Σ) ⟩
        W₁𝑅𝑒𝑛 𝐴 (σ ∘𝑅𝑒𝑛 id𝑅𝑒𝑛 Σ)
          ≡⟨ ap (W₁𝑅𝑒𝑛 𝐴) (R.𝒾𝒹R σ) ⟩
        W₁𝑅𝑒𝑛 𝐴 σ
          ≡⟨ ap (W₁𝑅𝑒𝑛 𝐴) (∘𝑅𝑒𝑛IdL σ ⁻¹) ⟩
        W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ ∘𝑅𝑒𝑛 σ)
          ≡⟨ Wlem5𝑅𝑒𝑛 (id𝑅𝑒𝑛 Δ) σ ⁻¹ ⟩
        W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ) ∘𝑅𝑒𝑛 W₂𝑅𝑒𝑛 𝐴 σ
          ∎

  u-A⇒B : (A B : Glueing) →
    Hom[ NE (A-A⇒B A B) , C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B) ]
  N-ob (N-ob (u-A⇒B A B) Γ M) Δ (σ , 𝓈) =
    N-ob (Gl-u B) Δ (APP (M [ σ ]NE) (N-ob (Gl-q A) Δ 𝓈))
  N-hom (N-ob (u-A⇒B A B) Γ M) {Δ} {Σ} σ i (τ , 𝓈) =
    (N-ob (Gl-u B) Σ (APP (M [ τ ∘𝑅𝑒𝑛 σ ]NE) (N-ob (Gl-q A) Σ (F-hom (Gl-⦇A⦈ A) σ 𝓈)))
      ≡⟨ (λ j → N-ob (Gl-u B) Σ (APP ([][]NE M τ σ (~ j)) (N-hom (Gl-q A) σ j 𝓈))) ⟩
    N-ob (Gl-u B) Σ (APP (M [ τ ]NE) (N-ob (Gl-q A) Δ 𝓈) [ σ ]NE)
      ≡⟨ (λ j → N-hom (Gl-u B) σ j (APP (M [ τ ]NE) (N-ob (Gl-q A) Δ 𝓈))) ⟩
    F-hom (Gl-⦇A⦈ B) σ (N-ob (Gl-u B) Δ (APP (M [ τ ]NE) (N-ob (Gl-q A) Δ 𝓈)))
      ∎) i
  N-ob (N-hom (u-A⇒B A B) σ i M) Γ (τ , 𝓈) =
    N-ob (Gl-u B) Γ (APP ([][]NE M σ τ i) (N-ob (Gl-q A) Γ 𝓈))
  N-hom (N-hom (u-A⇒B A B) {Σ} {Ω} σ i M) {Γ} {Δ} τ j (μ , 𝓈) =
    isSet→SquareP (λ i j → snd (F-ob (Gl-⦇A⦈ B) Δ))
      (λ k → N-hom (N-ob (u-A⇒B A B) Ω (M [ σ ]NE)) τ k (μ , 𝓈))
      (λ k → N-hom (F-hom (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B)) σ (N-ob (u-A⇒B A B) Σ M)) τ k (μ , 𝓈))
      (λ k → N-ob (N-hom (u-A⇒B A B) σ k M) Δ (μ ∘𝑅𝑒𝑛 τ , F-hom (Gl-⦇A⦈ A) τ 𝓈))
      (λ k → F-hom (Gl-⦇A⦈ B) τ (N-ob (N-hom (u-A⇒B A B) σ k M) Γ (μ , 𝓈))) i j

  private
    comp-A⇒B-ob : (A B : Glueing) →
      N-ob (ιNF (A-A⇒B A B) 𝒩∘ (q-A⇒B A B) 𝒩∘ (u-A⇒B A B)) ≡ N-ob (ιNE (A-A⇒B A B))
    comp-A⇒B-ob A B i Γ M =
      (Lam (ιNf (N-ob (Gl-q B) (Γ ⊹ 𝐴) (N-ob (Gl-u B) (Γ ⊹ 𝐴)
        (APP (M [ W₁𝑅𝑒𝑛 (Gl-A A) (id𝑅𝑒𝑛 Γ) ]NE)
             (N-ob (Gl-q A) (Γ ⊹ 𝐴) (N-ob (Gl-u A) (Γ ⊹ 𝐴) (VN 𝑧𝑣)))))))
        ≡⟨ (λ j → Lam (N-ob (Gl-comp B j) (Γ ⊹ 𝐴)
          (APP (M [ W₁𝑅𝑒𝑛 (Gl-A A) (id𝑅𝑒𝑛 Γ) ]NE)
             (N-ob (Gl-q A) (Γ ⊹ 𝐴) (N-ob (Gl-u A) (Γ ⊹ 𝐴) (VN 𝑧𝑣)))))) ⟩
      Lam (App (ιNe (M [ map𝑇𝑚𝑠 𝑠𝑣 (id𝑅𝑒𝑛 Γ) ]NE))
        (ιNf (N-ob (Gl-q A) (Γ ⊹ Gl-A A) (N-ob (Gl-u A) (Γ ⊹ Gl-A A) (VN 𝑧𝑣)))))
        ≡⟨ (λ j → Lam (App (ιNe (M [ map𝑇𝑚𝑠 𝑠𝑣 (id𝑅𝑒𝑛 Γ) ]NE))
          (N-ob (Gl-comp A j) (Γ ⊹ 𝐴) (VN 𝑧𝑣)))) ⟩
      Lam (App (ιNe (M [ W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Γ) ]NE)) (V 𝑧𝑣))
        ≡⟨ (λ j → Lam (App (ιNeLem M (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Γ)) j) (V 𝑧𝑣))) ⟩
      Lam (App (ιNe M [ varify (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Γ)) ]) (V 𝑧𝑣))
        ≡⟨ (λ j → Lam (App (ιNe M [ Vlem2 (id𝑅𝑒𝑛 Γ) j ]) (V 𝑧𝑣))) ⟩
      Lam (App (ιNe M [ W₁Tms 𝐴 (varify (id𝑅𝑒𝑛 Γ)) ]) (V 𝑧𝑣))
        ≡⟨ η (ιNe M) ⁻¹ ⟩
      ιNe M
        ∎) i where
        𝐴 = (Gl-A A)

  comp-A⇒B : (A B : Glueing) →
    ιNF (A-A⇒B A B) 𝒩∘ (q-A⇒B A B) 𝒩∘ (u-A⇒B A B) ≡ ιNE (A-A⇒B A B)
  comp-A⇒B A B = makeNatTransPath (comp-A⇒B-ob A B)

  record Subset {ℓ₁ ℓ₂ : Level} : Type (lsuc (ℓ₁ ⊔ ℓ₂))  where
    field
      Sub-A : Type ℓ₁
      Sub-q : isSet Sub-A
      Sub-B : Sub-A → Type ℓ₂
      Sub-p : (x : Sub-A) → (isProp (Sub-B x))
      
    type = Σ Sub-A Sub-B

    isSetType : isSet type
    isSetType = isSetΣ Sub-q (λ x → isProp→isSet (Sub-p x))
    
    subtypeLem : (x y : type) → fst x ≡ fst y → x ≡ y
    subtypeLem x y a i = a i , isOfHLevel→isOfHLevelDep 1 (λ z → Sub-p z) (snd x) (snd y) a i

  open Subset

  ⦇A⇒B⦈-ob : (A B : Glueing) (Γ : Ctx) → Subset
  Sub-A (⦇A⇒B⦈-ob A B Γ) = fst (F-ob (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B)) Γ)
  Sub-q (⦇A⇒B⦈-ob A B Γ) = snd (F-ob (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B)) Γ)
  Sub-B (⦇A⇒B⦈-ob A B Γ) α = (Δ : Ctx) (σ : 𝑅𝑒𝑛 Δ Γ) (x : fst (F-ob (Gl-⦇A⦈ A) Δ)) →
    ιNf (N-ob (Gl-q B) Δ (N-ob α Δ (σ , x)))
      ≡ App (ιNf (N-ob (q-A⇒B A B) Γ α [ σ ]NF)) (ιNf (N-ob (Gl-q A) Δ x))
  Sub-p (⦇A⇒B⦈-ob A B Γ) α = isPropΠ3 λ Δ σ y → trunc _ _
  
  _⇒TwGl_ : Glueing → Glueing → Glueing
  Gl-A (A ⇒TwGl B) = A-A⇒B A B
  
  F-ob (Gl-⦇A⦈ (A ⇒TwGl B)) Γ = type (⦇A⇒B⦈-ob A B Γ) , isSetType (⦇A⇒B⦈-ob A B Γ)
  F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) {Γ} {Δ} σ (α , p) =
    F-hom (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B)) σ α ,
      λ Σ τ x →
        ιNf (N-ob (Gl-q B) Σ (N-ob α Σ (σ ∘𝑅𝑒𝑛 τ , x)))
          ≡⟨ p Σ (σ ∘𝑅𝑒𝑛 τ) x ⟩
        App (ιNf (N-ob (q-A⇒B A B) Γ α [ σ ∘𝑅𝑒𝑛 τ ]NF)) (ιNf (N-ob (Gl-q A) Σ x))
          ≡⟨ (λ i → App (ιNf ([][]NF (N-ob (q-A⇒B A B) Γ α) σ τ (~ i)))
            (ιNf (N-ob (Gl-q A) Σ x))) ⟩
        App (ιNf (N-ob (q-A⇒B A B) Γ α [ σ ]NF [ τ ]NF)) (ιNf (N-ob (Gl-q A) Σ x))
          ≡⟨ (λ i → App (ιNf (N-hom (q-A⇒B A B) σ (~ i) α [ τ ]NF))
            (ιNf (N-ob (Gl-q A) Σ x))) ⟩
        App (ιNf (N-ob (q-A⇒B A B) Δ (F-hom (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B)) σ α) [ τ ]NF))
          (ιNf (N-ob (Gl-q A) Σ x))
          ∎
  F-id (Gl-⦇A⦈ (A ⇒TwGl B)) {Γ} i (α , p) =
    (subtypeLem (⦇A⇒B⦈-ob A B Γ)
      (F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) (id𝑅𝑒𝑛 Γ) (α , p)) (α , p)
      (λ j → F-id (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B)) j α)) i
  F-seq (Gl-⦇A⦈ (A ⇒TwGl B)) {Γ} {Δ} {Σ} σ τ i (α , p) =
    (subtypeLem (⦇A⇒B⦈-ob A B Σ)
      (F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) (σ ∘𝑅𝑒𝑛 τ) (α , p))
      (F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) τ (F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) σ (α , p)))
      (λ j → F-seq (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B)) σ τ j α)) i
  
  N-ob (Gl-u (A ⇒TwGl B)) Γ M = N-ob (u-A⇒B A B) Γ M ,
    λ Δ σ x →
      ιNf (N-ob (Gl-q B) Δ (N-ob (Gl-u B) Δ (APP (M [ σ ]NE) (N-ob (Gl-q A) Δ x))))
        ≡⟨ (λ i → N-ob (Gl-comp B i) Δ (APP (M [ σ ]NE) (N-ob (Gl-q A) Δ x))) ⟩
      App (ιNe (M [ σ ]NE)) (ιNf (N-ob (Gl-q A) Δ x))
        ≡⟨ (λ i → App (ιNeLem M σ i) (ιNf (N-ob (Gl-q A) Δ x))) ⟩
      App (ιNe M [ varify σ ]) (ιNf (N-ob (Gl-q A) Δ x))
        ≡⟨ (λ i → App (N-ob (comp-A⇒B A B (~ i)) Γ M [ varify σ ])
          (ιNf (N-ob (Gl-q A) Δ x))) ⟩
      App (ιNf (N-ob (q-A⇒B A B) Γ (N-ob (u-A⇒B A B) Γ M)) [ varify σ ])
        (ιNf (N-ob (Gl-q A) Δ x))
        ≡⟨ (λ i → App (ιNfLem (N-ob (q-A⇒B A B) Γ (N-ob (u-A⇒B A B) Γ M)) σ (~ i))
          (ιNf (N-ob (Gl-q A) Δ x))) ⟩
       App (ιNf (N-ob (q-A⇒B A B) Γ (N-ob (u-A⇒B A B) Γ M) [ σ ]NF))
         (ιNf (N-ob (Gl-q A) Δ x))
        ∎
  N-hom (Gl-u (A ⇒TwGl B)) {Γ} {Δ} σ i M =
    (subtypeLem (⦇A⇒B⦈-ob A B Δ)
      (N-ob (Gl-u (A ⇒TwGl B)) Δ (F-hom (NE (Gl-A (A ⇒TwGl B))) σ M))
      (F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) σ (N-ob (Gl-u (A ⇒TwGl B)) Γ M))
      (λ j → N-hom (u-A⇒B A B) σ j M)) i
  
  N-ob (Gl-q (A ⇒TwGl B)) Γ (α , p) = N-ob (q-A⇒B A B) Γ α
  N-hom (Gl-q (A ⇒TwGl B)) σ i (α , p) = N-hom (q-A⇒B A B) σ i α
  
  Gl-comp (A ⇒TwGl B) = makeNatTransPath (λ i → N-ob (comp-A⇒B A B i))

  open GlTm
  
  ΛTwGl-nat-ob : {Γ : Glueings} {A B : Glueing} → (t : GlTm (Γ ⊹ A) B) →
    N-ob ((ιNF (A-A⇒B A B) 𝒩∘ q-A⇒B A B) 𝒩∘ (C-Λ _ _ _ (GlTm-⦇α⦈ t)))
    ≡ N-ob (TMよ (Lam (GlTm-α t)) ⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧)
  ΛTwGl-nat-ob {Γ} {A} {B} t i Δ 𝓈 =
    (Lam (ιNf (N-ob (Gl-q B) (Δ ⊹ 𝐴) (N-ob (GlTm-⦇α⦈ t) (Δ ⊹ Gl-A A)
      (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ)) 𝓈 ,
        N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣)))))
      ≡⟨ (λ j → Lam (N-ob (GlTm-nat t j) (Δ ⊹ 𝐴)
        (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ)) 𝓈 ,
          N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣)))) ⟩
    Lam (N-ob (TMよ (GlTm-α t) ⟦ ιNFS (Gls-Γ (Γ ⊹ A)) ⊚ Gls-q (Γ ⊹ A) ⟧)
      (Δ ⊹ Gl-A A) (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) (W₁𝑅𝑒𝑛 (Gl-A A) (id𝑅𝑒𝑛 Δ)) 𝓈 ,
        N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣)))
      ≡⟨ ap Lam (indLem Γ A B (GlTm-α t) (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ)) 𝓈)
        (N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣))) ⟩
    Lam (GlTm-α t [
      ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) (Δ ⊹ 𝐴)
        (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ)) 𝓈))
      ⊕ ιNf (N-ob (Gl-q A) (Δ ⊹ 𝐴) (N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN 𝑧𝑣))) ])
      ≡⟨ (λ j → Lam (GlTm-α t [
        ⇓TMS (N-hom (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ)) j 𝓈)
        ⊕ N-ob (Gl-comp A j) (Δ ⊹ 𝐴) (VN 𝑧𝑣) ])) ⟩
    Lam (GlTm-α t [
      ⇓TMS (F-hom (⇓PSh (TMS (Gls-Γ Γ))) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ))
        (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈))
      ⊕ V 𝑧𝑣 ])
      ≡⟨ (λ j → Lam (GlTm-α t [
        ⇓TMSHom (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈) (W₁𝑅𝑒𝑛 𝐴 (id𝑅𝑒𝑛 Δ)) j
        ⊕ V 𝑧𝑣 ])) ⟩
    Lam (GlTm-α t [ W₂Tms 𝐴 (⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈)) ])
      ≡⟨ Lam[] (GlTm-α t) (⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈)) ⁻¹ ⟩
    N-ob (TMよ (Lam (GlTm-α t)) ⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧) Δ 𝓈
      ∎) i where
        𝐴 = (Gl-A A)

  ΛTwGl : {Γ : Glueings} {A B : Glueing} → GlTm (Γ ⊹ A) B → GlTm Γ (A ⇒TwGl B)
  N-ob (GlTm-⦇α⦈ (ΛTwGl {Γ} {A} {B} t)) Δ 𝓈 = N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t)) Δ 𝓈 ,
    λ Σ σ x →
      (App (ιNf (N-ob (q-A⇒B A B) Δ (N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t)) Δ 𝓈) [ σ ]NF))
        (ιNf (N-ob (Gl-q A) Σ x))
        ≡⟨ (λ i → App (ιNfLem (N-ob (q-A⇒B A B) Δ (N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t)) Δ 𝓈)) σ i)
          (ιNf (N-ob (Gl-q A) Σ x))) ⟩
      App (ιNf (N-ob (q-A⇒B A B) Δ (N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t)) Δ 𝓈)) [ varify σ ])
        (ιNf (N-ob (Gl-q A) Σ x))
        ≡⟨ (λ i → App (ΛTwGl-nat-ob t i Δ 𝓈 [ varify σ ]) (ιNf (N-ob (Gl-q A) Σ x))) ⟩
      App (Lam (GlTm-α t) [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈) ] [ varify σ ])
        (ιNf (N-ob (Gl-q A) Σ x))
        ≡⟨ (λ i → App ([][] (Lam (GlTm-α t))
          (⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈)) (varify σ) i)
          (ιNf (N-ob (Gl-q A) Σ x))) ⟩
      App (Lam (GlTm-α t) [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈) ∘Tms varify σ ])
        (ιNf (N-ob (Gl-q A) Σ x))
        ≡⟨ (λ i → App (Lam (GlTm-α t)
          [ ⇓TMSHom (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈) σ (~ i) ])
          (ιNf (N-ob (Gl-q A) Σ x))) ⟩
      App (Lam (GlTm-α t)
        [ ⇓TMS (F-hom (⇓PSh (TMS (Gls-Γ Γ))) σ (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈)) ])
        (ιNf (N-ob (Gl-q A) Σ x))
        ≡⟨ (λ i → App (Lam[] (GlTm-α t)
          (⇓TMS (N-hom (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) σ (~ i) 𝓈)) i)
          (ιNf (N-ob (Gl-q A) Σ x))) ⟩
      App (Lam (GlTm-α t
        [ W₂Tms (Gl-A A) (⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Σ
          (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) σ 𝓈))) ])) (ιNf (N-ob (Gl-q A) Σ x))
        ≡⟨ β (GlTm-α t
          [ W₂Tms (Gl-A A) (⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Σ
            (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) σ 𝓈))) ]) (ιNf (N-ob (Gl-q A) Σ x)) ⟩
      GlTm-α t
        [ W₂Tms (Gl-A A) (⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Σ
          (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) σ 𝓈))) ] [ idTms Σ ⊕ ιNf (N-ob (Gl-q A) Σ x) ]
        ≡⟨ lem (GlTm-α t) (⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Σ
          (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) σ 𝓈))) (ιNf (N-ob (Gl-q A) Σ x)) ⟩
      GlTm-α t [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Σ
          (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) σ 𝓈)) ⊕ ιNf (N-ob (Gl-q A) Σ x) ]
        ≡⟨ indLem Γ A B (GlTm-α t) (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) σ 𝓈) x ⁻¹ ⟩
      N-ob (TMよ (GlTm-α t) ⟦ ιNFS (Gls-Γ (Γ ⊹ A)) ⊚ Gls-q Γ ×tm Gl-q A ⟧)
        Σ (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) σ 𝓈 , x)
        ≡⟨ (λ i → N-ob (GlTm-nat t (~ i)) Σ (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) σ 𝓈 , x)) ⟩
      ιNf (N-ob (Gl-q B) Σ (N-ob (GlTm-⦇α⦈ t) Σ (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) σ 𝓈 , x)))
        ∎) ⁻¹ where
        lem : {Γ Δ : Ctx} {A B : Ty} (t : Tm (Δ ⊹ A) B) (σ : Tms Γ Δ) (s : Tm Γ A) →
          t [ W₂Tms A σ ] [ idTms Γ ⊕ s ] ≡ t [ σ ⊕ s ]
        lem {Γ} {Δ} {A} t σ s =
          t [ W₂Tms A σ ] [ idTms Γ ⊕ s ]
            ≡⟨ [][] t (W₂Tms A σ) (idTms Γ ⊕ s) ⟩
          t [ W₁Tms A σ ∘Tms (idTms Γ ⊕ s)  ⊕ V 𝑧𝑣 [ idTms Γ ⊕ s ] ]
            ≡⟨ (λ i → t [ Wlem1 σ (idTms Γ) s i ⊕ 𝑧𝑣[] (idTms Γ) s i ]) ⟩
          t [ σ ∘Tms idTms Γ ⊕ s ]
            ≡⟨ (λ i → t [ ∘TmsIdR σ i ⊕ s ]) ⟩
          t [ σ ⊕ s ]
            ∎
  N-hom (GlTm-⦇α⦈ (ΛTwGl {Γ} {A} {B} t)) {Δ} {Σ} σ i α =
    (subtypeLem (⦇A⇒B⦈-ob A B Σ)
      (N-ob (GlTm-⦇α⦈ (ΛTwGl t)) Σ (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) σ α))
      (F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) σ (N-ob (GlTm-⦇α⦈ (ΛTwGl t)) Δ α))
      (λ j → N-hom (C-Λ _ _ _ (GlTm-⦇α⦈ t)) σ j α)) i
  GlTm-α (ΛTwGl t) = Lam (GlTm-α t)
  GlTm-nat (ΛTwGl {Γ} {A} {B} t) = makeNatTransPath (ΛTwGl-nat-ob t)

  GlTm-⦇α⦈forget : {Γ : Glueings} {A B : Glueing} → GlTm Γ (A ⇒TwGl B) →
    tm (Gls-⦇Γ⦈ Γ) (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B))
  N-ob (GlTm-⦇α⦈forget t) Γ 𝓈 = fst (N-ob (GlTm-⦇α⦈ t) Γ 𝓈)
  N-hom (GlTm-⦇α⦈forget t) σ i 𝓈 = fst (N-hom (GlTm-⦇α⦈ t) σ i 𝓈)

  AppTwGl-nat-ob : {Γ : Glueings} {A B : Glueing} (t : GlTm Γ (A ⇒TwGl B)) (s : GlTm Γ A) →
    N-ob ((ιNF (Gl-A B) 𝒩∘ Gl-q B) 𝒩∘ C-App _ _ _ (GlTm-⦇α⦈forget t) (GlTm-⦇α⦈ s))
    ≡ N-ob (TMよ (App (GlTm-α t) (GlTm-α s)) ⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧)
  AppTwGl-nat-ob {Γ} {A} {B} t s i Δ 𝓈 =
    (ιNf (N-ob (Gl-q B) Δ (N-ob (fst (N-ob (GlTm-⦇α⦈ t) Δ 𝓈)) Δ
      (id𝑅𝑒𝑛 Δ , N-ob (GlTm-⦇α⦈ s) Δ 𝓈)))
      ≡⟨ snd ((N-ob (GlTm-⦇α⦈ t)) Δ 𝓈) Δ (id𝑅𝑒𝑛 Δ) (N-ob (GlTm-⦇α⦈ s) Δ 𝓈) ⟩
    App (ιNf (N-ob (Gl-q (A ⇒TwGl B)) Δ (N-ob (GlTm-⦇α⦈ t) Δ 𝓈) [ id𝑅𝑒𝑛 Δ ]NF))
      (ιNf (N-ob (Gl-q A) Δ (N-ob (GlTm-⦇α⦈ s) Δ 𝓈)))
      ≡⟨ (λ j → App (ιNf ([id]NF (N-ob (Gl-q (A ⇒TwGl B)) Δ (N-ob (GlTm-⦇α⦈ t) Δ 𝓈)) j))
        (ιNf (N-ob (Gl-q A) Δ (N-ob (GlTm-⦇α⦈ s) Δ 𝓈)))) ⟩
    App (ιNf (N-ob (Gl-q (A ⇒TwGl B)) Δ (N-ob (GlTm-⦇α⦈ t) Δ 𝓈)))
      (ιNf (N-ob (Gl-q A) Δ (N-ob (GlTm-⦇α⦈ s) Δ 𝓈)))
      ≡⟨ (λ j → App (N-ob (GlTm-nat t j) Δ 𝓈) (N-ob (GlTm-nat s j) Δ 𝓈)) ⟩
    App (GlTm-α t [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈) ])
        (GlTm-α s [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈) ])
      ≡⟨ App[] (GlTm-α t) (GlTm-α s) (⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈)) ⁻¹ ⟩
    App (GlTm-α t) (GlTm-α s) [ ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈) ]
      ∎) i

  AppTwGl : {Γ : Glueings} {A B : Glueing} → GlTm Γ (A ⇒TwGl B) → GlTm Γ A → GlTm Γ B
  GlTm-⦇α⦈ (AppTwGl t s) = C-App _ _ _ (GlTm-⦇α⦈forget t) (GlTm-⦇α⦈ s)
  GlTm-α (AppTwGl t s) = App (GlTm-α t) (GlTm-α s)
  GlTm-nat (AppTwGl t s) = makeNatTransPath (AppTwGl-nat-ob t s)

  {-ΛTwGl-nat : {Γ Δ : Glueings} {A B : Glueing} (t : GlTm (Δ ⊹ A) B) (σ : GlTms Γ Δ) →
    ΛTwGl t [ σ ]Gl ≡ ΛTwGl (t [ (σ ∘GlTms G.π) ⊕ G.𝑧 ]Gl)
  ΛTwGl-nat {Γ} {Δ} {A} {B} t σ = {!!}

  AppGlTmβ : {Γ : Glueings} {A B : Glueing} (t : GlTm (Γ ⊹ A) B) (s : GlTm Γ A) →
    AppTwGl (ΛTwGl t) s ≡ t [ idTwGl Γ ⊕ s ]Gl
  AppGlTmβ {Γ} t s = {!!}
  
  𝐴𝑝𝑝TwGl : {Γ : Glueings} {A B : Glueing} → GlTm Γ (A ⇒TwGl B) → GlTm (Γ ⊹ A) B
  𝐴𝑝𝑝TwGl t = AppTwGl (t [ G.π ]Gl) G.𝑧

  AppGlTmη : {Γ : Glueings} {A B : Glueing} (t : GlTm Γ (A ⇒TwGl B)) →
    t ≡ ΛTwGl (𝐴𝑝𝑝TwGl t)
  AppGlTmη = {!!}-}

  open CCC

  isCCCTwGl : CCC TwGl
  _⇛_ isCCCTwGl = _⇒TwGl_
  Λ isCCCTwGl = ΛTwGl
  𝑎𝑝𝑝 isCCCTwGl = AppTwGl
  Λnat isCCCTwGl = {!ΛTwGl-nat!}
  𝑎𝑝𝑝β isCCCTwGl = {!AppGlTmβ!}
  𝑎𝑝𝑝η isCCCTwGl = {!AppGlTmη!}

  {- ≡GlTm : {Γ : Glueings} {A : Glueing} {t s : GlTm Γ A} →
    N-ob (GlTm-⦇α⦈ t) ≡ N-ob (GlTm-⦇α⦈ s) → GlTm-α t ≡ GlTm-α s → t ≡ s
  GlTm-⦇α⦈ (≡GlTm {t = t} {s} p q i) = makeNatTransPath {α = GlTm-⦇α⦈ t} {β = GlTm-⦇α⦈ s} p i
  GlTm-α (≡GlTm {t = t} {s} p q i) = q i
  GlTm-nat (≡GlTm {Γ} {A} {t} {s} p q i) j =
    isSet→SquareP (λ i j → isSetNat)
      (GlTm-nat t)
      (GlTm-nat s)
      (λ k → (ιNF (Gl-A A) 𝒩∘ Gl-q A) 𝒩∘ (GlTm-⦇α⦈ (≡GlTm {t = t} {s} p q k)))
      (λ k → TMよ (GlTm-α (≡GlTm {t = t} {s} p q k)) ⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧) i j

  ≡GlTm⇒ : {Γ : Glueings} {A B : Glueing} {t s : GlTm Γ (A ⇒TwGl B)} →
    ((Δ : Ctx) → (𝓈 : fst (F-ob (⇓PSh (Gls-⦇Γ⦈ Γ)) Δ))
      → fst (N-ob (GlTm-⦇α⦈ t) Δ 𝓈) ≡ fst (N-ob (GlTm-⦇α⦈ s) Δ 𝓈)) →
    GlTm-α t ≡ GlTm-α s → t ≡ s
  ≡GlTm⇒ {Γ} {A} {B} {t} {s} p q =
    ≡GlTm
      (λ i Δ 𝓈 →
        (subtypeLem (⦇A⇒B⦈-ob A B Δ)
          (N-ob (GlTm-⦇α⦈ t) Δ 𝓈)
          (N-ob (GlTm-⦇α⦈ s) Δ 𝓈)
          (p Δ 𝓈)) i) q

  𝑧TwGl-⦇α⦈ : {Γ : Glueings} {A : Glueing} → GlTm-⦇α⦈ (G.𝑧 {Γ} {A}) ≡ 𝑧 {Gls-⦇Γ⦈ Γ}
  𝑧TwGl-⦇α⦈ {Γ} {A} = ap 𝑧𝑇𝑚𝑠 (idTwGl-⦇αs⦈ {Γ ⊹ A})

  πTwGl-⦇αs⦈ : {Γ : Glueings} {A : Glueing} → GlTms-⦇αs⦈ (G.π {Γ} {A}) ≡ π {Gls-⦇Γ⦈ Γ}
  πTwGl-⦇αs⦈ {Γ} {A} = ap π𝑇𝑚𝑠 (idTwGl-⦇αs⦈ {Γ ⊹ A})

  ΛTwGl-nat-⦇α⦈-ob : {Γ Δ : Glueings} {A B : Glueing} (t : GlTm (Δ ⊹ A) B) (σ : GlTms Γ Δ)
    (Σ : Ctx) (𝓈 : fst (F-ob (⇓PSh (Gls-⦇Γ⦈ Γ)) Σ)) →
    fst (N-ob (GlTm-⦇α⦈ (ΛTwGl t [ σ ]Gl)) Σ 𝓈)
    ≡ fst (N-ob (GlTm-⦇α⦈ (ΛTwGl (t [ (σ ∘GlTms (G.π {Γ} {A})) ⊕ G.𝑧 {Γ} {A} ]Gl))) Σ 𝓈)
  ΛTwGl-nat-⦇α⦈-ob {Γ} {Δ} {A} {B} t σ Σ 𝓈 =
    {!N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t)) Σ (N-ob (⇓PShMor (GlTms-⦇αs⦈ σ)) Σ 𝓈)
      ≡⟨ (λ i → N-ob (C-Λnat _ _ _ _ (⇓PShMor (GlTms-⦇αs⦈ σ)) (GlTm-⦇α⦈ t) (~ i)) Σ 𝓈) ⟩
    N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t 𝒩∘ (C-pair (⇓PShMor (GlTms-⦇αs⦈ σ) 𝒩∘ C-π₁ _ _) 𝑧))) Σ 𝓈
      ≡⟨ (λ i → N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t 𝒩∘
        (C-pair (⇓PShMor (GlTms-⦇αs⦈ σ) 𝒩∘ ⇓πPSh {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A} (~ i)) 𝑧))) Σ 𝓈) ⟩
    N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t 𝒩∘
      (C-pair (⇓PShMor (GlTms-⦇αs⦈ σ) 𝒩∘ ⇓PShMor (π {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A})) 𝑧))) Σ 𝓈
      ≡⟨ (λ i → N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t 𝒩∘
        (C-pair (⇓∘PShMor (GlTms-⦇αs⦈ σ) (π {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A}) (~ i)) 𝑧))) Σ 𝓈) ⟩
    N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t ⟦ GlTms-⦇αs⦈ σ ⊚ (π {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A})
      ⊕ 𝑧 {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A} ⟧)) Σ 𝓈
      ≡⟨ (λ i → N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t ⟦ GlTms-⦇αs⦈ σ ⊚ πTwGl-⦇αs⦈ {Γ} {A} (~ i)
        ⊕ 𝑧TwGl-⦇α⦈ {Γ} {A} (~ i) ⟧))  Σ 𝓈) ⟩
    N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t ⟦ GlTms-⦇αs⦈ σ ⊚ GlTms-⦇αs⦈ (G.π {Γ} {A})
      ⊕ GlTm-⦇α⦈ (G.𝑧 {Γ} {A}) ⟧)) Σ 𝓈
      ≡⟨ (λ i → N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t ⟦ Gl-⦇αs⦈∘ σ (G.π {Γ} {A}) (~ i)
        ⊕ GlTm-⦇α⦈ (G.𝑧 {Γ} {A}) ⟧)) Σ 𝓈) ⟩
    N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t ⟦ GlTms-⦇αs⦈ ((σ ∘GlTms (G.π {Γ} {A}))
      ⊕ (G.𝑧 {Γ} {A})) ⟧)) Σ 𝓈
      ∎!}

  𝑧TwGl-α : {Γ : Glueings} {A : Glueing} → GlTm-α (G.𝑧 {Γ} {A}) ≡ V 𝑧𝑣
  𝑧TwGl-α {Γ} {A} = ap 𝑧𝑇𝑚𝑠 (idTwGl-αs {Γ ⊹ A})

  πTwGl-αs : {Γ : Glueings} {A : Glueing} →
    GlTms-αs (G.π {Γ} {A}) ≡ varify (W₁𝑅𝑒𝑛 (Gl-A A) (id𝑅𝑒𝑛 (Gls-Γ Γ)))
  πTwGl-αs {Γ} {A} = ap π𝑇𝑚𝑠 (idTwGl-αs {Γ ⊹ A})

  ΛTwGl-nat : {Γ Δ : Glueings} {A B : Glueing} (t : GlTm (Δ ⊹ A) B) (σ : GlTms Γ Δ) →
    ΛTwGl t [ σ ]Gl ≡ ΛTwGl (t [ (σ ∘GlTms G.π) ⊕ G.𝑧 ]Gl)
  ΛTwGl-nat {Γ} {Δ} {A} {B} t σ =
    ≡GlTm⇒
      (ΛTwGl-nat-⦇α⦈-ob t σ)
      (Lam (GlTm-α t) [ GlTms-αs σ ]
        ≡⟨ Lam[] (GlTm-α t) (GlTms-αs σ) ⟩
      Lam (GlTm-α t [ W₂Tms (Gl-A A) (GlTms-αs σ) ])
        ≡⟨ (λ i → Lam (GlTm-α t [ GlTms-αs σ ∘Tms πTwGl-αs {Γ} {A} (~ i)
          ⊕ 𝑧TwGl-α {Γ} {A} (~ i) ])) ⟩
      Lam (GlTm-α t [ GlTms-αs σ ∘Tms GlTms-αs (G.π {Γ} {A}) ⊕ GlTm-α (G.𝑧 {Γ} {A}) ])
        ≡⟨ (λ i → Lam (GlTm-α t [ Gl-αs∘ σ (G.π {Γ} {A}) (~ i) ⊕ GlTm-α (G.𝑧 {Γ} {A}) ])) ⟩
      Lam (GlTm-α t [ GlTms-αs (σ ∘GlTms (G.π {Γ} {A})) ⊕ GlTm-α (G.𝑧 {Γ} {A}) ])
        ∎)

  AppGlTmβ-⦇α⦈-ob : {Γ : Glueings} {A B : Glueing} (t : GlTm (Γ ⊹ A) B) (s : GlTm Γ A) →
    N-ob (GlTm-⦇α⦈ (AppTwGl (ΛTwGl t) s)) ≡ N-ob (GlTm-⦇α⦈ (t [ idTwGl Γ ⊕ s ]Gl))
  AppGlTmβ-⦇α⦈-ob {Γ} {A} {B} t s i Δ 𝓈 =
    (N-ob (GlTm-⦇α⦈ t) Δ (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) (id𝑅𝑒𝑛 Δ) 𝓈 ,  N-ob (GlTm-⦇α⦈ s) Δ 𝓈)
      ≡⟨ (λ j → N-ob (GlTm-⦇α⦈ t) Δ (F-id (⇓PSh (Gls-⦇Γ⦈ Γ)) j 𝓈 ,  N-ob (GlTm-⦇α⦈ s) Δ 𝓈)) ⟩
    N-ob (GlTm-⦇α⦈ t) Δ (𝓈 , N-ob (GlTm-⦇α⦈ s) Δ 𝓈)
      ≡⟨ (λ j → N-ob (GlTm-⦇α⦈ t) Δ (N-ob (⇓idPSh (Gls-⦇Γ⦈ Γ) (~ j)) Δ 𝓈
        , N-ob (GlTm-⦇α⦈ s) Δ 𝓈)) ⟩
    N-ob (GlTm-⦇α⦈ t) Δ (N-ob (⇓PShMor (𝒾𝒹 (Gls-⦇Γ⦈ Γ))) Δ 𝓈 , N-ob (GlTm-⦇α⦈ s) Δ 𝓈)
      ≡⟨ (λ j → N-ob (GlTm-⦇α⦈ t) Δ (N-ob (⇓PShMor (idTwGl-⦇αs⦈ {Γ} (~ j))) Δ 𝓈
        , N-ob (GlTm-⦇α⦈ s) Δ 𝓈)) ⟩
    N-ob (GlTm-⦇α⦈ t) Δ (N-ob (⇓PShMor (GlTms-⦇αs⦈ (idTwGl Γ))) Δ 𝓈 , N-ob (GlTm-⦇α⦈ s) Δ 𝓈)
      ∎) i

  AppGlTmβ : {Γ : Glueings} {A B : Glueing} (t : GlTm (Γ ⊹ A) B) (s : GlTm Γ A) →
    AppTwGl (ΛTwGl t) s ≡ t [ idTwGl Γ ⊕ s ]Gl
  AppGlTmβ {Γ} t s =
    ≡GlTm
      (AppGlTmβ-⦇α⦈-ob t s)
      (App (Lam (GlTm-α t)) (GlTm-α s)
        ≡⟨ β (GlTm-α t) (GlTm-α s) ⟩
      GlTm-α t [ idTms (map𝐶𝑡𝑥 Gl-A Γ) ⊕ GlTm-α s ]
        ≡⟨ (λ i → GlTm-α t [ idTwGl-αs {Γ} (~ i) ⊕ GlTm-α s  ]) ⟩
      GlTm-α t [ GlTms-αs (idTwGl Γ ⊕ s) ]
        ∎)

  TwGl⟦⟧-⦇αs⦈forget : {Γ Δ : Glueings} {A B : Glueing} (t : GlTm Δ (A ⇒TwGl B)) (σ : GlTms Γ Δ) →
    GlTm-⦇α⦈forget (t [ σ ]Gl) ≡ GlTm-⦇α⦈forget t 𝒩∘ ⇓PShMor (GlTms-⦇αs⦈ σ)
  TwGl⟦⟧-⦇αs⦈forget {Γ} {Δ} {A} t σ =
    makeNatTransPath
      (λ i Σ 𝓈 → fst (N-ob (GlTm-⦇α⦈ t) Σ (N-ob (⇓PShMor (GlTms-⦇αs⦈ σ)) Σ 𝓈)))

  𝐴𝑝𝑝TwGl : {Γ : Glueings} {A B : Glueing} → GlTm Γ (A ⇒TwGl B) → GlTm (Γ ⊹ A) B
  𝐴𝑝𝑝TwGl {Γ} {A} {B} t = AppTwGl (t [ G.π {Γ} {A} ]Gl) (G.𝑧 {Γ} {A})

  AppTwGlη-⦇α⦈-ob : {Γ Δ : Glueings} {A B : Glueing} (t : GlTm Γ (A ⇒TwGl B))
    (Σ : Ctx) (𝓈 : fst (F-ob (⇓PSh (Gls-⦇Γ⦈ Γ)) Σ)) →
    fst (N-ob (GlTm-⦇α⦈ t) Σ 𝓈)
    ≡ fst (N-ob (GlTm-⦇α⦈ (ΛTwGl (𝐴𝑝𝑝TwGl t))) Σ 𝓈)
  AppTwGlη-⦇α⦈-ob {Γ} {Δ} {A} {B} t Σ 𝓈 =
    {!N-ob (C-Λ _ _ _ (C-App _ _ _ (GlTm-⦇α⦈forget (t [ G.π ]Gl)) (𝑧 {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A}))) Σ 𝓈
      ≡⟨ (λ i → N-ob (C-Λ _ _ _ (C-App _ _ _ (TwGl⟦⟧-⦇αs⦈forget t G.π i)
        (𝑧 {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A}))) Σ 𝓈) ⟩
    ?
    {-N-ob (C-Λ _ _ _ (C-App _ _ _ (GlTm-⦇α⦈forget t 𝒩∘ ⇓PShMor (GlTms-⦇αs⦈ (G.π {Γ} {A})))
      (𝑧 {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A}))) Σ 𝓈-}
      {-≡⟨ (λ i → N-ob (C-Λ _ _ _ (C-App _ _ _ (GlTm-⦇α⦈forget t 𝒩∘ ⇓PShMor (πTwGl-⦇αs⦈ i))
        (𝑧 {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A}))) Σ 𝓈) ⟩
    ?-}
      ∎
    {-fst (N-ob (GlTm-⦇α⦈ t) Σ 𝓈)
      ≡⟨ (λ i → N-ob (C-Appη _ _ _ (GlTm-⦇α⦈forget t) i) Σ 𝓈) ⟩
    N-ob (C-Λ _ _ _ (C-App _ _ _
      (GlTm-⦇α⦈forget t 𝒩∘ C-π₁ (⇓PSh (Gls-⦇Γ⦈ Γ)) (Gl-⦇A⦈ A)) (𝑧 {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A}))) Σ 𝓈
      ≡⟨ (λ i → N-ob (C-Λ _ _ _ (C-App _ _ _ (GlTm-⦇α⦈forget t
        𝒩∘ ⇓πPSh {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A} (~ i)) (𝑧 {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A}))) Σ 𝓈) ⟩
    N-ob (C-Λ _ _ _ (C-App _ _ _ (GlTm-⦇α⦈forget t 𝒩∘ ⇓PShMor (π {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A}))
      (𝑧 {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A}))) Σ 𝓈
      ≡⟨ (λ i → 
    --N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ (𝐴𝑝𝑝TwGl t))) Σ 𝓈
      ∎-}!}

  AppGlTmη : {Γ : Glueings} {A B : Glueing} (t : GlTm Γ (A ⇒TwGl B)) →
    t ≡ ΛTwGl (𝐴𝑝𝑝TwGl t)
  AppGlTmη = {!!} -}
-}
  
