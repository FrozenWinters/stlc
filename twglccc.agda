{-# OPTIONS --cubical  #-}

module twglccc where

open import lists
open import contextual
open import ccc
open import normal
open import psh
open import twgl

module TwGlCCC {ℓ} (𝒞 : Contextual ℓ ℓ) ⦃ 𝒞CCC : CCC 𝒞 ⦄
                   {X : Type ℓ} (base : X → Contextual.ty 𝒞) where
  open Contextual 𝒞
  open Presheaf REN
  open PresheafCCC REN
  open TwGlCC 𝒞 base
  open CCC 𝒞CCC
  open Normal 𝒞 base

  private
    module R = Contextual ρεν
    module T = Contextual TwGl
    module P = Contextual 𝒫𝒮𝒽

  open GlTy
  open GlTm
  open PSh
  open PShMor
  open PShMorCart

  A-A⇒B : (A B : GlTy) → ty
  A-A⇒B A B = Gl-A A ⇛ Gl-A B

  ⦇A⦈-A⇒B : (A B : GlTy) → PSh
  ⦇A⦈-A⇒B A B = Gl-⦇A⦈ A ⇒PSh Gl-⦇A⦈ B
  
  q-A⇒B : (A B : GlTy) → PShMorCart (⦇A⦈-A⇒B A B) (NF (A-A⇒B A B))
  ob (q-A⇒B A B) 𝒻 = LAM (⟪Gl-q⟫ B (ob 𝒻 (R.π , ⟪Gl-u⟫ A (VN 𝑧𝑣))))
  nat (q-A⇒B A B) {Γ} {Δ} σ 𝒻 =
    LAM (⟪Gl-q⟫ B (ob 𝒻 (σ R.⊚ R.π , ⟪Gl-u⟫ A (VN 𝑧𝑣))))
      ≡⟨ (λ i → LAM (⟪Gl-q⟫ B (ob 𝒻 (lem i , nat (Gl-u A) (W₂𝑅𝑒𝑛 𝐴 σ) (VN 𝑧𝑣) i)))) ⟩
    LAM (⟪Gl-q⟫ B (ob 𝒻 (R.π R.⊚ W₂𝑅𝑒𝑛 𝐴 σ , hom (Gl-⦇A⦈ A) (W₂𝑅𝑒𝑛 𝐴 σ) (⟪Gl-u⟫ A (VN 𝑧𝑣)))))
      ≡⟨ (λ i → LAM (⟪Gl-q⟫ B (nat 𝒻 (W₂𝑅𝑒𝑛 𝐴 σ) (R.π , ⟪Gl-u⟫ A (VN 𝑧𝑣)) i))) ⟩
    LAM (⟪Gl-q⟫ B (hom (Gl-⦇A⦈ B) (W₂𝑅𝑒𝑛 𝐴 σ) (ob 𝒻 (R.π , ⟪Gl-u⟫ A (VN 𝑧𝑣)))))
      ≡⟨ ap LAM (nat (Gl-q B) (W₂𝑅𝑒𝑛 𝐴 σ) (ob 𝒻 (R.π , ⟪Gl-u⟫ A (VN 𝑧𝑣)))) ⟩
    LAM (⟪Gl-q⟫ B (ob 𝒻 (R.π , ⟪Gl-u⟫ A (VN 𝑧𝑣)))) [ σ ]NF
      ∎ where
    𝐴 = Gl-A A
    lem : σ R.⊚ R.π ≡ R.π R.⊚ (W₂𝑅𝑒𝑛 (Gl-A A) σ)
    lem =
      σ R.⊚ R.π
        ≡⟨ Wlem3𝑅𝑒𝑛 σ (R.𝒾𝒹 Γ) ⟩
      W₁𝑅𝑒𝑛 (Gl-A A) (σ ∘𝑅𝑒𝑛 R.𝒾𝒹 Γ)
        ≡⟨ (λ i → W₁𝑅𝑒𝑛 (Gl-A A) (R.𝒾𝒹L (R.𝒾𝒹R σ i) (~ i))) ⟩
      W₁𝑅𝑒𝑛 (Gl-A A) (R.𝒾𝒹 Δ ∘𝑅𝑒𝑛 σ)
        ≡⟨ Wlem5𝑅𝑒𝑛 (R.𝒾𝒹 Δ) σ ⁻¹ ⟩
      R.π R.⊚ W₂𝑅𝑒𝑛 (Gl-A A) σ
        ∎

  u-A⇒B : (A B : GlTy) → PShMorCart (NE (A-A⇒B A B)) (⦇A⦈-A⇒B A B)
  ob (ob (u-A⇒B A B) M) (σ , 𝓈) = ⟪Gl-u⟫ B (APP (M [ σ ]NE) (⟪Gl-q⟫ A 𝓈))
  nat (ob (u-A⇒B A B) M) σ (τ , 𝓈)=
    ⟪Gl-u⟫ B (APP (M [ τ R.⊚ σ ]NE) (⟪Gl-q⟫ A (hom (Gl-⦇A⦈ A) σ 𝓈)))
      ≡⟨ (λ i → ⟪Gl-u⟫ B (APP ([][]NE M τ σ (~ i)) (nat (Gl-q A) σ 𝓈 i))) ⟩
    ⟪Gl-u⟫ B (APP (M [ τ ]NE) (⟪Gl-q⟫ A 𝓈) [ σ ]NE)
      ≡⟨ nat (Gl-u B) σ (APP (M [ τ ]NE) (⟪Gl-q⟫ A 𝓈)) ⟩
    hom (Gl-⦇A⦈ B) σ (⟪Gl-u⟫ B (APP (M [ τ ]NE) (⟪Gl-q⟫ A 𝓈)))
      ∎
  nat (u-A⇒B A B) σ M =
    ≡PShMorCart (λ {(τ , 𝓈) i → ⟪Gl-u⟫ B (APP ([][]NE M σ τ i) (⟪Gl-q⟫ A 𝓈))})

  comp-A⇒B : (A B : GlTy) {Γ : ctx} (M : Ne Γ (A-A⇒B A B)) →
    (ιNf ∘ ob (q-A⇒B A B) ∘ ob (u-A⇒B A B)) M ≡ ιNe M
  comp-A⇒B A B M =
    Λ ((ιNf ∘ ⟪Gl-q⟫ B ∘ ⟪Gl-u⟫ B) (APP (M [ R.π ]NE) ((⟪Gl-q⟫ A ∘ ⟪Gl-u⟫ A) (VN 𝑧𝑣))))
      ≡⟨ ap Λ (Gl-comp B (APP (M [ R.π ]NE) ((⟪Gl-q⟫ A ∘ ⟪Gl-u⟫ A) (VN 𝑧𝑣)))) ⟩
    Λ (𝑎𝑝𝑝 (ιNe (M [ R.π ]NE)) ((ιNf ∘ ⟪Gl-q⟫ A ∘ ⟪Gl-u⟫ A) (VN 𝑧𝑣)))
      ≡⟨ (λ i → Λ (𝑎𝑝𝑝 (ιNeLem M R.π i) (Gl-comp A (VN 𝑧𝑣) i))) ⟩
    Λ (𝑎𝑝𝑝 (ιNe M ⟦ makeRen R.π ⟧) 𝑧)
      ≡⟨ (λ i → Λ (𝑎𝑝𝑝 (ιNe M ⟦ πη i ⟧) 𝑧)) ⟩
    Λ (𝑎𝑝𝑝 (ιNe M ⟦ π ⟧) 𝑧)
      ≡⟨ 𝑎𝑝𝑝η (ιNe M) ⁻¹ ⟩
    ιNe M
      ∎

  record Subset {ℓ₁ ℓ₂ : Level} : Type (lsuc (ℓ₁ ⊔ ℓ₂))  where
    field
      Sub-A : Type ℓ₁
      Sub-q : isSet Sub-A
      Sub-B : Sub-A → Type ℓ₂
      Sub-p : (𝓈 : Sub-A) → (isProp (Sub-B 𝓈))
      
    type = Σ Sub-A Sub-B

    isSetType : isSet type
    isSetType = isSetΣ Sub-q (λ 𝓈 → isProp→isSet (Sub-p 𝓈))
    
    subtypeLem : {𝓈 𝓉 : type} → fst 𝓈 ≡ fst 𝓉 → 𝓈 ≡ 𝓉
    subtypeLem {𝓈} {𝓉} a i = a i , isOfHLevel→isOfHLevelDep 1 (λ z → Sub-p z) (snd 𝓈) (snd 𝓉) a i

  open Subset

  ⦇A⇒B⦈-sec : (A B : GlTy) (Γ : ctx) → Subset
  Sub-A (⦇A⇒B⦈-sec A B Γ) = sec (⦇A⦈-A⇒B A B) Γ
  Sub-q (⦇A⇒B⦈-sec A B Γ) = isSetSec (⦇A⦈-A⇒B A B)
  Sub-B (⦇A⇒B⦈-sec A B Γ) 𝒻 = (Δ : ctx) (σ : IntRen Δ Γ) (𝓈 : sec (Gl-⦇A⦈ A) Δ) →
    (ιNf ∘ ⟪Gl-q⟫ B ∘ ob 𝒻) (σ , 𝓈)
    ≡ 𝑎𝑝𝑝 (ιNf (ob (q-A⇒B A B) 𝒻 [ σ ]NF)) (ιNf (⟪Gl-q⟫ A 𝓈))
  Sub-p (⦇A⇒B⦈-sec A B Γ) α = isPropΠ3 (λ Δ σ y → isSetTm _ _)

  _⇒TwGl_ : GlTy → GlTy → GlTy
  Gl-A (A ⇒TwGl B) = A-A⇒B A B
  
  sec (Gl-⦇A⦈ (A ⇒TwGl B)) Γ = type (⦇A⇒B⦈-sec A B Γ)
  isSetSec (Gl-⦇A⦈ (A ⇒TwGl B)) {Γ} = isSetType (⦇A⇒B⦈-sec A B Γ)
  hom (Gl-⦇A⦈ (A ⇒TwGl B)) σ (𝒻 , p) =
    hom (⦇A⦈-A⇒B A B) σ 𝒻 ,
    (λ Γ τ 𝓈 →
      (ιNf ∘ ⟪Gl-q⟫ B ∘ ob 𝒻) (σ R.⊚ τ , 𝓈)
        ≡⟨ p Γ (σ R.⊚ τ) 𝓈 ⟩
      𝑎𝑝𝑝 (ιNf (ob (q-A⇒B A B) 𝒻 [ σ R.⊚ τ ]NF)) (ιNf (⟪Gl-q⟫ A 𝓈))
        ≡⟨ (λ i → 𝑎𝑝𝑝 (ιNf ([][]NF (ob (q-A⇒B A B) 𝒻) σ τ (~ i))) (ιNf (⟪Gl-q⟫ A 𝓈))) ⟩
      𝑎𝑝𝑝 (ιNf (ob (q-A⇒B A B) 𝒻 [ σ ]NF [ τ ]NF)) (ιNf (⟪Gl-q⟫ A 𝓈))
        ≡⟨ (λ i → 𝑎𝑝𝑝 (ιNf (nat (q-A⇒B A B) σ 𝒻 (~ i) [ τ ]NF)) (ιNf (⟪Gl-q⟫ A 𝓈))) ⟩
      𝑎𝑝𝑝 (ιNf (ob (q-A⇒B A B) (hom (⦇A⦈-A⇒B A B) σ 𝒻) [ τ ]NF)) (ιNf (⟪Gl-q⟫ A 𝓈))
        ∎)
  id-hom (Gl-⦇A⦈ (A ⇒TwGl B)) {Γ} (𝒻 , p) =
    subtypeLem (⦇A⇒B⦈-sec A B Γ) (id-hom (⦇A⦈-A⇒B A B) 𝒻)
  ⊚-hom (Gl-⦇A⦈ (A ⇒TwGl B)) {Γ} σ τ (𝒻 , p) =
    subtypeLem (⦇A⇒B⦈-sec A B Γ) (⊚-hom (⦇A⦈-A⇒B A B) σ τ 𝒻)

  ob (Gl-q (A ⇒TwGl B)) (𝒻 , p) = ob (q-A⇒B A B) 𝒻
  nat (Gl-q (A ⇒TwGl B)) σ (𝒻 , p) = nat (q-A⇒B A B) σ 𝒻
  
  ob (Gl-u (A ⇒TwGl B)) M =
    ob (u-A⇒B A B) M ,
    (λ Γ σ 𝓈 →
      (ιNf ∘ ⟪Gl-q⟫ B ∘ ⟪Gl-u⟫ B) (APP (M [ σ ]NE) (⟪Gl-q⟫ A 𝓈))
        ≡⟨ Gl-comp B (APP (M [ σ ]NE) (⟪Gl-q⟫ A 𝓈)) ⟩
      𝑎𝑝𝑝 (ιNe (M [ σ ]NE)) (ιNf (⟪Gl-q⟫ A 𝓈))
        ≡⟨ (λ i →  𝑎𝑝𝑝 (ιNeLem M σ i) (ιNf (⟪Gl-q⟫ A 𝓈))) ⟩
      𝑎𝑝𝑝 (ιNe M ⟦ makeRen σ ⟧) (ιNf (⟪Gl-q⟫ A 𝓈))
        ≡⟨ (λ i →  𝑎𝑝𝑝 (comp-A⇒B A B M (~ i) ⟦ makeRen σ ⟧) (ιNf (⟪Gl-q⟫ A 𝓈))) ⟩
      𝑎𝑝𝑝 ((ιNf ∘ ob (q-A⇒B A B) ∘ ob (u-A⇒B A B)) M ⟦ makeRen σ ⟧) (ιNf (⟪Gl-q⟫ A 𝓈))
        ≡⟨ (λ i → 𝑎𝑝𝑝 (ιNfLem ((ob (q-A⇒B A B) ∘ ob (u-A⇒B A B)) M) σ (~ i)) (ιNf (⟪Gl-q⟫ A 𝓈))) ⟩
      𝑎𝑝𝑝 (ιNf (ob (q-A⇒B A B) (ob (u-A⇒B A B) M) [ σ ]NF)) (ιNf (⟪Gl-q⟫ A 𝓈))
        ∎)
  nat (Gl-u (A ⇒TwGl B)) {Γ} σ M =
    subtypeLem (⦇A⇒B⦈-sec A B Γ) (nat (u-A⇒B A B) σ M)
  
  Gl-comp (A ⇒TwGl B) M = comp-A⇒B A B M

  ΛTwGl-nat : {Γ : GlCtx} {A B : GlTy} (t : GlTm (Γ ⊹ A) B) {Δ : ctx} (𝓈s : secs (Gls-⦇Γ⦈ Γ) Δ) →
    (ιNf ∘ ob (q-A⇒B A B) ∘ ob (ΛPSh (GlTm-⦇α⦈ t))) 𝓈s
    ≡ Λ (GlTm-α t) ⟦ (ιNfs ∘ ⟪Gls-q⟫ Γ) 𝓈s ⟧
  ΛTwGl-nat {Γ} {A} {B} t 𝓈s =
    Λ ((ιNf ∘ ⟪Gl-q⟫ B ∘ ⟪GlTm-⦇α⦈⟫ t) (homs (Gls-⦇Γ⦈ Γ) R.π 𝓈s ⊕ ⟪Gl-u⟫ A (VN 𝑧𝑣)))
      ≡⟨ ap Λ (GlTm-nat t (homs (Gls-⦇Γ⦈ Γ) R.π 𝓈s ⊕ ⟪Gl-u⟫ A (VN 𝑧𝑣))) ⟩
    Λ (GlTm-α t ⟦ ιNfs (⟪Gls-q⟫ Γ (homs (Gls-⦇Γ⦈ Γ) R.π 𝓈s))
      ⊕ ((ιNf ∘ ⟪Gl-q⟫ A ∘ ⟪Gl-u⟫ A) (VN 𝑧𝑣)) ⟧)
      ≡⟨ (λ i → Λ (GlTm-α t ⟦ ιNfs (Gls-q-nat Γ R.π 𝓈s i) ⊕ Gl-comp A (VN 𝑧𝑣) i ⟧)) ⟩
    Λ (GlTm-α t ⟦ ιNfs (⟪Gls-q⟫ Γ 𝓈s [ R.π ]NFS) ⊕ 𝑧 ⟧)
      ≡⟨ (λ i → Λ (GlTm-α t ⟦ ιNfsLem (⟪Gls-q⟫ Γ 𝓈s) R.π i ⊕ 𝑧 ⟧)) ⟩
    Λ (GlTm-α t ⟦ ιNfs (⟪Gls-q⟫ Γ 𝓈s) ⊚ makeRen R.π ⊕ 𝑧 ⟧)
      ≡⟨ (λ i → Λ (GlTm-α t ⟦ ιNfs (⟪Gls-q⟫ Γ 𝓈s) ⊚ πη i ⊕ 𝑧 ⟧)) ⟩
    Λ (GlTm-α t ⟦ W₂tms (Gl-A A) ((ιNfs ∘ ⟪Gls-q⟫ Γ) 𝓈s) ⟧)
      ≡⟨ Λnat (GlTm-α t) ((ιNfs ∘ ⟪Gls-q⟫ Γ) 𝓈s) ⁻¹ ⟩
    Λ (GlTm-α t) ⟦ (ιNfs ∘ ⟪Gls-q⟫ Γ) 𝓈s ⟧
      ∎

  ΛTwGl : {Γ : GlCtx} {A B : GlTy} → GlTm (Γ ⊹ A) B → GlTm Γ (A ⇒TwGl B)
  ob (GlTm-⦇α⦈ (ΛTwGl {Γ} {A} {B} t)) 𝓈s =
    ob (ΛPSh (GlTm-⦇α⦈ t)) 𝓈s ,
    (λ Δ σ 𝓈 →
      (ιNf ∘ ⟪Gl-q⟫ B ∘ ⟪GlTm-⦇α⦈⟫ t) (homs (Gls-⦇Γ⦈ Γ) σ 𝓈s ⊕ 𝓈)
        ≡⟨ GlTm-nat t (homs (Gls-⦇Γ⦈ Γ) σ 𝓈s ⊕ 𝓈) ⟩
      GlTm-α t ⟦ ιNfs (⟪Gls-q⟫ Γ (homs (Gls-⦇Γ⦈ Γ) σ 𝓈s)) ⊕ ιNf (⟪Gl-q⟫ A 𝓈) ⟧
        ≡⟨ (λ i → GlTm-α t ⟦ ιNfs (Gls-q-nat Γ σ 𝓈s i) ⊕ ιNf (⟪Gl-q⟫ A 𝓈) ⟧) ⟩
      GlTm-α t ⟦ ιNfs (⟪Gls-q⟫ Γ 𝓈s [ σ ]NFS) ⊕ ιNf (⟪Gl-q⟫ A 𝓈) ⟧
        ≡⟨ (λ i → GlTm-α t ⟦ ιNfsLem (⟪Gls-q⟫ Γ 𝓈s) σ i ⊕ ιNf (⟪Gl-q⟫ A 𝓈) ⟧) ⟩
      GlTm-α t ⟦ ιNfs (⟪Gls-q⟫ Γ 𝓈s) ⊚ makeRen σ ⊕ ιNf (⟪Gl-q⟫ A 𝓈) ⟧
        ≡⟨ lem (GlTm-α t) (ιNfs (⟪Gls-q⟫ Γ 𝓈s) ⊚ makeRen σ) (ιNf (⟪Gl-q⟫ A 𝓈)) ⁻¹ ⟩
      GlTm-α t ⟦ W₂tms (Gl-A A) (ιNfs (⟪Gls-q⟫ Γ 𝓈s) ⊚ makeRen σ) ⟧ ⟦ 𝒾𝒹 Δ ⊕ ιNf (⟪Gl-q⟫ A 𝓈) ⟧
        ≡⟨ 𝑎𝑝𝑝β (GlTm-α t ⟦ W₂tms (Gl-A A) (ιNfs (⟪Gls-q⟫ Γ 𝓈s) ⊚ makeRen σ) ⟧)
          (ιNf (⟪Gl-q⟫ A 𝓈)) ⁻¹ ⟩
      𝑎𝑝𝑝 (Λ (GlTm-α t ⟦ W₂tms (Gl-A A) (ιNfs (⟪Gls-q⟫ Γ 𝓈s) ⊚ makeRen σ) ⟧)) (ιNf (⟪Gl-q⟫ A 𝓈))
        ≡⟨ (λ i → 𝑎𝑝𝑝 (Λnat (GlTm-α t) (ιNfs (⟪Gls-q⟫ Γ 𝓈s) ⊚ makeRen σ) (~ i))
          (ιNf (⟪Gl-q⟫ A 𝓈))) ⟩
      𝑎𝑝𝑝 (Λ (GlTm-α t) ⟦ ιNfs (⟪Gls-q⟫ Γ 𝓈s) ⊚ makeRen σ ⟧) (ιNf (⟪Gl-q⟫ A 𝓈))
        ≡⟨ (λ i → 𝑎𝑝𝑝 (⟦⟧⟦⟧ (Λ (GlTm-α t)) (ιNfs (⟪Gls-q⟫ Γ 𝓈s)) (makeRen σ) (~ i))
          (ιNf (⟪Gl-q⟫ A 𝓈))) ⟩
      𝑎𝑝𝑝 (Λ (GlTm-α t) ⟦ ιNfs (⟪Gls-q⟫ Γ 𝓈s) ⟧ ⟦ makeRen σ ⟧) (ιNf (⟪Gl-q⟫ A 𝓈))
        ≡⟨ (λ i → 𝑎𝑝𝑝 (ΛTwGl-nat t 𝓈s (~ i) ⟦ makeRen σ ⟧) (ιNf (⟪Gl-q⟫ A 𝓈))) ⟩
      𝑎𝑝𝑝 ((ιNf ∘ ob (q-A⇒B A B) ∘ ob (ΛPSh (GlTm-⦇α⦈ t))) 𝓈s ⟦ makeRen σ ⟧) (ιNf (⟪Gl-q⟫ A 𝓈))
        ≡⟨ (λ i → 𝑎𝑝𝑝 (ιNfLem (ob (q-A⇒B A B) (ob (ΛPSh (GlTm-⦇α⦈ t)) 𝓈s)) σ (~ i))
          (ιNf (⟪Gl-q⟫ A 𝓈))) ⟩
      𝑎𝑝𝑝 (ιNf ((ob (q-A⇒B A B) ∘ ob (ΛPSh (GlTm-⦇α⦈ t))) 𝓈s [ σ ]NF)) (ιNf (⟪Gl-q⟫ A 𝓈))
        ∎) where
    lem : {Γ Δ : ctx} {A B : ty} (t : tm (Δ ⊹ A) B) (σ : tms Γ Δ) (s : tm Γ A) →
      t ⟦ W₂tms A σ ⟧ ⟦ 𝒾𝒹 Γ ⊕ s ⟧ ≡ t ⟦ σ ⊕ s ⟧
    lem {Γ} {Δ} {A} t σ s =
      t ⟦ W₂tms A σ ⟧ ⟦ 𝒾𝒹 Γ ⊕ s ⟧
        ≡⟨ ⟦⟧⟦⟧ t (W₂tms A σ) (𝒾𝒹 Γ ⊕ s) ⟩
      t ⟦ W₁tms A σ ⊚ (𝒾𝒹 Γ ⊕ s) ⊕ 𝑧 ⟦ 𝒾𝒹 Γ ⊕ s ⟧ ⟧
        ≡⟨ (λ i → t ⟦ Wtms⊚ σ (𝒾𝒹 Γ) s i ⊕ 𝑧⟦⟧ (𝒾𝒹 Γ ⊕ s) i ⟧) ⟩
      t ⟦ σ ⊚ 𝒾𝒹 Γ ⊕ s ⟧
        ≡⟨ (λ i → t ⟦ 𝒾𝒹R σ i ⊕ s ⟧)⟩
      t ⟦ σ ⊕ s ⟧
        ∎
  nat (GlTm-⦇α⦈ (ΛTwGl {Γ} {A} {B} t)) {Δ} σ 𝓈s =
    subtypeLem (⦇A⇒B⦈-sec A B Δ) (nat (ΛPSh (GlTm-⦇α⦈ t)) σ 𝓈s)
  GlTm-α (ΛTwGl t) = Λ (GlTm-α t)
  GlTm-nat (ΛTwGl t) 𝓈s = ΛTwGl-nat t 𝓈s

  GlTm-⦇α⦈forget : {Γ : GlCtx} {A B : GlTy} → GlTm Γ (A ⇒TwGl B) →
    PShMor (Gls-⦇Γ⦈ Γ) (⦇A⦈-A⇒B A B)
  ob (GlTm-⦇α⦈forget t) 𝓈s = fst (ob (GlTm-⦇α⦈ t) 𝓈s)
  nat (GlTm-⦇α⦈forget t) σ 𝓈s = ap fst (nat (GlTm-⦇α⦈ t) σ 𝓈s)

  AppTwGl : {Γ : GlCtx} {A B : GlTy} → GlTm Γ (A ⇒TwGl B) → GlTm Γ A → GlTm Γ B
  GlTm-⦇α⦈ (AppTwGl {Γ} {A} {B} t s) = AppPSh (GlTm-⦇α⦈forget {Γ} {A} {B} t) (GlTm-⦇α⦈ s)
  GlTm-α (AppTwGl t s) = 𝑎𝑝𝑝 (GlTm-α t) (GlTm-α s)
  GlTm-nat (AppTwGl {Γ} {A} {B} t s) {Δ} 𝓈s =
    (ιNf ∘ ⟪Gl-q⟫ B ∘ ob (fst (⟪GlTm-⦇α⦈⟫ t 𝓈s))) (R.𝒾𝒹 Δ , ⟪GlTm-⦇α⦈⟫ s 𝓈s)
      ≡⟨ snd (⟪GlTm-⦇α⦈⟫ t 𝓈s) Δ (R.𝒾𝒹 Δ) (⟪GlTm-⦇α⦈⟫ s 𝓈s) ⟩
    𝑎𝑝𝑝 (ιNf (ob (q-A⇒B A B) (fst (⟪GlTm-⦇α⦈⟫ t 𝓈s)) [ R.𝒾𝒹 Δ ]NF))
      ((ιNf ∘ ⟪Gl-q⟫ A ∘ ⟪GlTm-⦇α⦈⟫ s) 𝓈s)
      ≡⟨ (λ i → 𝑎𝑝𝑝 (ιNf ([id]NF (ob (q-A⇒B A B) (fst (⟪GlTm-⦇α⦈⟫ t 𝓈s))) i))
         ((ιNf ∘ ⟪Gl-q⟫ A ∘ ⟪GlTm-⦇α⦈⟫ s) 𝓈s) ) ⟩
    𝑎𝑝𝑝 ((ιNf ∘ ⟪Gl-q⟫ (A ⇒TwGl B) ∘ ⟪GlTm-⦇α⦈⟫ t) 𝓈s) ((ιNf ∘ ⟪Gl-q⟫ A ∘ ⟪GlTm-⦇α⦈⟫ s) 𝓈s)
      ≡⟨ (λ i → 𝑎𝑝𝑝 (GlTm-nat t 𝓈s i) (GlTm-nat s 𝓈s i)) ⟩
    𝑎𝑝𝑝 (GlTm-α t ⟦ (ιNfs ∘ ⟪Gls-q⟫ Γ) 𝓈s ⟧) (GlTm-α s ⟦ (ιNfs ∘ ⟪Gls-q⟫ Γ) 𝓈s ⟧)
      ≡⟨ 𝑎𝑝𝑝⟦⟧ (GlTm-α t) (GlTm-α s) ((ιNfs ∘ ⟪Gls-q⟫ Γ) 𝓈s) ⁻¹ ⟩
    𝑎𝑝𝑝 (GlTm-α t) (GlTm.GlTm-α s) ⟦ (ιNfs ∘ ⟪Gls-q⟫ Γ) 𝓈s ⟧
      ∎

  ≡GlTm⇒ : {Γ : GlCtx} {A B : GlTy} {t s : GlTm Γ (A ⇒TwGl B)} →
    ({Δ : ctx} → (𝓈s : secs (Gls-⦇Γ⦈ Γ) Δ)
      → fst (ob (GlTm-⦇α⦈ t) 𝓈s) ≡ fst (ob (GlTm-⦇α⦈ s) 𝓈s)) →
    GlTm-α t ≡ GlTm-α s → t ≡ s
  ≡GlTm⇒ {Γ} {A} {B} {t} {s} p q =
    ≡GlTm (≡PShMor (λ {Δ} 𝓈s → subtypeLem (⦇A⇒B⦈-sec A B Δ) (p 𝓈s))) q

  W₂TwGl-⦇αs⦈ : {Γ Δ : GlCtx} (A : GlTy) (σ : GlTms Γ Δ) →
    GlTms-⦇αs⦈ (T.W₂tms A σ) ≡ P.W₂tms (Gl-⦇A⦈ A) (GlTms-⦇αs⦈ σ)
  W₂TwGl-⦇αs⦈ {Γ} {Δ} A σ =
    GlTms-⦇αs⦈ (σ T.⊚ T.π ⊕ T.𝑧)
      ≡⟨ (λ i → Gl-⦇αs⦈∘ σ (T.π {Γ} {A}) i ⊕ GlTm-⦇α⦈ (T.𝑧 {Γ} {A})) ⟩
    GlTms-⦇αs⦈ σ P.⊚ GlTms-⦇αs⦈ T.π ⊕ GlTm-⦇α⦈ (T.𝑧 {Γ} {A})
      ≡⟨ (λ i → GlTms-⦇αs⦈ σ P.⊚ π𝐸𝑙𝑠 (idTwGl-⦇αs⦈ (Γ ⊹ A) i) ⊕ 𝑧𝐸𝑙𝑠 (idTwGl-⦇αs⦈ (Γ ⊹ A) i)) ⟩
    P.W₂tms (Gl-⦇A⦈ A) (GlTms-⦇αs⦈ σ)
      ∎

  W₂TwGl-αs : {Γ Δ : GlCtx} (A : GlTy) (σ : GlTms Γ Δ) →
    GlTms-αs (T.W₂tms A σ) ≡ W₂tms (Gl-A A) (GlTms-αs σ)
  W₂TwGl-αs {Γ} {Δ} A σ =
    GlTms-αs (σ T.⊚ T.π ⊕ T.𝑧)
      ≡⟨ (λ i → Gl-αs∘ σ (T.π {Γ} {A}) i ⊕ GlTm-α (T.𝑧 {Γ} {A})) ⟩
    GlTms-αs σ ⊚ GlTms-αs T.π ⊕ GlTm-α (T.𝑧 {Γ} {A})
      ≡⟨ (λ i → GlTms-αs σ ⊚ π𝐸𝑙𝑠 (idTwGl-αs (Γ ⊹ A) i) ⊕ 𝑧𝐸𝑙𝑠 (idTwGl-αs (Γ ⊹ A) i)) ⟩
    W₂tms (Gl-A A) (GlTms-αs σ)
      ∎

  ΛnatTwGl : {Γ Δ : T.ctx} {A B : T.ty} (t : T.tm (Δ ⊹ A) B) (σ : T.tms Γ Δ) →
    ΛTwGl {Δ} {A} {B} t T.⟦ σ ⟧ ≡ ΛTwGl {Γ} {A} {B} (t T.⟦ T.W₂tms A σ ⟧)
  ΛnatTwGl {A = A} {B} t σ =
    ≡GlTm⇒ {A = A} {B}
      (λ {Σ} 𝓈s →
        (ob (ΛPSh (GlTm-⦇α⦈ t)) ∘ ⟪GlTms-⦇αs⦈⟫ σ) 𝓈s
          ≡⟨ (λ i → ob (ΛnatPSh (GlTm-⦇α⦈ t) (GlTms-⦇αs⦈ σ) i) 𝓈s) ⟩
        ob (ΛPSh (GlTm-⦇α⦈ t P.⟦ P.W₂tms (Gl-⦇A⦈ A) (GlTms-⦇αs⦈ σ) ⟧)) 𝓈s
          ≡⟨ (λ i → ob (ΛPSh (GlTm-⦇α⦈ t P.⟦ W₂TwGl-⦇αs⦈ A σ (~ i) ⟧)) 𝓈s) ⟩
        ob (ΛPSh (GlTm-⦇α⦈ (t T.⟦ T.W₂tms A σ ⟧))) 𝓈s
          ∎)
      (Λ (GlTm-α t) ⟦ GlTms-αs σ ⟧
        ≡⟨ Λnat (GlTm-α t) (GlTms-αs σ) ⟩
      Λ (GlTm-α t ⟦ W₂tms (Gl-A A) (GlTms-αs σ) ⟧)
        ≡⟨ (λ i → Λ (GlTm-α t ⟦ W₂TwGl-αs A σ (~ i) ⟧)) ⟩
      Λ (GlTm-α (t T.⟦ T.W₂tms A σ ⟧))
        ∎)

  AppβGlTm : {Γ : GlCtx} {A B : GlTy} (t : GlTm (Γ ⊹ A) B) (s : GlTm Γ A) →
    AppTwGl {Γ} {A} {B} (ΛTwGl {Γ} {A} {B} t) s ≡ t T.⟦ T.𝒾𝒹 Γ ⊕ s ⟧
  AppβGlTm {Γ} {A} {B} t s =
    ≡GlTm
      (≡PShMor
        (λ {Δ} 𝓈s →
          ⟪GlTm-⦇α⦈⟫ t (homs (Gls-⦇Γ⦈ Γ) (R.𝒾𝒹 Δ) 𝓈s ⊕ ⟪GlTm-⦇α⦈⟫ s 𝓈s)
            ≡⟨ ap (λ x → ob x 𝓈s) (AppβPSh (GlTm-⦇α⦈ t) (GlTm-⦇α⦈ s)) ⟩
          ob (GlTm-⦇α⦈ t P.⟦ P.𝒾𝒹 (Gls-⦇Γ⦈ Γ) ⊕ GlTm-⦇α⦈ s ⟧) 𝓈s
            ≡⟨ (λ i → ob (GlTm-⦇α⦈ t P.⟦ idTwGl-⦇αs⦈ Γ (~ i) ⊕ GlTm-⦇α⦈ s ⟧) 𝓈s) ⟩
          ob (GlTm-⦇α⦈ (t T.⟦ T.𝒾𝒹 Γ ⊕ s ⟧)) 𝓈s
            ∎))
      (𝑎𝑝𝑝 (Λ (GlTm-α t)) (GlTm-α s)
        ≡⟨ 𝑎𝑝𝑝β (GlTm-α t) (GlTm-α s) ⟩
      GlTm-α t ⟦ 𝒾𝒹 (Gls-Γ Γ) ⊕ GlTm-α s ⟧
        ≡⟨ (λ i → GlTm-α t ⟦ idTwGl-αs Γ (~ i) ⊕ GlTm-α s ⟧) ⟩
      GlTm-α (t T.⟦ T.𝒾𝒹 Γ ⊕ s ⟧)
        ∎)

  𝐴𝑝𝑝TwGl : {Γ : GlCtx} {A B : GlTy} → GlTm Γ (A ⇒TwGl B) → GlTm (Γ ⊹ A) B
  𝐴𝑝𝑝TwGl {Γ} {A} {B} t = AppTwGl {Γ ⊹ A} {A} {B} (t T.⟦ T.π ⟧) (T.𝑧)

  TwGl⟦⟧-⦇αs⦈forget : {Γ Δ : GlCtx} {A B : GlTy} (t : GlTm Δ (A ⇒TwGl B)) (σ : GlTms Γ Δ) →
    GlTm-⦇α⦈forget {Γ} {A} {B} (t T.⟦ σ ⟧) ≡ (GlTm-⦇α⦈forget {Δ} {A} {B} t P.⟦ GlTms-⦇αs⦈ σ ⟧)
  TwGl⟦⟧-⦇αs⦈forget {Γ} {Δ} {A} {B} t σ =
    ≡PShMor⇒ {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A} {Gl-⦇A⦈ B} (λ 𝓈s τ 𝓈 → refl)

  AppηGlTm : {Γ : T.ctx} {A B : T.ty} (t : T.tm Γ (A ⇒TwGl B)) →
    t ≡ ΛTwGl {Γ} {A} {B} (𝐴𝑝𝑝TwGl {Γ} {A} {B} t)
  AppηGlTm {Γ} {A} {B} t =
    ≡GlTm⇒ {A = A} {B}
      (λ 𝓈s →
        fst (ob (GlTm-⦇α⦈ t) 𝓈s)
          ≡⟨ ap (λ x → ob x 𝓈s) (AppηPSh {Gls-⦇Γ⦈ Γ} {Gl-⦇A⦈ A} {Gl-⦇A⦈ B}
            (GlTm-⦇α⦈forget {Γ} {A} {B} t)) ⟩
        ob (ΛPSh (AppPSh {α = Gl-⦇A⦈ A} {Gl-⦇A⦈ B}
          (GlTm-⦇α⦈forget {Γ} {A} {B} t P.⟦ P.π ⟧) P.𝑧)) 𝓈s
          ≡⟨ (λ i → ob (ΛPSh (AppPSh {α = Gl-⦇A⦈ A} {Gl-⦇A⦈ B}
            (GlTm-⦇α⦈forget {Γ} {A} {B} t P.⟦ π𝐸𝑙𝑠 (idTwGl-⦇αs⦈ (Γ ⊹ A) (~ i)) ⟧) P.𝑧)) 𝓈s) ⟩
        ob (ΛPSh (AppPSh {α = Gl-⦇A⦈ A} {Gl-⦇A⦈ B}
          (GlTm-⦇α⦈forget {Γ} {A} {B} t P.⟦ GlTms-⦇αs⦈ T.π ⟧) P.𝑧)) 𝓈s
          ≡⟨ (λ i → ob (ΛPSh (AppPSh {α = Gl-⦇A⦈ A} {Gl-⦇A⦈ B}
            (TwGl⟦⟧-⦇αs⦈forget {Γ ⊹ A} {Γ} {A} {B} t T.π (~ i)) P.𝑧)) 𝓈s) ⟩
        ob (ΛPSh (AppPSh {α = Gl-⦇A⦈ A} {Gl-⦇A⦈ B}
          (GlTm-⦇α⦈forget {Γ ⊹ A} {A} {B} (t T.⟦ T.π ⟧)) P.𝑧)) 𝓈s
          ∎)
      (GlTm-α t
        ≡⟨ 𝑎𝑝𝑝η (GlTm-α t) ⟩
      Λ (𝑎𝑝𝑝 (GlTm-α t ⟦ π ⟧) 𝑧)
        ≡⟨ (λ i → Λ (𝑎𝑝𝑝 (GlTm-α t ⟦ π𝐸𝑙𝑠 (idTwGl-αs (Γ ⊹ A) (~ i)) ⟧) 𝑧)) ⟩
      Λ (𝑎𝑝𝑝 (GlTm-α t ⟦ GlTms-αs T.π ⟧) 𝑧)
        ∎)

  instance
    isCCCTwGl : CCC TwGl
    CCC._⇛_ isCCCTwGl = _⇒TwGl_
    CCC.Λ isCCCTwGl {Γ} {A} {B} = ΛTwGl {Γ} {A} {B}
    CCC.𝑎𝑝𝑝 isCCCTwGl {Γ} {A} {B} = AppTwGl {Γ} {A} {B}
    CCC.Λnat isCCCTwGl {Γ} {Δ} {A} {B} t σ = ΛnatTwGl {Γ} {Δ} {A} {B} t σ
    CCC.𝑎𝑝𝑝β isCCCTwGl {Γ} {A} {B} t s = AppβGlTm {Γ} {A} {B} t s
    CCC.𝑎𝑝𝑝η isCCCTwGl {Γ} {A} {B} t = AppηGlTm {Γ} {A} {B} t
  
