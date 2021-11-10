{-# OPTIONS --cubical #-}

module twglccc where

open import ren2
open import syn3
open import cartesian2
open import cartesian3
open import twglue
open import normal
open import psh

open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Categories.Instances.Sets

module _ where
  open Glueing
  open Functor
  open Cartesian (PShCart {𝒞 = REN})
  open Precategory (PSh REN) hiding (_∘_)
  open Contextual (𝒫𝒮𝒽 REN ⦃ isCatRen ⦄ ⦃ PShCat ⦄) 
  open NatTrans
  module R = Contextual ρεν

  private
    infixr 20 _𝒩∘_
    _𝒩∘_ = comp' (PSh REN)

  A-A⇒B : (A B : Glueing) → Ty
  A-A⇒B A B = Gl-A A ren2.⇒ Gl-A B

  q-A⇒B : (A B : Glueing) →
    Hom[ C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B) , NF (A-A⇒B A B) ]
  N-ob (q-A⇒B A B) Γ α =
    LAM (N-ob (Gl-q B) (Γ ⊹ 𝐴) (N-ob α (Γ ⊹ 𝐴)
      (W₁Ren 𝐴 (idRen Γ) , N-ob (Gl-u A) (Γ ⊹ 𝐴) (VN Zv)))) where
        𝐴 = (Gl-A A)
  N-hom (q-A⇒B A B) {Δ} {Σ} σ i α =
    (LAM (N-ob (Gl-q B) (Σ ⊹ 𝐴) (N-ob α (Σ ⊹ 𝐴)
      (σ ∘Ren W₁Ren 𝐴 (idRen Σ) , N-ob (Gl-u A) (Σ ⊹ 𝐴) (VN Zv))))
      ≡⟨ (λ j → LAM (N-ob (Gl-q B) (Σ ⊹ 𝐴) (N-ob α (Σ ⊹ 𝐴)
        (lem j , N-hom (Gl-u A) (W₂Ren 𝐴 σ) j (VN Zv))))) ⟩
    LAM (N-ob (Gl-q B) (Σ ⊹ 𝐴) (N-ob α (Σ ⊹ 𝐴) (W₁Ren 𝐴 (idRen Δ) ∘Ren W₂Ren 𝐴 σ ,
      (F-hom (Gl-⦇A⦈ A) (W₂Ren 𝐴 σ) (N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN Zv))))))
      ≡⟨ (λ j → LAM (N-ob (Gl-q B) (Σ ⊹ 𝐴) (N-hom α (W₂Ren 𝐴 σ) j
        (W₁Ren 𝐴 (idRen Δ) , N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN Zv))))) ⟩
    LAM (N-ob (Gl-q B) (Σ ⊹ 𝐴) (F-hom (Gl-⦇A⦈ B) (W₂Ren 𝐴 σ)
      (N-ob α (Δ ⊹ 𝐴) (W₁Ren 𝐴 (idRen Δ) , N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN Zv)))))
      ≡⟨ (λ j → LAM (N-hom (Gl-q B) (W₂Ren 𝐴 σ) j
        (N-ob α (Δ ⊹ 𝐴) (W₁Ren 𝐴 (idRen Δ) , N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN Zv))))) ⟩
    LAM (N-ob (Gl-q B) (Δ ⊹ 𝐴)
      (N-ob α (Δ ⊹ 𝐴) (W₁Ren 𝐴 (idRen Δ) , N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN Zv))) [ W₂Ren 𝐴 σ ]NF)
      ∎) i where
      𝐴 = (Gl-A A)
      lem : σ ∘Ren W₁Ren 𝐴 (idRen Σ) ≡ W₁Ren 𝐴 (idRen Δ) ∘Ren (W₂Ren 𝐴 σ)
      lem =
        σ ∘Ren W₁Ren 𝐴 (idRen Σ)
          ≡⟨ Wlem3Ren σ (idRen Σ) ⟩
        W₁Ren 𝐴 (σ ∘Ren idRen Σ)
          ≡⟨ ap (W₁Ren 𝐴) (R.𝒾𝒹R σ) ⟩
        W₁Ren 𝐴 σ
          ≡⟨ ap (W₁Ren 𝐴) (∘RenIdL σ ⁻¹) ⟩
        W₁Ren 𝐴 (idRen Δ ∘Ren σ)
          ≡⟨ Wlem5Ren (idRen Δ) σ ⁻¹ ⟩
        W₁Ren 𝐴 (idRen Δ) ∘Ren W₂Ren 𝐴 σ
          ∎

  u-A⇒B : (A B : Glueing) →
    Hom[ NE (A-A⇒B A B) , C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B) ]
  N-ob (N-ob (u-A⇒B A B) Γ M) Δ (σ , 𝓈) =
    N-ob (Gl-u B) Δ (APP (M [ σ ]NE) (N-ob (Gl-q A) Δ 𝓈))
  N-hom (N-ob (u-A⇒B A B) Γ M) {Δ} {Σ} σ i (τ , 𝓈) =
    (N-ob (Gl-u B) Σ (APP (M [ τ ∘Ren σ ]NE) (N-ob (Gl-q A) Σ (F-hom (Gl-⦇A⦈ A) σ 𝓈)))
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
      (λ k → N-ob (N-hom (u-A⇒B A B) σ k M) Δ (μ ∘Ren τ , F-hom (Gl-⦇A⦈ A) τ 𝓈))
      (λ k → F-hom (Gl-⦇A⦈ B) τ (N-ob (N-hom (u-A⇒B A B) σ k M) Γ (μ , 𝓈))) i j

  private
    comp-A⇒B-ob : (A B : Glueing) →
      N-ob (ιNF (A-A⇒B A B) 𝒩∘ (q-A⇒B A B) 𝒩∘ (u-A⇒B A B)) ≡ N-ob (ιNE (A-A⇒B A B))
    comp-A⇒B-ob A B i Γ M =
      (Lam (ιNf (N-ob (Gl-q B) (Γ ⊹ 𝐴) (N-ob (Gl-u B) (Γ ⊹ 𝐴)
        (APP (M [ W₁Ren (Gl-A A) (idRen Γ) ]NE)
             (N-ob (Gl-q A) (Γ ⊹ 𝐴) (N-ob (Gl-u A) (Γ ⊹ 𝐴) (VN Zv)))))))
        ≡⟨ (λ j → Lam (N-ob (Gl-comp B j) (Γ ⊹ 𝐴)
          (APP (M [ W₁Ren (Gl-A A) (idRen Γ) ]NE)
             (N-ob (Gl-q A) (Γ ⊹ 𝐴) (N-ob (Gl-u A) (Γ ⊹ 𝐴) (VN Zv)))))) ⟩
      Lam (App (ιNe (M [ mapIL Sv (idRen Γ) ]NE))
        (ιNf (N-ob (Gl-q A) (Γ ⊹ Gl-A A) (N-ob (Gl-u A) (Γ ⊹ Gl-A A) (VN Zv)))))
        ≡⟨ (λ j → Lam (App (ιNe (M [ mapIL Sv (idRen Γ) ]NE))
          (N-ob (Gl-comp A j) (Γ ⊹ 𝐴) (VN Zv)))) ⟩
      Lam (App (ιNe (M [ W₁Ren 𝐴 (idRen Γ) ]NE)) (V Zv))
        ≡⟨ (λ j → Lam (App (ιNeLem M (W₁Ren 𝐴 (idRen Γ)) j) (V Zv))) ⟩
      Lam (App (ιNe M [ varify (W₁Ren 𝐴 (idRen Γ)) ]) (V Zv))
        ≡⟨ (λ j → Lam (App (ιNe M [ Vlem2 (idRen Γ) j ]) (V Zv))) ⟩
      Lam (App (ιNe M [ W₁Tms 𝐴 (varify (idRen Γ)) ]) (V Zv))
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
  Sub-B (⦇A⇒B⦈-ob A B Γ) α = (Δ : Ctx) (σ : Ren Δ Γ) (x : fst (F-ob (Gl-⦇A⦈ A) Δ)) →
    ιNf (N-ob (Gl-q B) Δ (N-ob α Δ (σ , x)))
      ≡ App (ιNf (N-ob (q-A⇒B A B) Γ α [ σ ]NF)) (ιNf (N-ob (Gl-q A) Δ x))
  Sub-p (⦇A⇒B⦈-ob A B Γ) α = isPropΠ3 λ Δ σ y → trunc _ _
  
  _⇒TwGl_ : Glueing → Glueing → Glueing
  Gl-A (A ⇒TwGl B) = A-A⇒B A B
  
  F-ob (Gl-⦇A⦈ (A ⇒TwGl B)) Γ = type (⦇A⇒B⦈-ob A B Γ) , isSetType (⦇A⇒B⦈-ob A B Γ)
  F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) {Γ} {Δ} σ (α , p) =
    F-hom (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B)) σ α ,
      λ Σ τ x →
        ιNf (N-ob (Gl-q B) Σ (N-ob α Σ (σ ∘Ren τ , x)))
          ≡⟨ p Σ (σ ∘Ren τ) x ⟩
        App (ιNf (N-ob (q-A⇒B A B) Γ α [ σ ∘Ren τ ]NF)) (ιNf (N-ob (Gl-q A) Σ x))
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
      (F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) (idRen Γ) (α , p)) (α , p)
      (λ j → F-id (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B)) j α)) i
  F-seq (Gl-⦇A⦈ (A ⇒TwGl B)) {Γ} {Δ} {Σ} σ τ i (α , p) =
    (subtypeLem (⦇A⇒B⦈-ob A B Σ)
      (F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) (σ ∘Ren τ) (α , p))
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
  open PShFam

  ΛTwGL-nat-ob : {Γ : Glueings} {A B : Glueing} → (t : GlTm (Γ ⊹ A) B) →
    N-ob ((ιNF (A-A⇒B A B) 𝒩∘ q-A⇒B A B) 𝒩∘ (C-Λ _ _ _ (GlTm-⦇α⦈ t)))
    ≡ N-ob (TMよ (Lam (GlTm-α t)) ⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧)
  ΛTwGL-nat-ob {Γ} {A} {B} t i Δ 𝓈 =
    (Lam (ιNf (N-ob (Gl-q B) (Δ ⊹ 𝐴) (N-ob (GlTm-⦇α⦈ t) (Δ ⊹ Gl-A A)
      (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) (W₁Ren 𝐴 (idRen Δ)) 𝓈 ,
        N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN Zv)))))
      ≡⟨ (λ j → Lam (N-ob (GlTm-nat t j) (Δ ⊹ 𝐴)
        (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) (W₁Ren 𝐴 (idRen Δ)) 𝓈 ,
          N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN Zv)))) ⟩
    Lam (N-ob (TMよ (GlTm-α t) ⟦ ιNFS (Gls-Γ (Γ ⊹ A)) ⊚ Gls-q (Γ ⊹ A) ⟧)
      (Δ ⊹ Gl-A A) (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) (W₁Ren (Gl-A A) (idRen Δ)) 𝓈 ,
        N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN Zv)))
      ≡⟨ ap Lam (indLem Γ A B (GlTm-α t) (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) (W₁Ren 𝐴 (idRen Δ)) 𝓈)
        (N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN Zv))) ⟩
    Lam (GlTm-α t [
      ⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) (Δ ⊹ 𝐴)
        (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) (W₁Ren 𝐴 (idRen Δ)) 𝓈))
      ⊕ ιNf (N-ob (Gl-q A) (Δ ⊹ 𝐴) (N-ob (Gl-u A) (Δ ⊹ 𝐴) (VN Zv))) ])
      ≡⟨ (λ j → Lam (GlTm-α t [
        ⇓TMS (N-hom (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) (W₁Ren 𝐴 (idRen Δ)) j 𝓈)
        ⊕ N-ob (Gl-comp A j) (Δ ⊹ 𝐴) (VN Zv) ])) ⟩
    Lam (GlTm-α t [
      ⇓TMS (F-hom (⇓PSh (TMS (Gls-Γ Γ))) (W₁Ren 𝐴 (idRen Δ))
        (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈))
      ⊕ V Zv ])
      ≡⟨ (λ j → Lam (GlTm-α t [
        ⇓TMSHom (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈) (W₁Ren 𝐴 (idRen Δ)) j
        ⊕ V Zv ])) ⟩
    Lam (GlTm-α t [ W₂Tms 𝐴 (⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈)) ])
      ≡⟨ Lam[] (GlTm-α t) (⇓TMS (N-ob (⇓PShMor (ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ)) Δ 𝓈)) ⁻¹ ⟩
    N-ob (TMよ (Lam (GlTm-α t)) ⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧) Δ 𝓈
      ∎) i where
        𝐴 = (Gl-A A)

  ΛTwGL : {Γ : Glueings} {A B : Glueing} → GlTm (Γ ⊹ A) B → GlTm Γ (A ⇒TwGl B)
  N-ob (GlTm-⦇α⦈ (ΛTwGL {Γ} {A} {B} t)) Δ 𝓈 = N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t)) Δ 𝓈 ,
    λ Σ σ x →
      (App (ιNf (N-ob (q-A⇒B A B) Δ (N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t)) Δ 𝓈) [ σ ]NF))
        (ιNf (N-ob (Gl-q A) Σ x))
        ≡⟨ (λ i → App (ιNfLem (N-ob (q-A⇒B A B) Δ (N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t)) Δ 𝓈)) σ i)
          (ιNf (N-ob (Gl-q A) Σ x))) ⟩
      App (ιNf (N-ob (q-A⇒B A B) Δ (N-ob (C-Λ _ _ _ (GlTm-⦇α⦈ t)) Δ 𝓈)) [ varify σ ])
        (ιNf (N-ob (Gl-q A) Σ x))
        ≡⟨ (λ i → App (ΛTwGL-nat-ob t i Δ 𝓈 [ varify σ ]) (ιNf (N-ob (Gl-q A) Σ x))) ⟩
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
          t [ W₁Tms A σ ∘Tms (idTms Γ ⊕ s)  ⊕ V Zv [ idTms Γ ⊕ s ] ]
            ≡⟨ (λ i → t [ Wlem1 σ (idTms Γ) s i ⊕ Zv[] (idTms Γ) s i ]) ⟩
          t [ σ ∘Tms idTms Γ ⊕ s ]
            ≡⟨ (λ i → t [ ∘TmsIdR σ i ⊕ s ]) ⟩
          t [ σ ⊕ s ]
            ∎
  N-hom (GlTm-⦇α⦈ (ΛTwGL {Γ} {A} {B} t)) {Δ} {Σ} σ i α =
    (subtypeLem (⦇A⇒B⦈-ob A B Σ)
      (N-ob (GlTm-⦇α⦈ (ΛTwGL t)) Σ (F-hom (⇓PSh (Gls-⦇Γ⦈ Γ)) σ α))
      (F-hom (Gl-⦇A⦈ (A ⇒TwGl B)) σ (N-ob (GlTm-⦇α⦈ (ΛTwGL t)) Δ α))
      (λ j → N-hom (C-Λ _ _ _ (GlTm-⦇α⦈ t)) σ j α)) i
  GlTm-α (ΛTwGL t) = Lam (GlTm-α t)
  GlTm-nat (ΛTwGL {Γ} {A} {B} t) = makeNatTransPath (ΛTwGL-nat-ob t)

  GlTm-⦇α⦈forget : {Γ : Glueings} {A B : Glueing} → GlTm Γ (A ⇒TwGl B) →
    tm (Gls-⦇Γ⦈ Γ) (C-⇒ (Gl-⦇A⦈ A) (Gl-⦇A⦈ B))
  N-ob (GlTm-⦇α⦈forget t) Γ 𝓈 = fst (N-ob (GlTm-⦇α⦈ t) Γ 𝓈)
  N-hom (GlTm-⦇α⦈forget t) σ i 𝓈 = fst (N-hom (GlTm-⦇α⦈ t) σ i 𝓈)

  AppTwGl-nat-ob : {Γ : Glueings} {A B : Glueing} (t : GlTm Γ (A ⇒TwGl B)) (s : GlTm Γ A) →
    N-ob ((ιNF (Gl-A B) 𝒩∘ Gl-q B) 𝒩∘ C-App _ _ _ (GlTm-⦇α⦈forget t) (GlTm-⦇α⦈ s))
    ≡ N-ob (TMよ (App (GlTm-α t) (GlTm-α s)) ⟦ ιNFS (Gls-Γ Γ) ⊚ Gls-q Γ ⟧)
  AppTwGl-nat-ob {Γ} {A} {B} t s i Δ 𝓈 =
    (ιNf (N-ob (Gl-q B) Δ (N-ob (fst (N-ob (GlTm-⦇α⦈ t) Δ 𝓈)) Δ
      (idRen Δ , N-ob (GlTm-⦇α⦈ s) Δ 𝓈)))
      ≡⟨ snd ((N-ob (GlTm-⦇α⦈ t)) Δ 𝓈) Δ (idRen Δ) (N-ob (GlTm-⦇α⦈ s) Δ 𝓈) ⟩
    App (ιNf (N-ob (Gl-q (A ⇒TwGl B)) Δ (N-ob (GlTm-⦇α⦈ t) Δ 𝓈) [ idRen Δ ]NF))
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
