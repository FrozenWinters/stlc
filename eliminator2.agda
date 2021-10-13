{-# OPTIONS --cubical #-}

module eliminator2 where

open import cartesian
open import syn2
open import ren

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

module Eliminator {ℓ₁ ℓ₂} (𝒞 : Precategory ℓ₁ ℓ₂)
                  ⦃ isCat𝒞 : isCategory 𝒞 ⦄ ⦃ cart : Cartesian 𝒞 ⦄
                  (base : (c : Char) → Precategory.ob 𝒞) where
  open Precategory
  open Cartesian cart
  open Functor
  private
    module C = Precategory 𝒞
    isSet𝒞Hom = isCat𝒞 .isSetHom

  interpTy : Ty → ob 𝒞
  interpTy (Base c) = base c
  interpTy (A ⇒ B) = C-⇒ (interpTy A) (interpTy B)

  interpCtx : Ctx → ob 𝒞
  interpCtx ∅ = C-1
  interpCtx (Γ ⊹ A) = C-× (interpCtx Γ) (interpTy A)

  interpVar : {Γ : Ctx} {A : Ty} (v : Var Γ A) → C.Hom[ interpCtx Γ , interpTy A ]
  interpVar {Γ ⊹ A} {A} Zv = C-π₂ (interpCtx Γ) (interpTy A)
  interpVar {Γ ⊹ B} {A} (Sv v) = interpVar v C.∘ C-π₁ (interpCtx Γ) (interpTy B)

  interpTm : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → C.Hom[ interpCtx Γ , interpTy A ]

  {-# TERMINATING #-}
  interpTms : {Γ Δ : Ctx} (σ : Tms Γ Δ) → C.Hom[ interpCtx Γ , interpCtx Δ ]
  interpTms ! = C-!
  interpTms (σ ⊕ t) = C-pair (interpTms σ) (interpTm t)

  interpW₁Tms : {Γ Δ : Ctx} {A : Ty} (σ : Tms Γ Δ) →
    interpTms (W₁Tms A σ) ≡ interpTms σ C.∘ C-π₁ (interpCtx Γ) (interpTy A)
  interp∘Tms : {Γ Δ Σ : Ctx} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
    interpTms (σ ∘Tms τ) ≡ interpTms σ C.∘ interpTms τ
  interpId : {Γ : Ctx} → interpTms (idTms Γ) ≡ C.id (interpCtx Γ)

  private
    usefulLem : {Γ : Ctx} {A : Ty} →
      C-π₁ (interpCtx Γ) (interpTy A) ≡ interpTms (W₁Tms A (idTms Γ))
    usefulLem {Γ} {A} =
      C-π₁ (interpCtx Γ) (interpTy A)
        ≡⟨ C.⋆IdR (C-π₁ (interpCtx Γ) (interpTy A)) ⁻¹ ⟩
      C.id (interpCtx Γ) C.∘ C-π₁ (interpCtx Γ) (interpTy A)
        ≡⟨ ap (C._∘ C-π₁ (interpCtx Γ) (interpTy A)) (interpId {Γ} ⁻¹) ⟩
      (interpTms (idTms Γ) C.∘ C-π₁ (interpCtx Γ) (interpTy A))
        ≡⟨ interpW₁Tms (idTms Γ) ⁻¹ ⟩
      interpTms (W₁Tms A (idTms Γ))
        ∎

  interpTm (V v) =
    interpVar v
  interpTm (Lam {Γ} {A} {B} t) =
    C-Λ (interpCtx Γ) (interpTy A) (interpTy B) (interpTm t)
  interpTm (App {Γ} {A} {B} t s) =
    C-App (interpCtx Γ) (interpTy A) (interpTy B) (interpTm t) (interpTm s)
  interpTm (t [ σ ]) =
    interpTm t C.∘ interpTms σ
  interpTm (W₁ {Γ} A {B} t) =
    interpTm t C.∘ C-π₁ (interpCtx Γ) (interpTy A)
  
  interpTm (β {Γ} {A} {B} t s i) =
    (C-App (interpCtx Γ) (interpTy A) (interpTy B)
         (C-Λ (interpCtx Γ) (interpTy A) (interpTy B) (interpTm t))
         (interpTm s)
      ≡⟨ C-Appβ (interpCtx Γ) (interpTy A) (interpTy B) (interpTm t) (interpTm s) ⟩
    interpTm t C.∘ C-pair (C.id (interpCtx Γ)) (interpTm s)
      ≡⟨ (λ i →  interpTm t C.∘ C-pair (interpId {Γ} (~ i)) (interpTm s)) ⟩
    interpTm t C.∘ C-pair (interpTms (idTms Γ)) (interpTm s)
      ∎) i
  interpTm (η {Γ} {A} {B} t i) =
    (interpTm t
      ≡⟨ C-Appη (interpCtx Γ) (interpTy A) (interpTy B) (interpTm t) ⁻¹ ⟩
    C-Λ (interpCtx Γ) (interpTy A) (interpTy B)
      (C-App (C-× (interpCtx Γ) (interpTy A)) (interpTy A) (interpTy B)
       (interpTm t C.∘ C-π₁ (interpCtx Γ) (interpTy A))
       (C-π₂ (interpCtx Γ) (interpTy A)))
      ≡⟨ (λ i → C-Λ (interpCtx Γ) (interpTy A) (interpTy B)
          (C-App (C-× (interpCtx Γ) (interpTy A)) (interpTy A) (interpTy B)
           (interpTm t C.∘ usefulLem {Γ} {A} i)
           (C-π₂ (interpCtx Γ) (interpTy A)))) ⟩
    C-Λ (interpCtx Γ) (interpTy A) (interpTy B)
      (C-App (C-× (interpCtx Γ) (interpTy A)) (interpTy A) (interpTy B)
       (interpTm t C.∘ interpTms (W₁Tms A (idTms Γ))) (C-π₂ (interpCtx Γ) (interpTy A)))
      ∎) i
  interpTm (Zv[] σ t i) =
    C-π₂β (interpTms σ) (interpTm t) i
  interpTm (Sv[] {Γ} {Δ} {A} {B} v σ t i) =
    (C.⋆Assoc
      (C-pair (interpTms σ) (interpTm t)) (C-π₁ (interpCtx Δ) (interpTy B)) (interpVar v) ⁻¹
    ∙ ap (interpVar v C.∘_) (C-π₁β (interpTms σ) (interpTm t))) i
  interpTm (Lam[] {Γ} {Δ} {A} {B} t σ i) =
    (C-Λnat₁ (interpCtx Γ) (interpCtx Δ) (interpTy A) (interpTy B)
      (interpTms σ) (interpTm t) ⁻¹
    ∙ (λ k → C-Λ (interpCtx Γ) (interpTy A) (interpTy B)
        (interpTm t C.∘
          C-pair (interpW₁Tms {A = A} σ (~ k))
          (C-π₂ (interpCtx Γ) (interpTy A))))) i 
  interpTm (App[] t s σ i) =
    App∘ (interpTm t) (interpTm s) (interpTms σ) i
  interpTm ([][] t σ τ i) =
    ((interpTm t C.∘ interpTms σ) C.∘ interpTms τ
      ≡⟨ C.⋆Assoc (interpTms τ) (interpTms σ) (interpTm t) ⁻¹ ⟩
    interpTm t C.∘ (interpTms σ C.∘ interpTms τ)
      ≡⟨ ap (interpTm t C.∘_) (interp∘Tms σ τ ⁻¹) ⟩
    interpTm t C.∘ interpTms (σ ∘Tms τ)
      ∎) i
  interpTm {Γ} ([id] t i) =
    (interpTm t C.∘ interpTms (idTms Γ)
      ≡⟨ ap (interpTm t C.∘_) (interpId {Γ}) ⟩
    (interpTm t C.∘ C.id (interpCtx Γ))
      ≡⟨ C.⋆IdL (interpTm t) ⟩
    interpTm t
      ∎) i
  interpTm (W₁V {Γ} {A} v i) =
    interpVar v C.∘ C-π₁ (interpCtx Γ) (interpTy A)
  interpTm (W₁Lam {Γ} {A} {B} {C} t i) =
    ((C-Λ (interpCtx Γ) (interpTy B) (interpTy C) (interpTm t) C.∘
       C-π₁ (interpCtx Γ) (interpTy A))
       ≡⟨ (λ j → C-Λnat₁ (C-× (interpCtx Γ) (interpTy A)) (interpCtx Γ) (interpTy B) (interpTy C)
             (usefulLem {Γ} {A} j) (interpTm t) (~ j)) ⟩
    C-Λ (C-× (interpCtx Γ) (interpTy A)) (interpTy B) (interpTy C)
      (interpTm t C.∘
       C-pair
       (interpTms (W₁Tms A (idTms Γ)) C.∘
        C-π₁ (C-× (interpCtx Γ) (interpTy A)) (interpTy B))
       (C-π₂ (C-× (interpCtx Γ) (interpTy A)) (interpTy B)))
      ≡⟨ (λ j → C-Λ (C-× (interpCtx Γ) (interpTy A)) (interpTy B) (interpTy C)
            (interpTm t C.∘ C-pair
              (interpW₁Tms {A = B} (W₁Tms A (idTms Γ)) (~ j))
              (C-π₂ (C-× (interpCtx Γ) (interpTy A)) (interpTy B)))) ⟩
    C-Λ (C-× (interpCtx Γ) (interpTy A)) (interpTy B) (interpTy C)
      (interpTm t C.∘
       C-pair (interpW₁Tms {A = B} (W₁Tms A (idTms Γ)) (~ i1))
       (C-π₂ (C-× (interpCtx Γ) (interpTy A)) (interpTy B)))
      ∎) i
  interpTm (W₁App {Γ} {A} t s i) =
    App∘ (interpTm t) (interpTm s) (C-π₁ (interpCtx Γ) (interpTy A)) i
  interpTm {Γ} {A} (isSetTm t s p q i j) =
    isSet→SquareP (λ i j → isSet𝒞Hom)
      (λ k → interpTm (p k))
      (λ k → interpTm (q k))
      (λ k → interpTm t)
      (λ k → interpTm s) i j

  interpW₁Tms {Γ} {Δ} {A} ! = C-!η (C-! C.∘ C-π₁ (interpCtx Γ) (interpTy A)) ⁻¹
  interpW₁Tms {Γ} {Δ ⊹ B} {A} (σ ⊕ t) =
    C-pair (interpTms (W₁Tms A σ)) (interpTm t C.∘ C-π₁ (interpCtx Γ) (interpTy A))
      ≡⟨ (λ i →
        C-pair (interpW₁Tms {A = A} σ i) (interpTm t C.∘ C-π₁ (interpCtx Γ) (interpTy A))) ⟩
    C-pair (interpTms σ C.∘ C-π₁ (interpCtx Γ) (interpTy A))
           (interpTm t C.∘ C-π₁ (interpCtx Γ) (interpTy A))
      ≡⟨ π∘ (interpTms σ) (interpTm t) (C-π₁ (interpCtx Γ) (interpTy A )) ⁻¹ ⟩
    (C-pair (interpTms σ) (interpTm t) C.∘ C-π₁ (interpCtx Γ) (interpTy A))
      ∎

  interp∘Tms ! τ = C-!η (C-! C.∘ interpTms τ) ⁻¹
  interp∘Tms (σ ⊕ t) τ =
    C-pair (interpTms (σ ∘Tms τ)) (interpTm t C.∘ interpTms τ)
      ≡⟨ (λ k → C-pair (interp∘Tms σ τ k) (interpTm t C.∘ interpTms τ)) ⟩
    C-pair (interpTms σ C.∘ interpTms τ) (interpTm t C.∘ interpTms τ)
      ≡⟨ π∘ (interpTms σ) (interpTm t) (interpTms τ) ⁻¹ ⟩
    (C-pair (interpTms σ) (interpTm t) C.∘ interpTms τ)
      ∎

  interpId {∅} = C-!η (C.id C-1) ⁻¹
  interpId {Γ ⊹ A} =
    C-pair (interpTms (varify (W₁Ren A (idRen Γ)))) (C-π₂ (interpCtx Γ) (interpTy A))
      ≡⟨ (λ k → C-pair (interpTms (Vlem1 {A = A} (idRen Γ) k))
                       (C-π₂ (interpCtx Γ) (interpTy A))) ⟩
    C-pair (interpTms (W₁Tms A (idTms Γ))) (C-π₂ (interpCtx Γ) (interpTy A))
      ≡⟨ (λ k → C-pair (interpW₁Tms {A = A} (idTms Γ) k) (C-π₂ (interpCtx Γ) (interpTy A))) ⟩
    C-pair (interpTms (idTms Γ) C.∘ C-π₁ (interpCtx Γ) (interpTy A))
           (C-π₂ (interpCtx Γ) (interpTy A))
      ≡⟨ (λ k → C-pair
            (interpId {Γ} k C.∘ C-π₁ (interpCtx Γ) (interpTy A))
            (C-π₂ (interpCtx Γ) (interpTy A))) ⟩
    C-pair (C.id (interpCtx Γ) C.∘ C-π₁ (interpCtx Γ) (interpTy A))
      (C-π₂ (interpCtx Γ) (interpTy A))
      ≡⟨ (λ k → C-pair
            (C.⋆IdR (C-π₁ (interpCtx Γ) (interpTy A)) k)
            (C-π₂ (interpCtx Γ) (interpTy A))) ⟩
    C-pair (C-π₁ (interpCtx Γ) (interpTy A)) (C-π₂ (interpCtx Γ) (interpTy A))
      ≡⟨ (λ k → C-pair
       (C.⋆IdL (C-π₁ (interpCtx Γ) (interpTy A)) (~ k))
       (C.⋆IdL (C-π₂ (interpCtx Γ) (interpTy A)) (~ k))) ⟩
    C-pair
      (C-π₁ (interpCtx Γ) (interpTy A) C.∘ C.id (C-× (interpCtx Γ) (interpTy A)))
      (C-π₂ (interpCtx Γ) (interpTy A) C.∘ C.id (C-× (interpCtx Γ) (interpTy A)))
      ≡⟨ C-πη (C-× (interpCtx Γ) (interpTy A)) (interpCtx Γ) (interpTy A)
            (C.id (C-× (interpCtx Γ) (interpTy A))) ⟩
    C.id (C-× (interpCtx Γ) (interpTy A))
      ∎

module _ where
  open Precategory
  open Functor
  open PShCartesian REN

  semanticBase : Char → ob (PSh REN)
  semanticBase X = TM (Base X)

  open Eliminator (PSh REN) ⦃ PShCat ⦄ semanticBase

  SEM : Ty → ob (PSh REN)
  SEM A = interpTy A

module _ where
  open NatTrans
  open Functor
  open Precategory (PSh REN) hiding (_∘_)
  open PShCartesian REN
  open Eliminator (PSh REN) ⦃ PShCat ⦄ semanticBase

  qTM1 : (A : Ty) → Hom[ SEM A , TM A ]
  uTM1 : (A : Ty) → Hom[ TM A , SEM A ]

  N-ob (qTM1 (Base X)) Γ t = t
  N-hom (qTM1 (Base X)) σ = refl
  N-ob (qTM1 (A ⇒ B)) Γ α =
    Lam (N-ob (qTM1 B) (Γ ⊹ A) (N-ob α (Γ ⊹ A) (W₁Ren A (idRen Γ) , N-ob (uTM1 A) (Γ ⊹ A) (V Zv))))
  N-hom (qTM1 (A ⇒ B)) {Δ} {Σ} σ i α =
    (Lam (N-ob (qTM1 B) (Δ ⊹ A)
      (N-ob α (Δ ⊹ A) (W₁Ren A (idRen Δ) , N-ob (uTM1 A) (Δ ⊹ A) (V Zv)))) [ varify σ ]
      ≡⟨ Lam[] (N-ob (qTM1 B) (Δ ⊹ A)
          (N-ob α (Δ ⊹ A) (W₁Ren A (idRen Δ) , N-ob (uTM1 A) (Δ ⊹ A) (V Zv)))) (varify σ) ⟩
    Lam (N-ob (qTM1 B) (Δ ⊹ A)
      (N-ob α (Δ ⊹ A) (W₁Ren A (idRen Δ) , N-ob (uTM1 A) (Δ ⊹ A) (V Zv)))
        [ W₁Tms A (varify σ) ⊕ V Zv ])
     ≡⟨ (λ j → Lam (N-ob (qTM1 B) (Δ ⊹ A)
          (N-ob α (Δ ⊹ A) (W₁Ren A (idRen Δ) , N-ob (uTM1 A) (Δ ⊹ A) (V Zv)))
            [ Vlem1 σ (~ j) ⊕ V Zv ])) ⟩
   Lam (N-ob (qTM1 B) (Δ ⊹ A)
     (N-ob α (Δ ⊹ A) (W₁Ren A (idRen Δ) , N-ob (uTM1 A) (Δ ⊹ A) (V Zv)))
       [ varify (W₂Ren A σ) ])
     ≡⟨ (λ j → Lam
       (N-hom (qTM1 B) (W₂Ren A σ) (~ j)
         (N-ob α (Δ ⊹ A) (W₁Ren A (idRen Δ) , N-ob (uTM1 A) (Δ ⊹ A) (V Zv))))) ⟩
   _
     ≡⟨ (λ j → Lam (N-ob (qTM1 B) (Σ ⊹ A)
       (N-hom α (W₂Ren A σ) (~ j) (W₁Ren A (idRen Δ) , N-ob (uTM1 A) (Δ ⊹ A) (V Zv))))) ⟩
   _
     ≡⟨ (λ j → Lam (N-ob (qTM1 B) (Σ ⊹ A) (N-ob α (Σ ⊹ A)
       (lem j ,
         N-hom (uTM1 A) (W₂Ren A σ) (~ j) (V Zv))))) ⟩
   Lam
      (N-ob (qTM1 B) (Σ ⊹ A)
       (N-ob α (Σ ⊹ A)
        (σ ∘Ren W₁Ren A (idRen Σ) ,
         N-ob (uTM1 A) (Σ ⊹ A) (V Zv [ varify (W₁Ren A σ) ⊕ V Zv ]))))
     ≡⟨ (λ j → Lam (N-ob (qTM1 B) (Σ ⊹ A)
       (N-ob α (Σ ⊹ A)
        (σ ∘Ren W₁Ren A (idRen Σ) ,
         N-ob (uTM1 A) (Σ ⊹ A) (Zv[] (varify (W₁Ren A σ)) (V Zv) j))))) ⟩
   Lam
      (N-ob (qTM1 B) (Σ ⊹ A)
       (N-ob α (Σ ⊹ A)
        (σ ∘Ren W₁Ren A (idRen Σ) , N-ob (uTM1 A) (Σ ⊹ A) (V Zv))))
     ∎) (~ i) where
     lem : W₁Ren A (idRen Δ) ∘Ren (W₂Ren A σ) ≡ σ ∘Ren W₁Ren A (idRen Σ)
     lem =
       W₁Ren A (idRen Δ) ∘Ren W₂Ren A σ
         ≡⟨ Wlem5Ren (idRen Δ) σ ⟩
       W₁Ren A (idRen Δ ∘Ren σ)
         ≡⟨ ap (W₁Ren A) (∘RenIdL σ) ⟩
       W₁Ren A σ
         ≡⟨ ap (W₁Ren A) (∘RenIdR σ ⁻¹) ⟩
       W₁Ren A (σ ∘Ren idRen Σ)
         ≡⟨ Wlem3Ren σ (idRen Σ) ⁻¹ ⟩
       σ ∘Ren W₁Ren A (idRen Σ)
         ∎
  
  N-ob (uTM1 (Base X)) Γ t = t
  N-hom (uTM1 (Base X)) σ = refl
  N-ob (N-ob (uTM1 (A ⇒ B)) Γ t) Δ (σ , 𝓈) =
    N-ob (uTM1 B) Δ (App (t [ varify σ ]) (N-ob (qTM1 A) Δ 𝓈))
  N-hom (N-ob (uTM1 (A ⇒ B)) Γ t) {Δ} {Σ} σ i (τ , 𝓈) =
    (N-ob (uTM1 B) Σ (App (t [ varify (τ ∘Ren σ) ]) (N-ob (qTM1 A) Σ (F-hom (interpTy A) σ 𝓈)))
      ≡⟨ (λ j → N-ob (uTM1 B) Σ (App (t [ Vlem4 τ σ j ]) (N-hom (qTM1 A) σ j 𝓈))) ⟩
    N-ob (uTM1 B) Σ (App (t [ varify τ ∘Tms varify σ ]) (N-ob (qTM1 A) Δ 𝓈 [ varify σ ]))
      ≡⟨ (λ j → N-ob (uTM1 B) Σ (App ([][] t (varify τ) (varify σ) (~ j))
        (N-ob (qTM1 A) Δ 𝓈 [ varify σ ]))) ⟩
    N-ob (uTM1 B) Σ (App (t [ varify τ ] [ varify σ ]) (N-ob (qTM1 A) Δ 𝓈 [ varify σ ]))
      ≡⟨ (λ j → N-ob (uTM1 B) Σ (App[] (t [ varify τ ]) (N-ob (qTM1 A) Δ 𝓈) (varify σ) (~ j))) ⟩
    N-ob (uTM1 B) Σ (App (t [ varify τ ]) (N-ob (qTM1 A) Δ 𝓈) [ varify σ ])
      ≡⟨ (λ j → N-hom (uTM1 B) σ j (App (t [ varify τ ]) (N-ob (qTM1 A) Δ 𝓈))) ⟩
    F-hom (interpTy B) σ (N-ob (uTM1 B) Δ (App (t [ varify τ ]) (N-ob (qTM1 A) Δ 𝓈)))
      ∎) i
  N-ob (N-hom (uTM1 (A ⇒ B)) σ i t) Γ (τ , 𝓈) =
    (N-ob (uTM1 B) Γ (App (t [ varify σ ] [ varify τ ]) (N-ob (qTM1 A) Γ 𝓈))
      ≡⟨ (λ j → N-ob (uTM1 B) Γ (App ([][] t (varify σ) (varify τ) j) (N-ob (qTM1 A) Γ 𝓈))) ⟩
    N-ob (uTM1 B) Γ (App (t [ varify σ ∘Tms varify τ ]) (N-ob (qTM1 A) Γ 𝓈))
      ≡⟨ (λ j → N-ob (uTM1 B) Γ (App (t [ Vlem4 σ τ (~ j) ]) (N-ob (qTM1 A) Γ 𝓈))) ⟩
    N-ob (uTM1 B) Γ (App (t [ varify (σ ∘Ren τ) ]) (N-ob (qTM1 A) Γ 𝓈))
      ∎) i
  N-hom (N-hom (uTM1 (A ⇒ B)) {Σ} {Ω} σ i t) {Γ} {Δ} τ j (μ , 𝓈) =
    isSet→SquareP (λ i j → snd (F-ob (interpTy B) Δ))
      (λ k → N-hom (N-ob (uTM1 (A Ty.⇒ B)) Ω (t [ varify σ ])) τ k (μ , 𝓈))
      (λ k → N-hom (F-hom (SEM (A Ty.⇒ B)) σ (N-ob (uTM1 (A Ty.⇒ B)) Σ t)) τ k (μ , 𝓈))
      (λ k → N-ob (N-hom (uTM1 (A Ty.⇒ B)) σ k t) Δ (μ ∘Ren τ , F-hom (interpTy A) τ 𝓈))
      (λ k → F-hom (interpTy B) τ (N-ob (N-hom (uTM1 (A Ty.⇒ B)) σ k t) Γ (μ , 𝓈))) i j

module _ where
  open NatTrans
  open Functor
  open Precategory (PSh REN) hiding (_∘_)
  open PShCartesian REN
  open Eliminator (PSh REN) ⦃ PShCat ⦄ semanticBase

  qTM : (A : Ty) → Hom[ SEM A , NF A ]
  uTM : (A : Ty) → Hom[ NE A , SEM A ]

  N-ob (qTM (Base X)) = {!!}
  N-hom (qTM (Base X)) = {!!}
  N-ob (qTM (A ⇒ B)) = {!!}
  N-hom (qTM (A ⇒ B)) = {!!}

  uTM (Base X) = {!!}
  uTM (A ⇒ B) = {!!}

module _ where
  open NatTrans

  open SampleSyn

  test1 = N-ob (uTM1 (ChurchType (Base 'A'))) ∅ TwoPlusTwo
  test2 = N-ob (qTM1 (ChurchType (Base 'A'))) ∅ test1

  {-test1 = SEM (ChurchType (Base 'A')) .F-ob ∅
  test2 = SEM (ChurchType (Base 'A')) .F-hom-}
