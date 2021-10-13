{-# OPTIONS --cubical --allow-unsolved-metas #-}

module eliminator where

open import cartesian
open import syn
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
    interpTms (W₁Tms {A = A} σ) ≡ interpTms σ C.∘ C-π₁ (interpCtx Γ) (interpTy A)
  interp∘Tms : {Γ Δ Σ : Ctx} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
    interpTms (σ ∘Tms τ) ≡ interpTms σ C.∘ interpTms τ
  interpId : {Γ : Ctx} → interpTms (idTms {Γ}) ≡ C.id (interpCtx Γ)

  interpTm (V v) = interpVar v
  interpTm {Γ} {A ⇒ B} (Lam t) =
    C-Λ (interpCtx Γ) (interpTy A) (interpTy B) (interpTm t)
  interpTm (App {Γ} {A} {B} t s) =
    C-App (interpCtx Γ) (interpTy A) (interpTy B) (interpTm t) (interpTm s)
  interpTm (t [ σ ]) = interpTm t C.∘ interpTms σ
  interpTm (Zv[] σ t i) =
    C-π₂β (interpTms σ) (interpTm t) i
  interpTm (Sv[] {Γ} {Δ} {A} {B} v σ t i) =
    (C.⋆Assoc
      (C-pair (interpTms σ) (interpTm t)) (C-π₁ (interpCtx Δ) (interpTy B)) (interpVar v) ⁻¹
    ∙ ap (interpVar v C.∘_) (C-π₁β (interpTms σ) (interpTm t))) i
  interpTm (Lam[] {Γ} {Δ} {A} {B} σ t i) =
    (C-Λnat₁ (interpCtx Γ) (interpCtx Δ) (interpTy A) (interpTy B)
      (interpTms σ) (interpTm t) ⁻¹
    ∙ (λ k → C-Λ (interpCtx Γ) (interpTy A) (interpTy B)
        (interpTm t C.∘
          C-pair (interpW₁Tms {A = A} σ (~ k))
          (C-π₂ (interpCtx Γ) (interpTy A))))) i 
  interpTm (App[] {Γ} {Δ} {Σ} {A} σ t s i) =
    App∘ (interpTm t) (interpTm s) (interpTms σ) i
  interpTm {Γ} {A} ([][] t σ τ i) =
    ((interpTm t C.∘ interpTms σ) C.∘ interpTms τ
      ≡⟨ C.⋆Assoc (interpTms τ) (interpTms σ) (interpTm t) ⁻¹ ⟩
    interpTm t C.∘ (interpTms σ C.∘ interpTms τ)
      ≡⟨ ap (interpTm t C.∘_) (interp∘Tms σ τ ⁻¹) ⟩
    interpTm t C.∘ interpTms (σ ∘Tms τ)
      ∎) i
  interpTm (β {Γ} {A} {B} t s i) =
    (C-App (interpCtx Γ) (interpTy A) (interpTy B)
      (C-Λ (interpCtx Γ) (interpTy A) (interpTy B) (interpTm t))
      (interpTm s)
      ≡⟨ C-Appβ (interpCtx Γ) (interpTy A) (interpTy B) (interpTm t) (interpTm s) ⟩
    (interpTm t C.∘ C-pair (C.id (interpCtx Γ)) (interpTm s))
      ≡⟨ {!!} ⟩
    interpTm t C.∘ C-pair (interpTms (idTms {Γ = Γ})) (interpTm s)
      ∎) i
  interpTm (η t i) =
    {!!}
  interpTm {Γ} {A} (isSetTm t s p q i j) =
    isSet→SquareP (λ i j → isSet𝒞Hom)
      (λ k → interpTm (p k))
      (λ k → interpTm (q k))
      (λ k → interpTm t)
      (λ k → interpTm s) i j

  interpW₁Tm : {Γ : Ctx} {A B : Ty} (t : Tm Γ A) →
    interpTm (W₁Tm {B = B} t) ≡ interpTm t C.∘ C-π₁ (interpCtx Γ) (interpTy B)
  interpW₁Tm (V v) = refl
  interpW₁Tm {Γ} {A ⇒ B} {C} (Lam t) =
    C-Λ (C-× (interpCtx Γ) (interpTy C)) (interpTy A) (interpTy B)
      (interpTm t C.∘
       C-pair (interpTms (varify (W₁Ren {A = A} (W₁Ren {A = C} (idRen {Γ})))))
              (C-π₂ (C-× (interpCtx Γ) (interpTy C)) (interpTy A)))
      ≡⟨ (λ k → C-Λ (C-× (interpCtx Γ) (interpTy C)) (interpTy A) (interpTy B)
        (interpTm t C.∘
          C-pair (interpTms (Vlem0 {A = A} (W₁Ren {A = C} (idRen {Γ})) k))
                 (C-π₂ (C-× (interpCtx Γ) (interpTy C)) (interpTy A)))) ⟩
    C-Λ (C-× (interpCtx Γ) (interpTy C)) (interpTy A) (interpTy B)
      (interpTm t C.∘
        C-pair (interpTms (W₁Tms {A = A} (varify (W₁Ren {A = C} (idRen {Γ})))))
               (C-π₂ (C-× (interpCtx Γ) (interpTy C)) (interpTy A)))
      ≡⟨ (λ k → C-Λ (C-× (interpCtx Γ) (interpTy C)) (interpTy A) (interpTy B)
            (interpTm t C.∘
              C-pair (interpW₁Tms {A = A} (Vlem0 {A = C} (idRen {Γ = Γ}) k) k)
                     (C-π₂ (C-× (interpCtx Γ) (interpTy C)) (interpTy A)))) ⟩
    C-Λ (C-× (interpCtx Γ) (interpTy C)) (interpTy A) (interpTy B)
      (interpTm t C.∘
        C-pair ((interpTms (W₁Tms {A = C} (varify (idRen {Γ = Γ})))) C.∘
                 (C-π₁ (C-× (interpCtx Γ) (interpTy C))  (interpTy A)))
               (C-π₂ (C-× (interpCtx Γ) (interpTy C)) (interpTy A)))
      ≡⟨ C-Λnat₁ (C-× (interpCtx Γ) (interpTy C)) (interpCtx Γ) (interpTy A) (interpTy B)
           (interpTms (W₁Tms {A = C} (idTms {Γ}))) (interpTm t) ⟩
    (C-Λ (interpCtx Γ) (interpTy A) (interpTy B) (interpTm t) C.∘
       interpTms (W₁Tms {A = C} (idTms {Γ})))
      ≡⟨ {!λ k → !} ⟩
    (C-Λ (interpCtx Γ) (interpTy A) (interpTy B) (interpTm t) C.∘
       C-π₁ (interpCtx Γ) (interpTy C))
      ∎
  interpW₁Tm {B = C} (App {Γ} {A} {B} t s) =
    C-App (C-× (interpCtx Γ) (interpTy C)) (interpTy A)
      (interpTy B) (interpTm (W₁Tm {B = C} t)) (interpTm (W₁Tm {B = C} s))
      ≡⟨ (λ k →
            C-App (C-× (interpCtx Γ) (interpTy C)) (interpTy A) (interpTy B)
              (interpW₁Tm {B = C} t k) (interpW₁Tm {B = C} s k)) ⟩
    C-App (C-× (interpCtx Γ) (interpTy C)) (interpTy A) (interpTy B)
      (interpTm t C.∘ C-π₁ (interpCtx Γ) (interpTy C))
      (interpTm s C.∘ C-π₁ (interpCtx Γ) (interpTy C))
      ≡⟨ App∘ (interpTm t) (interpTm s) (C-π₁ (interpCtx Γ) (interpTy C)) ⁻¹ ⟩
    (C-App (interpCtx Γ) (interpTy A) (interpTy B) (interpTm t) (interpTm s)
       C.∘ C-π₁ (interpCtx Γ) (interpTy C))
      ∎
  interpW₁Tm {Γ} {A} {B} (t [ σ ]) =
    interpTm t C.∘ interpTms (W₁Tms {A = B} σ)
      ≡⟨ ap (interpTm t C.∘_) (interpW₁Tms σ) ⟩
    interpTm t C.∘ (interpTms σ C.∘ C-π₁ (interpCtx Γ) (interpTy B))
      ≡⟨ C.⋆Assoc (C-π₁ (interpCtx Γ) (interpTy B)) (interpTms σ) (interpTm t) ⟩
    (interpTm t C.∘ interpTms σ) C.∘ C-π₁ (interpCtx Γ) (interpTy B)
      ∎
  interpW₁Tm {Γ} {A} {B} (Zv[] σ t i) j =
    isSet→SquareP (λ i j → isSet𝒞Hom)
      (interpW₁Tm {B = B} (V Zv [ σ ⊕ t ]))
      (interpW₁Tm t)
      (C-π₂β (interpTms (W₁Tms σ)) (interpTm (W₁Tm {B = B} t)))
      (λ k → C-π₂β (interpTms σ) (interpTm t) k C.∘
         C-π₁ (interpCtx Γ) (interpTy B)) i j
  interpW₁Tm {Γ} {A} {B} (Sv[] v σ t i) j =
    isSet→SquareP (λ i j → isSet𝒞Hom)
      (interpW₁Tm {B = B} (V (Sv v) [ σ ⊕ t ]))
      (interpW₁Tm {B = B} (V v [ σ ]))
      (λ k → interpTm (W₁Tm {B = B} (Sv[] v σ t k)))
      (λ k → (interpTm (Sv[] v σ t k) C.∘ C-π₁ (interpCtx Γ) (interpTy B))) i j
  interpW₁Tm (Lam[] σ t i) j = {!!}
  interpW₁Tm (App[] σ t s i) j = {!!}
  interpW₁Tm ([][] t σ τ i) j = {!!}
  interpW₁Tm (β t s i) j = {!!}
  interpW₁Tm (η t i) j = {!!}
  interpW₁Tm {Γ} {A} {B} (isSetTm t s p q i j) =
    isSet→SquareP
      (λ i j →
        isSet→isGroupoid isSet𝒞Hom
          (interpTm (W₁Tm {B = B} (isSetTm t s p q i j)))
          ((interpTm (isSetTm t s p q i j) C.∘ C-π₁ (interpCtx Γ) (interpTy B))))
      (λ k → interpW₁Tm (p k))
      (λ k → interpW₁Tm (q k))
      (λ k → interpW₁Tm t)
      (λ k → interpW₁Tm s) i j

  interpW₁Tms {Γ} {Δ} {A} ! = C-!η (C-! C.∘ C-π₁ (interpCtx Γ) (interpTy A)) ⁻¹
  interpW₁Tms {Γ} {Δ} {A} (σ ⊕ t) =
    C-pair (interpTms (W₁Tms σ)) (interpTm (W₁Tm {B = A} t))
      ≡⟨ (λ k → C-pair (interpW₁Tms {A = A} σ k) (interpW₁Tm {B = A} t k)) ⟩
    C-pair (interpTms σ C.∘ C-π₁ (interpCtx Γ) (interpTy A))
           (interpTm t C.∘ C-π₁ (interpCtx Γ) (interpTy A))
      ≡⟨ π∘ (interpTms σ) (interpTm t) (C-π₁ (interpCtx Γ) (interpTy A)) ⁻¹ ⟩
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
    C-pair (interpTms (varify (W₁Ren {A = A} (idRen {Γ})))) (C-π₂ (interpCtx Γ) (interpTy A))
      ≡⟨ (λ k → C-pair (interpTms (Vlem0 {A = A} (idRen {Γ}) k)) (C-π₂ (interpCtx Γ) (interpTy A))) ⟩
    C-pair (interpTms (W₁Tms {A = A} (idTms {Γ}))) (C-π₂ (interpCtx Γ) (interpTy A))
      ≡⟨ (λ k → C-pair (interpW₁Tms {A = A} (idTms {Γ}) k) (C-π₂ (interpCtx Γ) (interpTy A))) ⟩
    C-pair (interpTms (idTms {Γ}) C.∘ C-π₁ (interpCtx Γ) (interpTy A))
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

  interpret : Functor SYN 𝒞
  interpret .F-ob Γ = interpCtx Γ
  interpret .F-hom = interpTms
  interpret .F-id {Γ} = interpId {Γ}
  interpret .F-seq σ τ = interp∘Tms τ σ

module _ where
  open Precategory
  open Functor
  open PShCartesian REN

  semanticBase : Char → ob (PSh REN)
  semanticBase c = TMS (∅ ⊹ Base c)

  open Eliminator (PSh REN) ⦃ PShCat ⦄ semanticBase

  SEM : Ctx → ob (PSh REN)
  SEM Γ = interpCtx Γ

  open SampleSyn

  test1 = SEM (∅ ⊹ (ChurchType (Base 'A'))) .F-ob ∅
  test2 = SEM (∅ ⊹ (ChurchType (Base 'A'))) .F-hom {∅} idRen

module _ where
  open NatTrans
  open Precategory (PSh REN)
  open PShCartesian REN
  open Eliminator (PSh REN) ⦃ PShCat ⦄ semanticBase

  qTMS : (Γ : Ctx) → Hom[ SEM Γ , TMS Γ ]
  uTMS : (Γ : Ctx) → Hom[ TMS Γ , SEM Γ ]
  
  qTMS ∅ .N-ob _ _ = !
  qTMS ∅ .N-hom σ = refl
  qTMS (Γ ⊹ Base c) .N-ob Δ (MS , ! ⊕ M) = N-ob (qTMS Γ) Δ MS ⊕ M
  qTMS (Γ ⊹ (A ⇒ B)) .N-ob Δ (MS , f) =
    N-ob (qTMS Γ) Δ MS ⊕ {!!}
  qTMS (Γ ⊹ A) .N-hom = {!!}

  uTMS ∅ .N-ob _ _ = lift tt
  uTMS ∅ .N-hom σ = refl
  uTMS (Γ ⊹ Base x) .N-ob Δ (σ ⊕ t) = N-ob (uTMS Γ) Δ σ , ! ⊕ t
  uTMS (Γ ⊹ (A ⇒ B)) .N-ob Δ (σ ⊕ t) =
    N-ob (uTMS Γ) Δ σ ,
      natTrans
        (λ Γ → λ {(σ , x) → snd (N-ob (uTMS (∅ ⊹ B)) Γ {!!}) })
        {!!} 
  uTMS (Γ ⊹ A) .N-hom = {!!}
  

{-module _ where
  open SampleSyn
  open Precategory
  open Functor
  open NatTrans
  open PShCartesian SYN
  module C = Precategory (PSh SYN)

  base : Char → C.ob
  base c = よ (∅ ⊹ (Base c))
  
  open Eliminator (PSh SYN) ⦃ PShCat ⦄ base

  test1 = interpTy (ChurchType (Base 'A'))
  test2 = interpTm (ChurchTwo {∅} {Base 'A'}) .N-ob ∅-}
