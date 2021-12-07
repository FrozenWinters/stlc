{-# OPTIONS --cubical #-}

module cart where

open import contextual
open import ccc

open import Cubical.Categories.Category

record Cartesian {ℓ₁ ℓ₂} (𝒞 : Precategory ℓ₁ ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  open Precategory 𝒞 renaming (_∘_ to _⊚_; id to 𝒾𝒹)
  field
    -- Terminal object
    C-1 : ob
    C-! : {A : ob} → Hom[ A , C-1 ]
    C-!η : {A : ob} (f : Hom[ A , C-1 ]) → f ≡ C-!

    -- Products
    C-× : ob → ob → ob
    C-pair : {A B C : ob} → Hom[ A , B ] → Hom[ A , C ] → Hom[ A , C-× B C ]
    C-π₁ : (A B : ob) → Hom[ C-× A B , A ]
    C-π₂ : (A B : ob) → Hom[ C-× A B , B ]
    C-π₁β : {A B C : ob} (f : Hom[ A , B ]) (g : Hom[ A , C ]) →
      C-π₁ B C ⊚ C-pair f g ≡ f
    C-π₂β : {A B C : ob} (f : Hom[ A , B ]) (g : Hom[ A , C ]) →
      C-π₂ B C ⊚ C-pair f g ≡ g
    C-πη : (A B C : ob) (f : Hom[ A , C-× B C ]) →
      C-pair (C-π₁ B C ⊚ f) (C-π₂ B C ⊚ f) ≡ f

  field
    -- Exponentials
    C-⇒ : ob → ob → ob
    C-Λ : (A B C : ob) → Hom[ C-× A B , C ] → Hom[ A , C-⇒ B C ]
    C-App : (A B C : ob) → Hom[ A , C-⇒ B C ] → Hom[ A , B ] → Hom[ A , C ]

  field
    C-Λnat : (A A' B C : ob) (f : Hom[ A , A' ]) (g : Hom[ C-× A' B , C ]) →
      C-Λ A B C (g ⊚ C-pair (f ⊚ C-π₁ A B) (C-π₂ A B)) ≡ (C-Λ A' B C g) ⊚ f
    C-Appβ : (A B C : ob) (f : Hom[ C-× A B , C ]) (g : Hom[ A , B ]) →
      C-App A B C (C-Λ A B C f) g ≡ f ⊚ (C-pair (𝒾𝒹 A) g)
    C-Appη : (A B C : ob) (f : Hom[ A , C-⇒ B C ]) →
      f ≡ C-Λ A B C (C-App (C-× A B) B C (f ⊚ C-π₁ A B) (C-π₂ A B))

  π∘ : {A B C D : ob} (f : Hom[ B , C ]) (g : Hom[ B , D ]) (h : Hom[ A , B ]) →
    (C-pair f g) ⊚ h ≡ (C-pair (f ⊚ h) (g ⊚ h))
  π∘ {A} {B} {C} {D} f g h =
    C-πη A C D (C-pair f g ⊚ h) ⁻¹
    ∙ (λ k → C-pair (lem1 k) (lem2 k)) where
      lem1 : C-π₁ C D ⊚ ((C-pair f g) ⊚ h) ≡ f ⊚ h
      lem1 =
        ⋆Assoc h (C-pair f g) (C-π₁ C D)
        ∙ ap (_⊚ h) (C-π₁β f g)

      lem2 : C-π₂ C D ⊚ ((C-pair f g) ⊚ h) ≡ g ⊚ h
      lem2 =
        ⋆Assoc h (C-pair f g) (C-π₂ C D)
        ∙ ap (_⊚ h) (C-π₂β f g)

-- Every cartesian closed category can be made into a CCC

module CartToCCC {ℓ₁ ℓ₂} (𝒞 : Precategory ℓ₁ ℓ₂)
       ⦃ C-cat : isCategory 𝒞 ⦄ ⦃ C-cart : Cartesian 𝒞 ⦄ where

  open Precategory 𝒞 renaming (id to 𝒾𝒹; _∘_ to _𝒞∘_)
  open Cartesian C-cart

  Ty = ob
  Ctx = 𝐶𝑡𝑥 Ty

  ⇓Ctx : Ctx → ob
  ⇓Ctx ∅ = C-1
  ⇓Ctx (Γ ⊹ A) = C-× (⇓Ctx Γ) A

  _⇒_ = C-⇒

  Tm : Ctx → Ty → Type ℓ₂
  Tm Γ A = Hom[ ⇓Ctx Γ , A ]

  Tms = 𝑇𝑚𝑠 Tm

  ⇓Tms : {Γ Δ : Ctx} → Tms Γ Δ → Hom[ ⇓Ctx Γ , ⇓Ctx Δ ]
  ⇓Tms ! = C-!
  ⇓Tms (σ ⊕ t) = C-pair (⇓Tms σ) t

  Lam : {Γ : Ctx} {A B : Ty} → Tm (Γ ⊹ A) B → Tm Γ (A ⇒ B)
  Lam {Γ} {A} {B} = C-Λ (⇓Ctx Γ) A B

  App : {Γ : Ctx} {A B : Ty} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  App {Γ} {A} {B} = C-App (⇓Ctx Γ) A B

  infixl 30 _[_]
  _[_] : {Γ Δ : Ctx} {A : Ty} → Tm Δ A → Tms Γ Δ → Tm Γ A
  t [ σ ] = t 𝒞∘ (⇓Tms σ)

  infixl 20 _∘Tms_
  _∘Tms_ : {Γ Δ Σ : Ctx} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
  σ ∘Tms τ = map𝑇𝑚𝑠 _[ τ ] σ

  ⇓∘Tms : {Γ Δ Σ : Ctx} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
    ⇓Tms (σ ∘Tms τ) ≡ ⇓Tms σ 𝒞∘ ⇓Tms τ
  ⇓∘Tms ! τ = C-!η (C-! 𝒞∘ ⇓Tms τ) ⁻¹
  ⇓∘Tms (σ ⊕ t) τ =
    C-pair (⇓Tms (σ ∘Tms τ)) (t 𝒞∘ ⇓Tms τ)
      ≡⟨ (λ i → C-pair (⇓∘Tms σ τ i) (t 𝒞∘ ⇓Tms τ)) ⟩
    C-pair (⇓Tms σ 𝒞∘ ⇓Tms τ) (t 𝒞∘ ⇓Tms τ)
      ≡⟨ π∘ (⇓Tms σ) t (⇓Tms τ) ⁻¹ ⟩
    C-pair (⇓Tms σ) t 𝒞∘ ⇓Tms τ
      ∎

  W₁Tm : (Γ : Ctx) (A : Ty) {B : Ty} → Tm Γ B → Tm (Γ ⊹ A) B
  W₁Tm Γ A t = t 𝒞∘ C-π₁ (⇓Ctx Γ) A

  W₁Tms : (Γ : Ctx) {Δ : Ctx} (A : Ty) → Tms Γ Δ → Tms (Γ ⊹ A) Δ
  W₁Tms Γ A σ = map𝑇𝑚𝑠 (W₁Tm Γ A) σ

  W₁Lem1 : {Γ Δ : Ctx} {A : Ty} (σ : Tms Γ Δ) →
    ⇓Tms (W₁Tms Γ A σ) ≡ ⇓Tms σ 𝒞∘ C-π₁ (⇓Ctx Γ) A
  W₁Lem1 {Γ} {Δ} {A} ! = C-!η (C-! 𝒞∘ C-π₁ (⇓Ctx Γ) A) ⁻¹
  W₁Lem1 {Γ} {Δ} {A} (σ ⊕ t) =
    C-pair (⇓Tms (map𝑇𝑚𝑠 (W₁Tm Γ A) σ)) (W₁Tm Γ A t)
      ≡⟨ (λ i → C-pair (W₁Lem1 σ i) (W₁Tm Γ A t)) ⟩
    C-pair (⇓Tms σ 𝒞∘ C-π₁ (⇓Ctx Γ) A) (t 𝒞∘ C-π₁ (⇓Ctx Γ) A)
      ≡⟨ π∘ (⇓Tms σ) t (C-π₁ (⇓Ctx Γ) A) ⁻¹ ⟩
    (C-pair (⇓Tms σ) t 𝒞∘ C-π₁ (⇓Ctx Γ) A)
      ∎

  W₁Lem2 : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) (s : Tm Γ A) →
    W₁Tm Δ A t [ σ ⊕ s ] ≡ t [ σ ]
  W₁Lem2 {Γ} {Δ} {A} t σ s =
    (t 𝒞∘ (C-π₁ (⇓Ctx Δ) A)) 𝒞∘ (C-pair (⇓Tms σ) s)
      ≡⟨ ⋆Assoc (C-pair (⇓Tms σ) s) (C-π₁ (⇓Ctx Δ) A) t ⁻¹ ⟩
    t 𝒞∘ ((C-π₁ (⇓Ctx Δ) A) 𝒞∘ (C-pair (⇓Tms σ) s))
      ≡⟨ ap (t 𝒞∘_) (C-π₁β (⇓Tms σ) s) ⟩
    t [ σ ]
      ∎

  W₁Lem3 : {Γ Δ Σ : Ctx} {A : Ty} (τ : Tms Δ Σ) (σ : Tms Γ Δ) (s : Tm Γ A) →
    W₁Tms Δ A τ ∘Tms (σ ⊕ s) ≡ τ ∘Tms σ
  W₁Lem3 ! σ s = refl
  W₁Lem3 {Γ} {Δ} {Σ} {A} (τ ⊕ t) σ s i = W₁Lem3 τ σ s i ⊕ W₁Lem2 t σ s i

  idTms : (Γ : Ctx) → Tms Γ Γ
  idTms ∅ = !
  idTms (Γ ⊹ A) = W₁Tms Γ A (idTms Γ) ⊕ C-π₂ (⇓Ctx Γ) A

  ⇓idTms : (Γ : Ctx) → ⇓Tms (idTms Γ) ≡ 𝒾𝒹 (⇓Ctx Γ)
  ⇓idTms ∅ = C-!η (𝒾𝒹 C-1) ⁻¹
  ⇓idTms (Γ ⊹ A) =
    C-pair (⇓Tms (W₁Tms Γ A (idTms Γ))) (C-π₂ (⇓Ctx Γ) A)
      ≡⟨ (λ i → C-pair (W₁Lem1 (idTms Γ) i) (C-π₂ (⇓Ctx Γ) A)) ⟩
    C-pair (⇓Tms (idTms Γ) 𝒞∘ C-π₁ (⇓Ctx Γ) A) (C-π₂ (⇓Ctx Γ) A)
      ≡⟨ (λ i → C-pair (⇓idTms Γ i 𝒞∘ C-π₁ (⇓Ctx Γ) A) (C-π₂ (⇓Ctx Γ) A)) ⟩
    C-pair (𝒾𝒹 (⇓Ctx Γ) 𝒞∘ C-π₁ (⇓Ctx Γ) A) (C-π₂ (⇓Ctx Γ) A)
      ≡⟨ (λ i → C-pair (⋆IdR (⋆IdL (C-π₁ (⇓Ctx Γ) A) (~ i)) i) (⋆IdL (C-π₂ (⇓Ctx Γ) A) (~ i))) ⟩
    C-pair (C-π₁ (⇓Ctx Γ) A 𝒞∘ 𝒾𝒹 (C-× (⇓Ctx Γ) A)) (C-π₂ (⇓Ctx Γ) A 𝒞∘ 𝒾𝒹 (C-× (⇓Ctx Γ) A))
      ≡⟨ C-πη (C-× (⇓Ctx Γ) A) (⇓Ctx Γ) A (𝒾𝒹 (C-× (⇓Ctx Γ) A)) ⟩
    𝒾𝒹 (C-× (⇓Ctx Γ) A)
      ∎

  ∘TmsIdL : {Γ Δ : Ctx} (σ : Tms Γ Δ) → idTms Δ ∘Tms σ ≡ σ
  ∘TmsIdL ! = refl
  ∘TmsIdL {Γ} {Δ ⊹ A} (σ ⊕ t) =
    W₁Tms Δ A (idTms Δ) ∘Tms (σ ⊕ t) ⊕ (C-π₂ (⇓Ctx Δ) A 𝒞∘ (C-pair (⇓Tms σ) t))
      ≡⟨ (λ i → W₁Lem3 (idTms Δ) σ t i ⊕ C-π₂β (⇓Tms σ) t i) ⟩
    idTms Δ ∘Tms σ ⊕ t
      ≡⟨ ap (_⊕ t) (∘TmsIdL σ) ⟩
    σ ⊕ t
      ∎

  [id] : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → t [ idTms Γ ] ≡ t
  [id] {Γ} t =
    t 𝒞∘ (⇓Tms (idTms Γ))
      ≡⟨ ap (t 𝒞∘_) (⇓idTms Γ) ⟩
    t 𝒞∘ 𝒾𝒹 (⇓Ctx Γ)
      ≡⟨ ⋆IdL t ⟩
    t
      ∎

  [][] : {Γ Δ Σ : Ctx} {A : Ty} (t : Tm Σ A) (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
    t [ σ ] [ τ ] ≡ t [ σ ∘Tms τ ]
  [][] t σ τ =
    (t 𝒞∘ ⇓Tms σ) 𝒞∘ ⇓Tms τ
      ≡⟨ ⋆Assoc (⇓Tms τ) (⇓Tms σ) t ⁻¹ ⟩
    t 𝒞∘ (⇓Tms σ 𝒞∘ ⇓Tms τ)
      ≡⟨ ap (t 𝒞∘_ ) (⇓∘Tms σ τ ⁻¹) ⟩
    t [ σ ∘Tms τ ]
      ∎

  𝑧Tm : {Γ : Ctx} {A : Ty} → Tm (Γ ⊹ A) A
  𝑧Tm {Γ} {A} = C-π₂ (⇓Ctx Γ) A

  πTms : {Γ : Ctx} {A : Ty} → Tms (Γ ⊹ A) Γ
  πTms {Γ} {A} = W₁Tms Γ A (idTms Γ)

  ⇓πTms : {Γ : Ctx} {A : Ty} →
    ⇓Tms {Δ = Γ} πTms ≡ C-π₁ (⇓Ctx Γ) A
  ⇓πTms {Γ} {A} =
    ⇓Tms (W₁Tms Γ A (idTms Γ))
      ≡⟨ W₁Lem1  (idTms Γ) ⟩
    ⇓Tms (idTms Γ) 𝒞∘ C-π₁ (⇓Ctx Γ) A
      ≡⟨ ap (_𝒞∘ C-π₁ (⇓Ctx Γ) A) (⇓idTms Γ) ⟩
    𝒾𝒹 (⇓Ctx Γ) 𝒞∘ C-π₁ (⇓Ctx Γ) A
      ≡⟨ ⋆IdR (C-π₁ (⇓Ctx Γ) A) ⟩
    C-π₁ (⇓Ctx Γ) A
      ∎

  ΛnatTm : {Γ Δ : Ctx} {A B : Ty} (t : Tm (Δ ⊹ A) B) (σ : Tms Γ Δ) →
    C-Λ (⇓Ctx Δ) A B t [ σ ] ≡  C-Λ (⇓Ctx Γ) A B ( t [ (σ ∘Tms πTms) ⊕ 𝑧Tm {Γ} ])
  ΛnatTm {Γ} {Δ} {A} {B} t σ =
    C-Λ (⇓Ctx Δ) A B t [ σ ]
      ≡⟨ C-Λnat (⇓Ctx Γ) (⇓Ctx Δ) A B (⇓Tms σ) t ⁻¹ ⟩
    C-Λ (⇓Ctx Γ) A B (t 𝒞∘ C-pair (⇓Tms σ 𝒞∘ C-π₁ (⇓Ctx Γ) A) (𝑧Tm {Γ}))
      ≡⟨ (λ i → C-Λ (⇓Ctx Γ) A B (t 𝒞∘ C-pair (⇓Tms σ 𝒞∘ ⇓πTms {Γ} (~ i)) (𝑧Tm {Γ}))) ⟩
    C-Λ (⇓Ctx Γ) A B (t 𝒞∘ C-pair (⇓Tms σ 𝒞∘ ⇓Tms {Δ = Γ} πTms) (𝑧Tm {Γ}))
      ≡⟨ (λ i → C-Λ (⇓Ctx Γ) A B (t 𝒞∘ C-pair (⇓∘Tms σ πTms (~ i)) (𝑧Tm {Γ}))) ⟩
    C-Λ (⇓Ctx Γ) A B (t [ (σ ∘Tms πTms) ⊕ (𝑧Tm {Γ}) ])
      ∎

  𝑎𝑝𝑝βTm : {Γ : Ctx} {A B : Ty} (t : Tm (Γ ⊹ A) B) (s : Tm Γ A) →
    C-App (⇓Ctx Γ) A B (C-Λ (⇓Ctx Γ) A B t) s ≡ t [ idTms Γ ⊕ s ]
  𝑎𝑝𝑝βTm {Γ} {A} {B} t s =
    C-App (⇓Ctx Γ) A B (C-Λ (⇓Ctx Γ) A B t) s
      ≡⟨ C-Appβ (⇓Ctx Γ) A B t s ⟩
    t 𝒞∘ C-pair (𝒾𝒹 (⇓Ctx Γ)) s
      ≡⟨ (λ i → t 𝒞∘ C-pair (⇓idTms Γ (~ i)) s) ⟩
    t [ idTms Γ ⊕ s ]
      ∎

  𝑎𝑝𝑝ηTm : {Γ : Ctx} {A B : Ty} (t : Tm Γ (C-⇒ A B)) →
    t ≡ C-Λ (⇓Ctx Γ) A B (C-App (⇓Ctx (Γ ⊹ A)) A B (t [ πTms {Γ} ]) (𝑧Tm {Γ}))
  𝑎𝑝𝑝ηTm {Γ} {A} {B} t =
    t
      ≡⟨ C-Appη (⇓Ctx Γ) A B t ⟩
    C-Λ (⇓Ctx Γ) A B (C-App (⇓Ctx (Γ ⊹ A)) A B (t 𝒞∘ C-π₁ (⇓Ctx Γ) A) (𝑧Tm {Γ}))
      ≡⟨ (λ i → C-Λ (⇓Ctx Γ) A B (C-App (⇓Ctx (Γ ⊹ A)) A B (t 𝒞∘ ⇓πTms {Γ} (~ i)) (𝑧Tm {Γ}))) ⟩
    C-Λ (⇓Ctx Γ) A B (C-App (⇓Ctx (Γ ⊹ A)) A B (t [ πTms {Γ} ]) (𝑧Tm {Γ}))
      ∎

  ⊚πlem : {Γ Δ : Ctx} {A B : Ty} (t : Hom[ A , B ]) (σ : Tms Γ Δ) (s : Tm Γ A )  →
    (t 𝒞∘ 𝑧Tm {Δ}) [ σ ⊕ s ] ≡ t 𝒞∘ s
  ⊚πlem {Γ} {Δ} {A} t σ s =
    (t 𝒞∘ C-π₂ (⇓Ctx Δ) A) 𝒞∘ C-pair (⇓Tms σ) s
      ≡⟨ ⋆Assoc (C-pair (⇓Tms σ) s) (C-π₂ (⇓Ctx Δ) A) t ⁻¹ ⟩
    t 𝒞∘ (C-π₂ (⇓Ctx Δ) A 𝒞∘ C-pair (⇓Tms σ) s)
      ≡⟨ ap (t 𝒞∘_) (C-π₂β (⇓Tms σ) s) ⟩
    t 𝒞∘ s
      ∎

module Enveloping {ℓ₁ ℓ₂} (𝒞 : Precategory ℓ₁ ℓ₂)
       ⦃ C-cat : isCategory 𝒞 ⦄ ⦃ C-cart : Cartesian 𝒞 ⦄ where
  open CartToCCC 𝒞

  module _ where
    open Contextual

    envCC : Contextual ℓ₁ ℓ₂
    ty envCC = Ty
    tm envCC = Tm
    _⟦_⟧ envCC = _[_]
    𝒾𝒹 envCC = idTms
    𝒾𝒹L envCC = ∘TmsIdL
    𝒾𝒹⟦⟧ envCC {Γ} = [id] {Γ}
    ⟦⟧⟦⟧ envCC = [][]
    Contextual.isSetTm envCC = isSetHom C-cat

    open CCC

    envCCC : CCC envCC
    _⇛_ envCCC = _⇒_
    Λ envCCC {Γ} = Lam {Γ}
    𝑎𝑝𝑝 envCCC {Γ} = App {Γ}
    Λnat envCCC = ΛnatTm
    𝑎𝑝𝑝β envCCC {Γ} = 𝑎𝑝𝑝βTm {Γ}
    𝑎𝑝𝑝η envCCC {Γ} = 𝑎𝑝𝑝ηTm {Γ}

  ⇓EnvCtx = ⇓Ctx
  ⇓EnvTms = ⇓Tms
  ⇓Envπ = ⇓πTms

  open Precategory 𝒞 renaming (_∘_ to _𝒞∘_)
  open Cartesian C-cart
  open Contextual envCC
  open CCC envCCC

  infixl 30 _×tm_
  _×tm_ : {Γ Δ : ctx} {A B : ty} → tms Γ Δ → Hom[ A , B ] → tms (Γ ⊹ A) (Δ ⊹ B)
  _×tm_ {Γ} σ t = σ ⊚ π ⊕ (t 𝒞∘ (𝑧 {Γ}))

  ×tmLem1 : {Γ Δ Σ : ctx} {A B : ty} (σ : tms Δ Σ) (t : Hom[ A , B ])
    (τ : tms Γ Δ) (s : tm Γ A ) →
    (σ ×tm t) ⊚ (τ ⊕ s) ≡ (σ ⊚ τ) ⊕ (t 𝒞∘ s)
  ×tmLem1 {Γ} {Δ} σ t τ s =
    σ ⊚ π ⊕ (t 𝒞∘ 𝑧 {Δ}) ⊚ (τ ⊕ s)
      ≡⟨ ⊕⊚ (σ ⊚ π) (t 𝒞∘ 𝑧 {Δ}) (τ ⊕ s) ⟩
    σ ⊚ π ⊚ (τ ⊕ s) ⊕ (t 𝒞∘ 𝑧 {Δ}) ⟦ τ ⊕ s ⟧
      ≡⟨ (λ i → ⊚Assoc σ π (τ ⊕ s) i ⊕ ⊚πlem t τ s i) ⟩
    σ ⊚ (π ⊚ (τ ⊕ s)) ⊕ (t 𝒞∘ s)
      ≡⟨ (λ i → σ ⊚ (πβ (τ ⊕ s) i) ⊕ (t 𝒞∘ s)) ⟩
    σ ⊚ τ ⊕ (t 𝒞∘ s)
      ∎

  ×tmLem2 : {Γ Δ Σ : ctx} {A B C : ty} (σ : tms Δ Σ) (t : Hom[ B , C ])
    (τ : tms Γ Δ) (s : Hom[ A , B ]) →
    (σ ×tm t) ⊚ (τ ×tm s) ≡ (σ ⊚ τ) ×tm (t 𝒞∘ s)
  ×tmLem2 {Γ} {Δ} σ t τ s =
    (σ ×tm t) ⊚ (τ ⊚ π ⊕ (s 𝒞∘ 𝑧 {Γ}))
      ≡⟨ ×tmLem1 σ t (τ ⊚ π) (s 𝒞∘ 𝑧 {Γ}) ⟩
    σ ⊚ (τ ⊚ π) ⊕ (t 𝒞∘ (s 𝒞∘ 𝑧 {Γ}))
      ≡⟨ (λ i → ⊚Assoc σ τ π (~ i) ⊕ ⋆Assoc (𝑧 {Γ}) s t i) ⟩
    (σ ⊚ τ) ×tm (t 𝒞∘ s)
      ∎

  ×IndLem : {Γ Δ : ctx} {A B : ty} (σ : tms Γ Δ) (s : Hom[ A , B ]) →
    ⇓EnvTms (σ ×tm s) ≡ C-pair (⇓Tms σ 𝒞∘ C-π₁ (⇓Ctx Γ) A) (s 𝒞∘ C-π₂ (⇓Ctx Γ) A)
  ×IndLem {Γ} σ s =
    C-pair (⇓Tms (σ ⊚ π)) (s 𝒞∘ C-π₂ _ _)
      ≡⟨ (λ i → C-pair (⇓∘Tms σ π i) (s 𝒞∘ C-π₂ _ _)) ⟩
    C-pair (⇓Tms σ 𝒞∘ ⇓Tms (π {Γ})) (s 𝒞∘ C-π₂ _ _)
      ≡⟨ (λ i → C-pair (⇓Tms σ 𝒞∘ ⇓πTms {Γ} i) (s 𝒞∘ C-π₂ _ _)) ⟩
    C-pair (⇓Tms σ 𝒞∘ C-π₁ _ _) (s 𝒞∘ C-π₂ _ _)
      ∎

  module _ {ℓ} {𝑡𝑦 : Type ℓ} where
    𝑐𝑡𝑥 = 𝐶𝑡𝑥 𝑡𝑦

    TypeFamily = 𝑡𝑦 → ty
    ContextFamily = 𝑐𝑡𝑥 → ctx

    plurify : TypeFamily → ContextFamily
    plurify 𝒫 = map𝐶𝑡𝑥 𝒫

    HomFamily : (𝒫 𝒬 : TypeFamily) → Type _
    HomFamily 𝒫 𝒬 = (A : 𝑡𝑦) → Hom[ 𝒫 A , 𝒬 A ]

    weaveHom : {𝒫 𝒬 : TypeFamily} (𝒜 : HomFamily 𝒫 𝒬) →
      (Γ : 𝑐𝑡𝑥) → tms (plurify 𝒫 Γ) (plurify 𝒬 Γ)
    weaveHom 𝒜 ∅ = !
    weaveHom 𝒜 (Γ ⊹ A) = weaveHom 𝒜 Γ ×tm 𝒜 A
  

{-
  ⇓ctx = ⇓Ctx
  ⇓tms = ⇓Tms
  ⇓∘tms = ⇓∘Tms
  ⇓idtms = ⇓idTms

  open Contextual

  envCC : Contextual ℓ₁ ℓ₂
  ty envCC = Ty
  tm envCC = Tm
  _⟦_⟧ envCC = _[_]
  𝒾𝒹 envCC = idTms
  𝒾𝒹L envCC = ∘TmsIdL
  𝒾𝒹⟦⟧ envCC {Γ} = [id] {Γ}
  ⟦⟧⟦⟧ envCC = [][]
  Contextual.isSetTm envCC = isSetHom C-cat

  private
    module C = Contextual envCC

  πη : {Γ : C.ctx} {A : C.ty} →
    C.π ≡ C.W₁tms A (C.𝒾𝒹 Γ)
  πη {Γ} {A} = C.𝒾𝒹L (C.π {Γ}) ⁻¹

  ⇓π : {Γ : C.ctx} {A : C.ty} →
    ⇓tms (C.π {Γ} {A}) ≡ C-π₁ (⇓ctx Γ) A
  ⇓π {∅} {A} = C-!η (C-π₁ C-1 A) ⁻¹
  ⇓π {Γ ⊹ B} {A} =
    C-pair
      (⇓Tms (W₁Tms (Γ ⊹ B) A (C.π {Γ} {B})))
      (C-π₂ (⇓Ctx Γ) B 𝒞∘ C-π₁ (C-× (⇓Ctx Γ) B) A)
      ≡⟨ (λ i → C-pair
        (W₁Lem1 (C.π {Γ} {B}) i)
        (C-π₂ (⇓Ctx Γ) B 𝒞∘ C-π₁ (C-× (⇓Ctx Γ) B) A)) ⟩
    C-pair
      (⇓Tms (C.π {Γ}) 𝒞∘ C-π₁ (C-× (⇓Ctx Γ) B) A)
      (C-π₂ (⇓Ctx Γ) B 𝒞∘ C-π₁ (C-× (⇓Ctx Γ) B) A)
      ≡⟨ (λ i → C-pair
        (⇓π {Γ} {B} i 𝒞∘ C-π₁ (C-× (⇓Ctx Γ) B) A)
        (C-π₂ (⇓Ctx Γ) B 𝒞∘ C-π₁ (C-× (⇓Ctx Γ) B) A)) ⟩
    C-pair
      (C-π₁ (⇓Ctx Γ) B 𝒞∘ C-π₁ (C-× (⇓Ctx Γ) B) A)
      (C-π₂ (⇓Ctx Γ) B 𝒞∘ C-π₁ (C-× (⇓Ctx Γ) B) A)
      ≡⟨ C-πη (⇓Ctx (Γ ⊹ B ⊹ A)) (⇓Ctx Γ) B (C-π₁ (C-× (⇓Ctx Γ) B) A) ⟩
    C-π₁ (C-× (⇓Ctx Γ) B) A
      ∎

  open CCC

  envCCC : CCC envCC
  _⇛_ envCCC = C-⇒
  Λ envCCC {Γ} {A} {B} = C-Λ (⇓Ctx Γ) A B
  𝑎𝑝𝑝 envCCC {Γ} {A} {B} = C-App (⇓Ctx Γ) A B
  Λnat envCCC {Γ} {Δ} {A} {B} t σ = ΛnatTm t σ
  𝑎𝑝𝑝β envCCC {Γ} = 𝑎𝑝𝑝βTm {Γ}
  𝑎𝑝𝑝η envCCC {Γ} = 𝑎𝑝𝑝ηTm {Γ}
-}
