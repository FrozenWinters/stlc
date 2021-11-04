{-# OPTIONS --cubical #-}

module cartesian3 where

open import contextual
open import cartesian2

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

  {-eval : (A B : ob) → Hom[ C-× (C-⇒ A B) A , B ]
  eval A B = C-App (C-× (C-⇒ A B) A) A B (C-π₁ (C-⇒ A B) A) (C-π₂ (C-⇒ A B) A)-}

  field
    C-Λnat : (A A' B C : ob) (f : Hom[ A , A' ]) (g : Hom[ C-× A' B , C ]) →
      C-Λ A B C (g ⊚ C-pair (f ⊚ C-π₁ A B) (C-π₂ A B)) ≡ (C-Λ A' B C g) ⊚ f
    {-C-Λnat₂ : (A B C C' : ob) (f : Hom[ C , C' ]) (g : Hom[ C-× A B , C ]) →
      C-Λ A B C' (f ⊚ g) ≡ C-Λ (C-⇒ B C) B C' (f ⊚ eval B C) ⊚ C-Λ A B C g-}
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

  private
    open Precategory 𝒞 renaming (id to 𝒾𝒹; _∘_ to _𝒞∘_)
    open Cartesian C-cart
    
    Ty = ob
    Ctx = RL Ty

    ⇓Ctx : Ctx → ob
    ⇓Ctx ∅ = C-1
    ⇓Ctx (Γ ⊹ A) = C-× (⇓Ctx Γ) A

    Tm : Ctx → Ty → Type ℓ₂
    Tm Γ A = Hom[ ⇓Ctx Γ , A ]

    Tms = IL Tm

    ⇓Tms : {Γ Δ : Ctx} → Tms Γ Δ → Hom[ ⇓Ctx Γ , ⇓Ctx Δ ]
    ⇓Tms ! = C-!
    ⇓Tms (σ ⊕ t) = C-pair (⇓Tms σ) t

    infixl 30 _[_]
    _[_] : {Γ Δ : Ctx} {A : Ty} → Tm Δ A → Tms Γ Δ → Tm Γ A
    t [ σ ] = t 𝒞∘ (⇓Tms σ)

    infixl 20 _∘Tms_
    _∘Tms_ : {Γ Δ Σ : Ctx} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
    σ ∘Tms τ = mapIL _[ τ ] σ

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
    W₁Tms Γ A σ = mapIL (W₁Tm Γ A) σ

    W₁Lem1 : {Γ Δ : Ctx} {A : Ty} (σ : Tms Γ Δ) →
      ⇓Tms (W₁Tms Γ A σ) ≡ ⇓Tms σ 𝒞∘ C-π₁ (⇓Ctx Γ) A
    W₁Lem1 {Γ} {Δ} {A} ! = C-!η (C-! 𝒞∘ C-π₁ (⇓Ctx Γ) A) ⁻¹
    W₁Lem1 {Γ} {Δ} {A} (σ ⊕ t) =
      C-pair (⇓Tms (mapIL (W₁Tm Γ A) σ)) (W₁Tm Γ A t)
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

    πTm : {Γ : Ctx} {A : Ty} → Tms (Γ ⊹ A) Γ
    πTm {Γ} {A} = W₁Tms Γ A (idTms Γ)

    πTmLem : {Γ : Ctx} {A : Ty} →
      ⇓Tms {Δ = Γ} πTm ≡ C-π₁ (⇓Ctx Γ) A
    πTmLem {Γ} {A} =
      ⇓Tms (W₁Tms Γ A (idTms Γ))
        ≡⟨ W₁Lem1  (idTms Γ) ⟩
      ⇓Tms (idTms Γ) 𝒞∘ C-π₁ (⇓Ctx Γ) A
        ≡⟨ ap (_𝒞∘ C-π₁ (⇓Ctx Γ) A) (⇓idTms Γ) ⟩
      𝒾𝒹 (⇓Ctx Γ) 𝒞∘ C-π₁ (⇓Ctx Γ) A
        ≡⟨ ⋆IdR (C-π₁ (⇓Ctx Γ) A) ⟩
      C-π₁ (⇓Ctx Γ) A
        ∎

    ΛnatTm : {Γ Δ : Ctx} {A B : Ty} (t : Tm (Δ ⊹ A) B) (σ : Tms Γ Δ) →
      C-Λ (⇓Ctx Δ) A B t [ σ ] ≡  C-Λ (⇓Ctx Γ) A B ( t [ (σ ∘Tms πTm) ⊕ 𝑧Tm {Γ} ])
    ΛnatTm {Γ} {Δ} {A} {B} t σ =
      C-Λ (⇓Ctx Δ) A B t [ σ ]
        ≡⟨ C-Λnat (⇓Ctx Γ) (⇓Ctx Δ) A B (⇓Tms σ) t ⁻¹ ⟩
      C-Λ (⇓Ctx Γ) A B (t 𝒞∘ C-pair (⇓Tms σ 𝒞∘ C-π₁ (⇓Ctx Γ) A) (𝑧Tm {Γ}))
        ≡⟨ (λ i → C-Λ (⇓Ctx Γ) A B (t 𝒞∘ C-pair (⇓Tms σ 𝒞∘ πTmLem {Γ} (~ i)) (𝑧Tm {Γ}))) ⟩
      C-Λ (⇓Ctx Γ) A B (t 𝒞∘ C-pair (⇓Tms σ 𝒞∘ ⇓Tms {Δ = Γ} πTm) (𝑧Tm {Γ}))
        ≡⟨ (λ i → C-Λ (⇓Ctx Γ) A B (t 𝒞∘ C-pair (⇓∘Tms σ πTm (~ i)) (𝑧Tm {Γ}))) ⟩
      C-Λ (⇓Ctx Γ) A B (t [ (σ ∘Tms πTm) ⊕ (𝑧Tm {Γ}) ])
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
      t ≡ C-Λ (⇓Ctx Γ) A B (C-App (⇓Ctx (Γ ⊹ A)) A B (t [ πTm {Γ} ]) (𝑧Tm {Γ}))
    𝑎𝑝𝑝ηTm {Γ} {A} {B} t =
      t
        ≡⟨ C-Appη (⇓Ctx Γ) A B t ⟩
      C-Λ (⇓Ctx Γ) A B (C-App (⇓Ctx (Γ ⊹ A)) A B (t 𝒞∘ C-π₁ (⇓Ctx Γ) A) (𝑧Tm {Γ}))
        ≡⟨ (λ i → C-Λ (⇓Ctx Γ) A B (C-App (⇓Ctx (Γ ⊹ A)) A B (t 𝒞∘ πTmLem {Γ} (~ i)) (𝑧Tm {Γ}))) ⟩
      C-Λ (⇓Ctx Γ) A B (C-App (⇓Ctx (Γ ⊹ A)) A B (t [ πTm {Γ} ]) (𝑧Tm {Γ}))
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

  ⇓ctx = ⇓Ctx
  ⇓tms = ⇓Tms
  ⇓∘tms = ⇓∘Tms

  {-W₁tm = W₁Tm
  W₁tms = W₁Tms-}

  open Contextual

  ambCC : Contextual ℓ₁ ℓ₂
  ty ambCC = Ty
  tm ambCC = Tm
  _⟦_⟧ ambCC = _[_]
  𝒾𝒹 ambCC = idTms
  𝒾𝒹L ambCC = ∘TmsIdL
  𝒾𝒹⟦⟧ ambCC {Γ} = [id] {Γ}
  ⟦⟧⟦⟧ ambCC = [][]
  Contextual.isSetTm ambCC = isSetHom C-cat

  --open Contextual ambCC
  private
    module C = Contextual ambCC

  W₁tm : {Γ : C.ctx} (A : C.ty) {B : C.ty} → C.tm Γ B → C.tm (Γ ⊹ A) B
  W₁tm {Γ} A t = t C.⟦ C.π {Γ} ⟧

  W₁tms : {Γ Δ : C.ctx} (A : C.ty) → C.tms Γ Δ → C.tms (Γ ⊹ A) Δ
  W₁tms {Γ} A σ = σ C.⊚ C.π {Γ}

  πη : {Γ : C.ctx} {A : C.ty} →
    C.π ≡ W₁tms A (C.𝒾𝒹 Γ)
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

--⇓π {Γ} {B}

  open CCC

  ambCCC : CCC ambCC
  _⇛_ ambCCC = C-⇒
  Λ ambCCC {Γ} {A} {B} = C-Λ (⇓Ctx Γ) A B
  𝑎𝑝𝑝 ambCCC {Γ} {A} {B} = C-App (⇓Ctx Γ) A B
  Λnat ambCCC {Γ} {Δ} {A} {B} t σ = ΛnatTm t σ
  𝑎𝑝𝑝β ambCCC {Γ} = 𝑎𝑝𝑝βTm {Γ}
  𝑎𝑝𝑝η ambCCC {Γ} = 𝑎𝑝𝑝ηTm {Γ}

