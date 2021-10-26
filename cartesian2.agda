{-# OPTIONS --cubical #-}

module cartesian2 where

open import contextual

open import Cubical.Categories.Category

private
  variable
    ℓ₁ ℓ₂ : Level

record CCC (𝒞 : Contextual ℓ₁ ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  open Contextual 𝒞
  
  -- the product is given by ⊹ with pairing given by ⊕

  field
    π : {Γ : ctx} {A : ty} → tms (Γ ⊹ A) Γ
    𝑧 : {Γ : ctx} {A : ty} → tm (Γ ⊹ A) A
    πβ : {Γ Δ : ctx} {A : ty} (σ : tms Γ Δ) (t : tm Γ A) →
      π ⊚ (σ ⊕ t) ≡ σ
    𝑧β : {Γ Δ : ctx} {A : ty} (σ : tms Γ Δ) (t : tm Γ A) →
      𝑧 ⟦ σ ⊕ t ⟧ ≡ t
    π𝑧η : {Γ Δ : ctx} {A : ty} (σ : tms Γ (Δ ⊹ A)) →
      σ ≡ (π ⊚ σ) ⊕ (𝑧 ⟦ σ ⟧)

  field
    _⇛_ : ty → ty → ty
    Λ : {Γ : ctx} {A B : ty} → tm (Γ ⊹ A) B → tm Γ (A ⇛ B)
    𝑎𝑝𝑝 : {Γ : ctx} {A B : ty} → tm Γ (A ⇛ B) → tm Γ A → tm Γ B

  -- Categorical app operator
  𝐴𝑝𝑝 : {Γ : ctx} {A B : ty} → tm Γ (A ⇛ B) → tm (Γ ⊹ A) B
  𝐴𝑝𝑝 t = 𝑎𝑝𝑝 (t ⟦ π ⟧) 𝑧

  field
    Λnat : {Γ Δ : ctx} {A B : ty} (t : tm (Δ ⊹ A) B) (σ : tms Γ Δ) →
      Λ t ⟦ σ ⟧ ≡  Λ ( t ⟦ (σ ⊚ π) ⊕ 𝑧 ⟧)
    {-Λnat₂ : {Γ Δ : ctx} {A B : ty} (t : tm Δ B) (σ : tms (Γ ⊹ A) Δ) →
      Λ (t ⟦ σ ⟧) ≡ Λ (t ⟦ {!!} ⟧) ⟦ mapIL₁ Λ σ ⟧-}
    𝑎𝑝𝑝β : {Γ : ctx} {A B : ty} (t : tm (Γ ⊹ A) B) (s : tm Γ A) →
      𝑎𝑝𝑝 (Λ t) s ≡ t ⟦ 𝒾𝒹 Γ ⊕ s ⟧
    𝑎𝑝𝑝η : {Γ : ctx} {A B : ty} (t : tm Γ (A ⇛ B)) →
      t ≡ Λ (𝐴𝑝𝑝 t)

  -- ∅ is automatically the terminal object with unique morphism !

  !η : {Γ : ctx} (σ : tms Γ ∅) → ! ≡ σ
  !η ! = refl

  -- Some useful lemmas

  ⊕⊚ : {Γ Δ Σ : ctx} {A : ty} (σ : tms Δ Σ) (t : tm Δ A) (τ : tms Γ Δ) →
    (σ ⊕ t) ⊚ τ ≡ (σ ⊚ τ) ⊕ (t ⟦ τ ⟧)
  ⊕⊚ σ t τ =
    (σ ⊕ t) ⊚ τ
      ≡⟨ π𝑧η (σ ⊕ t ⊚ τ) ⟩
    π ⊚ (σ ⊕ t ⊚ τ) ⊕ 𝑧 ⟦ σ ⊕ t ⊚ τ ⟧
      ≡⟨ (λ i → ⊚Assoc π (σ ⊕ t) τ (~ i) ⊕ ⟦⟧⟦⟧ 𝑧 (σ ⊕ t) τ (~ i)) ⟩
    π ⊚ (σ ⊕ t) ⊚ τ ⊕ 𝑧 ⟦ σ ⊕ t ⟧ ⟦ τ ⟧
      ≡⟨ (λ i → (πβ σ t i ⊚ τ) ⊕ (𝑧β σ t i ⟦ τ ⟧)) ⟩
    (σ ⊚ τ) ⊕ (t ⟦ τ ⟧)
      ∎

  𝒾𝒹β : {Γ : ctx} {A : ty} → π ⊕ 𝑧 ≡ 𝒾𝒹 (Γ ⊹ A)
  𝒾𝒹β {Γ} {A} =
    π ⊕ 𝑧
      ≡⟨ (λ i → 𝒾𝒹R π (~ i) ⊕ 𝒾𝒹⟦⟧ 𝑧 (~ i)) ⟩
    (π ⊚ (𝒾𝒹 (Γ ⊹ A))) ⊕ (𝑧 ⟦ 𝒾𝒹 (Γ ⊹ A) ⟧)
      ≡⟨ π𝑧η (𝒾𝒹 (Γ ⊹ A)) ⁻¹ ⟩
    𝒾𝒹 (Γ ⊹ A)
      ∎

  private
    lem : {Γ Δ : ctx} {A : ty} (σ : tms Γ Δ) (t : tm Γ A) →
      ((σ ⊚ π) ⊕ 𝑧) ⊚ (𝒾𝒹 Γ ⊕ t) ≡ σ ⊕ t
    lem {Γ} σ t =
      ((σ ⊚ π) ⊕ 𝑧) ⊚ (𝒾𝒹 Γ ⊕ t)
        ≡⟨ ⊕⊚ (σ ⊚ π) 𝑧 (𝒾𝒹 Γ ⊕ t) ⟩
      σ ⊚ π ⊚ (𝒾𝒹 Γ ⊕ t) ⊕ 𝑧 ⟦ 𝒾𝒹 Γ ⊕ t ⟧
        ≡⟨ (λ i → ⊚Assoc σ π (𝒾𝒹 Γ ⊕ t) i ⊕ 𝑧β (𝒾𝒹 Γ) t i) ⟩
      σ ⊚ (π ⊚ (𝒾𝒹 Γ ⊕ t)) ⊕ t
        ≡⟨ (λ i → σ ⊚ (πβ (𝒾𝒹 Γ) t i) ⊕ t) ⟩
      σ ⊚ 𝒾𝒹 Γ ⊕ t
        ≡⟨ ap (_⊕ t) (𝒾𝒹R σ) ⟩
      σ ⊕ t
        ∎

  𝐴𝑝𝑝β : {Γ : ctx} {A B : ty} (t : tm (Γ ⊹ A) B) →
    𝐴𝑝𝑝 (Λ t) ≡ t
  𝐴𝑝𝑝β {Γ} {A} {B} t =
    𝑎𝑝𝑝 (Λ t ⟦ π ⟧) 𝑧
      ≡⟨ (λ i → 𝑎𝑝𝑝 (Λnat t π i) 𝑧) ⟩
    𝑎𝑝𝑝 (Λ (t ⟦ (π ⊚ π) ⊕ 𝑧 ⟧)) 𝑧
      ≡⟨ 𝑎𝑝𝑝β (t ⟦ (π ⊚ π) ⊕ 𝑧 ⟧) 𝑧 ⟩
    t ⟦ (π ⊚ π) ⊕ 𝑧 ⟧ ⟦ 𝒾𝒹 (Γ ⊹ A) ⊕ 𝑧 ⟧
      ≡⟨ ⟦⟧⟦⟧ t ((π ⊚ π) ⊕ 𝑧) (𝒾𝒹 (Γ ⊹ A) ⊕ 𝑧) ⟩
    t ⟦ ((π ⊚ π) ⊕ 𝑧) ⊚ (𝒾𝒹 (Γ ⊹ A) ⊕ 𝑧) ⟧
      ≡⟨ ap (t ⟦_⟧) (lem π 𝑧) ⟩
    t ⟦ π ⊕ 𝑧 ⟧
      ≡⟨ ap (t ⟦_⟧) 𝒾𝒹β ⟩
    t ⟦ 𝒾𝒹 (Γ ⊹ A) ⟧
      ≡⟨ 𝒾𝒹⟦⟧ t ⟩
    t
      ∎

  𝐴𝑝𝑝⟦⟧ : {Γ Δ : ctx} {A B : ty} (t : tm Δ (A ⇛ B)) (σ : tms Γ Δ) →
    𝐴𝑝𝑝 (t ⟦ σ ⟧) ≡ (𝐴𝑝𝑝 t ⟦ σ ⊚ π ⊕ 𝑧 ⟧)
  𝐴𝑝𝑝⟦⟧ t σ =
    𝐴𝑝𝑝 (t ⟦ σ ⟧)
      ≡⟨ (λ i → 𝐴𝑝𝑝 (𝑎𝑝𝑝η t i ⟦ σ ⟧)) ⟩
    𝐴𝑝𝑝 (Λ (𝐴𝑝𝑝 t) ⟦ σ ⟧)
      ≡⟨ ap 𝐴𝑝𝑝 (Λnat (𝐴𝑝𝑝 t) σ) ⟩
    𝐴𝑝𝑝 (Λ (𝐴𝑝𝑝 t ⟦ σ ⊚ π ⊕ 𝑧 ⟧))
      ≡⟨ 𝐴𝑝𝑝β (𝐴𝑝𝑝 t ⟦ σ ⊚ π ⊕ 𝑧 ⟧) ⟩
    𝐴𝑝𝑝 t ⟦ σ ⊚ π ⊕ 𝑧 ⟧
      ∎

  𝑎𝑝𝑝𝐴𝑝𝑝 : {Γ : ctx} {A B : ty} (t : tm Γ (A ⇛ B)) (s : tm Γ A) →
    𝑎𝑝𝑝 t s ≡ 𝐴𝑝𝑝 t ⟦ 𝒾𝒹 Γ ⊕ s ⟧
  𝑎𝑝𝑝𝐴𝑝𝑝 {Γ} t s =
    𝑎𝑝𝑝 t s
      ≡⟨ (λ i → 𝑎𝑝𝑝 (𝑎𝑝𝑝η t i) s) ⟩
    𝑎𝑝𝑝 (Λ (𝐴𝑝𝑝 t)) s
      ≡⟨ 𝑎𝑝𝑝β (𝐴𝑝𝑝 t) s ⟩
    𝐴𝑝𝑝 t ⟦ 𝒾𝒹 Γ ⊕ s ⟧
      ∎

  -- We finally get to the substitution law for applications;
  -- this follows from the axioms, with great difficulty.
  
  𝑎𝑝𝑝⟦⟧ : {Γ Δ : ctx} {A B : ty} (t : tm Δ (A ⇛ B)) (s : tm Δ A) (σ : tms Γ Δ) →
    𝑎𝑝𝑝 t s ⟦ σ ⟧ ≡ 𝑎𝑝𝑝 (t ⟦ σ ⟧) (s ⟦ σ ⟧)
  𝑎𝑝𝑝⟦⟧ {Γ} {Δ} t s σ =
    𝑎𝑝𝑝 t s ⟦ σ ⟧
      ≡⟨ ap (_⟦ σ ⟧) (𝑎𝑝𝑝𝐴𝑝𝑝 t s) ⟩
    𝐴𝑝𝑝 t ⟦ 𝒾𝒹 Δ ⊕ s ⟧ ⟦ σ ⟧
      ≡⟨ ⟦⟧⟦⟧ (𝐴𝑝𝑝 t) (𝒾𝒹 Δ  ⊕ s) σ ⟩
    𝐴𝑝𝑝 t ⟦ 𝒾𝒹 Δ ⊕ s ⊚ σ ⟧
      ≡⟨ ap (𝐴𝑝𝑝 t ⟦_⟧) (⊕⊚ (𝒾𝒹 Δ) s σ) ⟩
    𝐴𝑝𝑝 t ⟦ (𝒾𝒹 Δ) ⊚ σ ⊕ s ⟦ σ ⟧ ⟧
      ≡⟨ (λ i → 𝐴𝑝𝑝 t ⟦ 𝒾𝒹L σ i ⊕ s ⟦ σ ⟧ ⟧) ⟩
    𝐴𝑝𝑝 t ⟦ σ ⊕ s ⟦ σ ⟧ ⟧
      ≡⟨ ap (𝐴𝑝𝑝 t ⟦_⟧) (lem σ (s ⟦ σ ⟧) ⁻¹) ⟩
    𝐴𝑝𝑝 t ⟦ (σ ⊚ π ⊕ 𝑧) ⊚ (𝒾𝒹 Γ ⊕ s ⟦ σ ⟧) ⟧
      ≡⟨ ⟦⟧⟦⟧ (𝐴𝑝𝑝 t) (σ ⊚ π ⊕ 𝑧) (𝒾𝒹 Γ ⊕ s ⟦ σ ⟧) ⁻¹ ⟩
    𝐴𝑝𝑝 t ⟦ σ ⊚ π ⊕ 𝑧 ⟧ ⟦ 𝒾𝒹 Γ ⊕ s ⟦ σ ⟧ ⟧
      ≡⟨ ap _⟦ 𝒾𝒹 Γ ⊕ s ⟦ σ ⟧ ⟧ (𝐴𝑝𝑝⟦⟧ t σ ⁻¹) ⟩
    𝐴𝑝𝑝 (t ⟦ σ ⟧) ⟦ 𝒾𝒹 Γ ⊕ s ⟦ σ ⟧ ⟧
      ≡⟨ 𝑎𝑝𝑝𝐴𝑝𝑝 (t ⟦ σ ⟧) (s ⟦ σ ⟧) ⁻¹ ⟩
    𝑎𝑝𝑝 (t ⟦ σ ⟧) (s ⟦ σ ⟧)
      ∎
