{-# OPTIONS --cubical #-}

module ccc where

open import contextual

open import Cubical.Categories.Category

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

-- Here is a definition of a Cartesian Closed Contextual Category

record CCC (𝒞 : Contextual ℓ₁ ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  open Contextual 𝒞
  
  -- the product is given by ⊹ with pairing given by ⊕

  field
    _⇛_ : ty → ty → ty
    Λ : {Γ : ctx} {A B : ty} → tm (Γ ⊹ A) B → tm Γ (A ⇛ B)
    𝑎𝑝𝑝 : {Γ : ctx} {A B : ty} → tm Γ (A ⇛ B) → tm Γ A → tm Γ B

  -- Categorical app operator
  𝐴𝑝𝑝 : {Γ : ctx} {A B : ty} → tm Γ (A ⇛ B) → tm (Γ ⊹ A) B
  𝐴𝑝𝑝 t = 𝑎𝑝𝑝 (t ⟦ π ⟧) 𝑧

  field
    Λnat : {Γ Δ : ctx} {A B : ty} (t : tm (Δ ⊹ A) B) (σ : tms Γ Δ) →
      Λ t ⟦ σ ⟧ ≡  Λ ( t ⟦ W₂tms A σ ⟧)
    𝑎𝑝𝑝β : {Γ : ctx} {A B : ty} (t : tm (Γ ⊹ A) B) (s : tm Γ A) →
      𝑎𝑝𝑝 (Λ t) s ≡ t ⟦ 𝒾𝒹 Γ ⊕ s ⟧
    𝑎𝑝𝑝η : {Γ : ctx} {A B : ty} (t : tm Γ (A ⇛ B)) →
      t ≡ Λ (𝐴𝑝𝑝 t)

  -- Some useful lemmas

  ⊕⊚ : {Γ Δ Σ : ctx} {A : ty} (σ : tms Δ Σ) (t : tm Δ A) (τ : tms Γ Δ) →
    (σ ⊕ t) ⊚ τ ≡ (σ ⊚ τ) ⊕ (t ⟦ τ ⟧)
  ⊕⊚ σ t τ =
    (σ ⊕ t) ⊚ τ
      ≡⟨ π𝑧η (σ ⊕ t ⊚ τ) ⁻¹ ⟩
    π ⊚ (σ ⊕ t ⊚ τ) ⊕ 𝑧 ⟦ σ ⊕ t ⊚ τ ⟧
      ≡⟨ (λ i → ⊚Assoc π (σ ⊕ t) τ (~ i) ⊕ ⟦⟧⟦⟧ 𝑧 (σ ⊕ t) τ (~ i)) ⟩
    π ⊚ (σ ⊕ t) ⊚ τ ⊕ 𝑧 ⟦ σ ⊕ t ⟧ ⟦ τ ⟧
      ≡⟨ (λ i → (πβ (σ ⊕ t) i ⊚ τ) ⊕ (𝑧β (σ ⊕ t) i ⟦ τ ⟧)) ⟩
    (σ ⊚ τ) ⊕ (t ⟦ τ ⟧)
      ∎

  private
    lem : {Γ Δ : ctx} {A : ty} (σ : tms Γ Δ) (t : tm Γ A) →
      ((σ ⊚ π) ⊕ 𝑧) ⊚ (𝒾𝒹 Γ ⊕ t) ≡ σ ⊕ t
    lem {Γ} σ t =
      ((σ ⊚ π) ⊕ 𝑧) ⊚ (𝒾𝒹 Γ ⊕ t)
        ≡⟨ ⊕⊚ (σ ⊚ π) 𝑧 (𝒾𝒹 Γ ⊕ t) ⟩
      σ ⊚ π ⊚ (𝒾𝒹 Γ ⊕ t) ⊕ 𝑧 ⟦ 𝒾𝒹 Γ ⊕ t ⟧
        ≡⟨ (λ i → ⊚Assoc σ π (𝒾𝒹 Γ ⊕ t) i ⊕ 𝑧β (𝒾𝒹 Γ ⊕ t) i) ⟩
      σ ⊚ (π ⊚ (𝒾𝒹 Γ ⊕ t)) ⊕ t
        ≡⟨ (λ i → σ ⊚ (πβ (𝒾𝒹 Γ ⊕ t) i) ⊕ t) ⟩
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
      ≡⟨ ap (t ⟦_⟧) 𝒾𝒹η ⟩
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

  -- A transport lemma

  transp𝐴𝑝𝑝 : {Γ Δ : ctx} {A B : ty} (a : Γ ≡ Δ) (t : tm Γ (A ⇛ B)) →
    transport (λ i → tm (a i ⊹ A) B) (𝐴𝑝𝑝 t) ≡ 𝐴𝑝𝑝 (transport (λ i → tm (a i) (A ⇛ B)) t)
  transp𝐴𝑝𝑝 {A = A} {B} a t =
    J (λ Δ a → transport (λ i → tm (a i ⊹ A) B) (𝐴𝑝𝑝 t)
      ≡ 𝐴𝑝𝑝 (transport (λ i → tm (a i) (A ⇛ B)) t))
      (transportRefl (𝐴𝑝𝑝 t) ∙ ap 𝐴𝑝𝑝 (transportRefl t ⁻¹)) a

-- Next we define what it means for a CF to prserve CCC structures

record CCCPreserving {𝒞 : Contextual ℓ₁ ℓ₂} {𝒟 : Contextual ℓ₃ ℓ₄}
       ⦃ 𝒞CCC : CCC 𝒞 ⦄ ⦃ 𝒟CCC : CCC 𝒟 ⦄ (F : ContextualFunctor 𝒞 𝒟)
       : Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where

  private
    module C = Contextual 𝒞
    module D = Contextual 𝒟
    module Cc = CCC 𝒞CCC
    module Dc = CCC 𝒟CCC

  open ContextualFunctor F

  -- We only need to stipulate that it preserves the categorical 𝐴𝑝𝑝
  -- Preservation of Λ and 𝑎𝑝𝑝 follow as corollaries

  field
    pres-⇛ : (A B : C.ty) → CF-ty (A Cc.⇛ B) ≡ CF-ty A Dc.⇛ CF-ty B
    pres-𝐴𝑝𝑝 : {Γ : C.ctx} {A B : C.ty} (t : C.tm Γ (A Cc.⇛ B)) →
      CF-tm (Cc.𝐴𝑝𝑝 t) ≡ Dc.𝐴𝑝𝑝 (transport (λ i → D.tm (CF-ctx Γ) (pres-⇛ A B i)) (CF-tm t))

  pres-Λ : {Γ : C.ctx} {A B : C.ty} (t : C.tm (Γ ⊹ A) B) →
    PathP (λ i → D.tm (CF-ctx Γ) (pres-⇛ A B i)) (CF-tm (Cc.Λ t)) (Dc.Λ (CF-tm t))
  pres-Λ {Γ} {A} {B} t =
    toPathP
      (transport (λ i → D.tm (CF-ctx Γ) (pres-⇛ A B i)) (CF-tm (Cc.Λ t))
        ≡⟨ Dc.𝑎𝑝𝑝η (transport (λ i → D.tm (CF-ctx Γ) (pres-⇛ A B i)) (CF-tm (Cc.Λ t))) ⟩
      Dc.Λ (Dc.𝐴𝑝𝑝 (transport (λ i → D.tm (CF-ctx Γ) (pres-⇛ A B i)) (CF-tm (Cc.Λ t))))
        ≡⟨ ap Dc.Λ (pres-𝐴𝑝𝑝 (Cc.Λ t) ⁻¹) ⟩
      Dc.Λ (CF-tm (Cc.𝐴𝑝𝑝 (Cc.Λ t)))
        ≡⟨ (λ i → Dc.Λ (CF-tm (Cc.𝐴𝑝𝑝β t i))) ⟩
      Dc.Λ (CF-tm t)
        ∎)
      
  pres-𝑎𝑝𝑝 : {Γ : C.ctx} {A B : C.ty} (t : C.tm Γ (A Cc.⇛ B)) (s : C.tm Γ A) →
    CF-tm (Cc.𝑎𝑝𝑝 t s) ≡
    Dc.𝑎𝑝𝑝 (transport (λ i → D.tm (CF-ctx Γ) (pres-⇛ A B i)) (CF-tm t)) (CF-tm s)
  pres-𝑎𝑝𝑝 {Γ} {A} {B} t s =
    CF-tm (Cc.𝑎𝑝𝑝 t s)
      ≡⟨ ap CF-tm (Cc.𝑎𝑝𝑝𝐴𝑝𝑝 t s) ⟩
    CF-tm (Cc.𝐴𝑝𝑝 t C.⟦ C.𝒾𝒹 Γ ⊕ s ⟧)
      ≡⟨ CF-sub (Cc.𝐴𝑝𝑝 t) (C.𝒾𝒹 Γ ⊕ s) ⟩
    CF-tm (Cc.𝐴𝑝𝑝 t) D.⟦ CF-tms (C.𝒾𝒹 Γ) ⊕ CF-tm s ⟧
      ≡⟨ (λ i → pres-𝐴𝑝𝑝 t i D.⟦ CF-id i ⊕  CF-tm s ⟧) ⟩
    Dc.𝐴𝑝𝑝 (transport (λ i → D.tm (CF-ctx Γ) (pres-⇛ A B i)) (CF-tm t))
      D.⟦ D.𝒾𝒹 (map𝐶𝑡𝑥 CF-ty Γ) ⊕ CF-tm s ⟧
      ≡⟨ Dc.𝑎𝑝𝑝𝐴𝑝𝑝 (transport (λ i → D.tm (CF-ctx Γ) (pres-⇛ A B i)) (CF-tm t)) (CF-tm s) ⁻¹ ⟩
    Dc.𝑎𝑝𝑝 (transport (λ i → D.tm (CF-ctx Γ) (pres-⇛ A B i)) (CF-tm t)) (CF-tm s)
      ∎

-- We define what it means for a CCC to be initial

module _ (𝒞 : Contextual ℓ ℓ) ⦃ 𝒞CCC : CCC 𝒞 ⦄ (base₁ : Char → Contextual.ty 𝒞) where
  open Contextual
  open ContextualFunctor

  record InitialInstance (𝒟 : Contextual ℓ₁ ℓ₂) ⦃ 𝒟CCC : CCC 𝒟 ⦄ (base₂ : Char → ty 𝒟)
                         : Type (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    constructor initIn
    
    BasePreserving : ContextualFunctor 𝒞 𝒟 → Type ℓ₁
    BasePreserving F = (c : Char) → CF-ty F (base₁ c) ≡ base₂ c
    
    field
      elim : ContextualFunctor 𝒞 𝒟
      ccc-pres : CCCPreserving elim
      base-pres : BasePreserving elim
      UP : (F : ContextualFunctor 𝒞 𝒟) → CCCPreserving F → BasePreserving F → F ≡ elim

  InitialCCC = ∀ {ℓ₁} {ℓ₂} (𝒟 : Contextual ℓ₁ ℓ₂) ⦃ 𝒟CCC : CCC 𝒟 ⦄ (base₂ : Char → ty 𝒟) →
    InitialInstance 𝒟 base₂

-- Proof that the composition of CCC preserving CFs is CCC preserving
-- Welcome to the ninth circle of transport hell

module _ {𝒞 : Contextual ℓ₁ ℓ₂} {𝒟 : Contextual ℓ₃ ℓ₄} {ℰ : Contextual ℓ₅ ℓ₆}
         ⦃ 𝒞CCC : CCC 𝒞 ⦄ ⦃ 𝒟CCC : CCC 𝒟 ⦄ ⦃ ℰCCC : CCC ℰ ⦄
         {G : ContextualFunctor 𝒟 ℰ} {F : ContextualFunctor 𝒞 𝒟} where
  open ContextualFunctor
  open CCCPreserving
  open CCC

  private
    module C = Contextual 𝒞
    module D = Contextual 𝒟
    module E = Contextual ℰ
    module Cc = CCC 𝒞CCC
    module Dc = CCC 𝒟CCC
    module Ec = CCC ℰCCC

  ∘CF-CCCPres : CCCPreserving G → CCCPreserving F → CCCPreserving (G ∘CF F)
  pres-⇛ (∘CF-CCCPres p₁ p₂) A B =
    ap (CF-ty G) (pres-⇛ p₂ A B) ∙ (pres-⇛ p₁ (CF-ty F A) (CF-ty F B))
  pres-𝐴𝑝𝑝 (∘CF-CCCPres p₁ p₂) {Γ} {A} {B} t =
    transport (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) (Γ ⊹ A) i) (CF-ty G (CF-ty F B)))
      (CF-tm G (CF-tm F (Cc.𝐴𝑝𝑝 t)))
      ≡⟨ ap (transport (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) (Γ ⊹ A) i)
        (CF-ty G (CF-ty F B)))) lem ⟩
    transport (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) (Γ ⊹ A) i) (CF-ty G (CF-ty F B)))
      (Ec.𝐴𝑝𝑝 (transport (λ i → E.tm (CF-ctx G (CF-ctx F Γ)) ((ap (CF-ty G) (pres-⇛ p₂ A B)
        ∙ pres-⇛ p₁ (CF-ty F A) (CF-ty F B)) i)) (CF-tm G (CF-tm F t))))
      ≡⟨ transp𝐴𝑝𝑝 ℰCCC (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ) (transport (λ i → E.tm
        (CF-ctx G (CF-ctx F Γ)) ((ap (CF-ty G) (pres-⇛ p₂ A B)
        ∙ pres-⇛ p₁ (CF-ty F A) (CF-ty F B)) i)) (CF-tm G (CF-tm F t))) ⟩
    Ec.𝐴𝑝𝑝 (transport
      (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i)
        (CF-ty G (CF-ty F A) Ec.⇛ CF-ty G (CF-ty F B)))
      (transport
        (λ i → E.tm (CF-ctx G (CF-ctx F Γ)) ((ap (CF-ty G) (pres-⇛ p₂ A B)
          ∙ pres-⇛ p₁ (CF-ty F A) (CF-ty F B)) i))
        (CF-tm G (CF-tm F t))))
      ≡⟨ ap Ec.𝐴𝑝𝑝 (transport-tm {tm = E.tm} refl (ap (CF-ty G) (pres-⇛ p₂ A B)
        ∙ pres-⇛ p₁ (CF-ty F A) (CF-ty F B)) (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ) refl
        (CF-tm G (CF-tm F t))) ⟩
    Ec.𝐴𝑝𝑝 (transport (λ i → E.tm
      ((refl ∙ map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ) i)
      (((ap (CF-ty G) (pres-⇛ p₂ A B) ∙ pres-⇛ p₁ (CF-ty F A) (CF-ty F B)) ∙ refl) i))
      (CF-tm G (CF-tm F t)))
      ≡⟨ (λ j → Ec.𝐴𝑝𝑝 (transport (λ i → E.tm
        (rUnit (lUnit (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ) (~ j)) j i)
        (lUnit (rUnit (ap (CF-ty G) (pres-⇛ p₂ A B)
          ∙ pres-⇛ p₁ (CF-ty F A) (CF-ty F B)) (~ j)) j i))
        (CF-tm G (CF-tm F t)))) ⟩
    Ec.𝐴𝑝𝑝 (transport (λ i → E.tm
      ((map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ ∙ refl) i)
      ((refl ∙ (ap (CF-ty G) (pres-⇛ p₂ A B) ∙ pres-⇛ p₁ (CF-ty F A) (CF-ty F B))) i))
      (CF-tm G (CF-tm F t)))
      ≡⟨ ap Ec.𝐴𝑝𝑝 (transport-tm {tm = E.tm} (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ) refl
        refl (ap (CF-ty G) (pres-⇛ p₂ A B) ∙ pres-⇛ p₁ (CF-ty F A) (CF-ty F B))
        (CF-tm G (CF-tm F t)) ⁻¹) ⟩
    Ec.𝐴𝑝𝑝 (transport (λ i → E.tm (map𝐶𝑡𝑥 (CF-ty G ∘ CF-ty F) Γ)
      ((ap (CF-ty G) (pres-⇛ p₂ A B) ∙ pres-⇛ p₁ (CF-ty F A) (CF-ty F B)) i))
      (transport (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (CF-ty G (CF-ty F (A Cc.⇛ B))))
        (CF-tm G (CF-tm F t))))
      ∎ where
    lem : CF-tm G (CF-tm F (Cc.𝐴𝑝𝑝 t))
      ≡ Ec.𝐴𝑝𝑝 (transport (λ i → E.tm (CF-ctx G (CF-ctx F Γ)) ((ap (CF-ty G) (pres-⇛ p₂ A B)
        ∙ pres-⇛ p₁ (CF-ty F A) (CF-ty F B)) i)) (CF-tm G (CF-tm F t)))
    lem =
      CF-tm G (CF-tm F (Cc.𝐴𝑝𝑝 t))
        ≡⟨ ap (CF-tm G) (pres-𝐴𝑝𝑝 p₂ t) ⟩
      CF-tm G (Dc.𝐴𝑝𝑝 (transport (λ i → D.tm (CF-ctx F Γ) (pres-⇛ p₂ A B i)) (CF-tm F t)))
        ≡⟨ pres-𝐴𝑝𝑝 p₁ (transport (λ i → D.tm (CF-ctx F Γ) (pres-⇛ p₂ A B i)) (CF-tm F t)) ⟩
      Ec.𝐴𝑝𝑝 (transport (λ i → E.tm (CF-ctx G (CF-ctx F Γ)) (pres-⇛ p₁ (CF-ty F A) (CF-ty F B) i))
        (CF-tm G (transport (λ i → D.tm (CF-ctx F Γ) (pres-⇛ p₂ A B i)) (CF-tm F t))))
        ≡⟨ (λ i → Ec.𝐴𝑝𝑝 (transport (λ i → E.tm (CF-ctx G (CF-ctx F Γ)) (pres-⇛ p₁ (CF-ty F A)
          (CF-ty F B) i)) (transpCF-tm G (pres-⇛ p₂ A B) (CF-tm F t) (~ i)))) ⟩
      Ec.𝐴𝑝𝑝 (transport (λ i → E.tm (CF-ctx G (CF-ctx F Γ)) (pres-⇛ p₁ (CF-ty F A) (CF-ty F B) i))
        (transport (λ i → E.tm (CF-ctx G (map𝐶𝑡𝑥 (CF-ty F) Γ)) (CF-ty G (pres-⇛ p₂ A B i)))
          (CF-tm G (CF-tm F t))))
        ≡⟨ ap Ec.𝐴𝑝𝑝 (transport-tm {tm = E.tm} refl (ap (CF-ty G) (pres-⇛ p₂ A B))
          refl (pres-⇛ p₁ (CF-ty F A) (CF-ty F B)) (CF-tm G (CF-tm F t))) ⟩
      Ec.𝐴𝑝𝑝 (transport (λ i → E.tm ((refl {x = CF-ctx G (CF-ctx F Γ)} ∙ refl) i)
        ((ap (CF-ty G) (pres-⇛ p₂ A B) ∙ pres-⇛ p₁ (CF-ty F A) (CF-ty F B)) i))
        (CF-tm G (CF-tm F t)))
        ≡⟨ (λ j → Ec.𝐴𝑝𝑝 (transport (λ i → E.tm (rUnit (refl {x = CF-ctx G (CF-ctx F Γ)}) (~ j) i)
          ((ap (CF-ty G) (pres-⇛ p₂ A B) ∙ pres-⇛ p₁ (CF-ty F A) (CF-ty F B)) i))
          (CF-tm G (CF-tm F t)))) ⟩
      Ec.𝐴𝑝𝑝 (transport (λ i → E.tm (CF-ctx G (CF-ctx F Γ)) ((ap (CF-ty G) (pres-⇛ p₂ A B)
        ∙ pres-⇛ p₁ (CF-ty F A) (CF-ty F B)) i)) (CF-tm G (CF-tm F t)))
        ∎
