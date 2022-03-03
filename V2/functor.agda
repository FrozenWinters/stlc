{-# OPTIONS --cubical #-}

module functor where

open import lists
open import contextual
open import ccc

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

-- We define contextual functors, what it means for a CF to be CCC preserving, and initial CCCs
-- This file contains the most painful constructions in the entire project
-- (these arise from constructing an proving things about compositions)

-- First, the definitions

record ContextualFunctor (𝒞 : Contextual ℓ₁ ℓ₂) (𝒟 : Contextual ℓ₃ ℓ₄)
       : Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  open Contextual

  private
    module C = Contextual 𝒞
    module D = Contextual 𝒟
  
  field
    CF-ty : ty 𝒞 → ty 𝒟

  CF-ctx : ctx 𝒞 → ctx 𝒟
  CF-ctx Γ = map𝐶𝑡𝑥 CF-ty Γ

  field
    CF-tm : {Γ : ctx 𝒞} {A : ty 𝒞} → tm 𝒞 Γ A → tm 𝒟 (CF-ctx Γ) (CF-ty A)

  CF-tms : {Γ Δ : ctx 𝒞} → tms 𝒞 Γ Δ → tms 𝒟 (CF-ctx Γ) (CF-ctx Δ)
  CF-tms σ = map𝐸𝑙𝑠₁ CF-tm σ

  field
    CF-id : {Γ : ctx 𝒞} → CF-tms (𝒾𝒹 𝒞 Γ) ≡ 𝒾𝒹 𝒟 (CF-ctx Γ)
    CF-sub : {Γ Δ : ctx 𝒞} {A : ty 𝒞} (t : tm 𝒞 Δ A) (σ : tms 𝒞 Γ Δ) →
      CF-tm (t C.⟦ σ ⟧) ≡ CF-tm t D.⟦ CF-tms σ ⟧

  CF-comp : {Γ Δ Σ : ctx 𝒞} (σ : tms 𝒞 Δ Σ) (τ : tms 𝒞 Γ Δ) →
    CF-tms (σ C.⊚ τ) ≡ (CF-tms σ) D.⊚ (CF-tms τ)
  CF-comp ! τ = refl
  CF-comp (σ ⊕ t) τ i = CF-comp σ τ i ⊕ CF-sub t τ i

  CF-Var : {Γ : C.ctx} {A : C.ty} (v : C.IntVar Γ A) →
    CF-tm (C.makeVar v) ≡ D.makeVar (tr𝑉𝑎𝑟 CF-ty v)
  CF-Var {Γ} v =
    CF-tm (C.makeVar v)
      ≡⟨ deriveMap₁ CF-tm (C.𝒾𝒹 Γ) v ⁻¹ ⟩
    derive (CF-tms (C.𝒾𝒹 Γ)) (tr𝑉𝑎𝑟 CF-ty v)
      ≡⟨ (λ i → derive (CF-id i) (tr𝑉𝑎𝑟 CF-ty v)) ⟩
    D.makeVar (tr𝑉𝑎𝑟 CF-ty v)
      ∎

  transpCF-tm : {Γ : C.ctx} {A B : C.ty} (a : A ≡ B) (t : C.tm Γ A) →
    transport (λ i → D.tm (CF-ctx Γ) (CF-ty (a i))) (CF-tm t)
      ≡ CF-tm (transport (λ i → C.tm Γ (a i)) t)
  transpCF-tm {Γ} a t =
    J (λ B a → transport (λ i → D.tm (CF-ctx Γ) (CF-ty (a i))) (CF-tm t)
      ≡ CF-tm (transport (λ i → C.tm Γ (a i)) t))
      (transportRefl (CF-tm t) ∙ ap CF-tm (transportRefl t ⁻¹)) a

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

module _ (𝒞 : Contextual ℓ ℓ) ⦃ 𝒞CCC : CCC 𝒞 ⦄ {X : Type ℓ} (base₁ : X → Contextual.ty 𝒞) where
  open Contextual
  open ContextualFunctor

  record InitialInstance (𝒟 : Contextual ℓ₁ ℓ₂) ⦃ 𝒟CCC : CCC 𝒟 ⦄ (base₂ : X → ty 𝒟)
                         : Type (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    constructor initIn
    
    BasePreserving : ContextualFunctor 𝒞 𝒟 → Type (ℓ ⊔ ℓ₁)
    BasePreserving F = (x : X) → CF-ty F (base₁ x) ≡ base₂ x
    
    field
      elim : ContextualFunctor 𝒞 𝒟
      ccc-pres : CCCPreserving elim
      base-pres : BasePreserving elim
      UP : (F : ContextualFunctor 𝒞 𝒟) → CCCPreserving F → BasePreserving F → F ≡ elim

  InitialCCC = ∀ {ℓ₁} {ℓ₂} (𝒟 : Contextual ℓ₁ ℓ₂) ⦃ 𝒟CCC : CCC 𝒟 ⦄ (base₂ : X → ty 𝒟) →
    InitialInstance 𝒟 base₂

-- Now, the operations and properties

open Contextual
open ContextualFunctor
open CCCPreserving

idCF : (𝒞 : Contextual ℓ₁ ℓ₂) → ContextualFunctor 𝒞 𝒞
CF-ty (idCF 𝒞) A = A
CF-tm (idCF 𝒞) {Γ} {A} t = transport (λ i → tm 𝒞 (map𝐶𝑡𝑥id Γ (~ i)) A) t
CF-id (idCF 𝒞) {Γ} =
  map𝐸𝑙𝑠₁ (λ {A} t → transport (λ i → tm 𝒞 (map𝐶𝑡𝑥id Γ (~ i)) A) t) (𝒾𝒹 𝒞 Γ)
    ≡⟨ map𝑇𝑚𝑠₁id {tm = tm 𝒞} (𝒾𝒹 𝒞 Γ) ⟩
  transport (λ i → 𝑇𝑚𝑠 (tm 𝒞) (map𝐶𝑡𝑥id Γ (~ i)) (map𝐶𝑡𝑥id Γ (~ i))) (𝒾𝒹 𝒞 Γ)
    ≡⟨ transp𝒾𝒹 𝒞 (map𝐶𝑡𝑥id Γ ⁻¹) ⟩
  𝒾𝒹 𝒞 (map𝐶𝑡𝑥 (λ A → A) Γ)
    ∎
CF-sub (idCF 𝒞) {Γ} {Δ} {A} t σ =
  transport (λ i → C.tm (map𝐶𝑡𝑥id Γ (~ i)) A) (t C.⟦ σ ⟧)
    ≡⟨ C.transp⟦⟧ (map𝐶𝑡𝑥id Γ ⁻¹) (map𝐶𝑡𝑥id Δ ⁻¹) t σ ⟩
  transport (λ i → C.tm (map𝐶𝑡𝑥id Δ (~ i)) A) t
    C.⟦ transport (λ i → C.tms (map𝐶𝑡𝑥id Γ (~ i)) (map𝐶𝑡𝑥id Δ (~ i))) σ ⟧
    ≡⟨ (λ i → transport (λ i → C.tm (map𝐶𝑡𝑥id Δ (~ i)) A) t C.⟦ map𝑇𝑚𝑠₁id {tm = C.tm} σ (~ i) ⟧) ⟩
  transport (λ i → C.tm (map𝐶𝑡𝑥id Δ (~ i)) A) t
    C.⟦ map𝐸𝑙𝑠₁ (λ {B} → transport (λ i → C.tm (map𝐶𝑡𝑥id Γ (~ i)) B)) σ ⟧
    ∎ where
  module C = Contextual 𝒞

_∘CF_ : {𝒞 : Contextual ℓ₁ ℓ₂} {𝒟 : Contextual ℓ₃ ℓ₄} {ℰ : Contextual ℓ₅ ℓ₆} →
  ContextualFunctor 𝒟 ℰ → ContextualFunctor 𝒞 𝒟 → ContextualFunctor 𝒞 ℰ
CF-ty (G ∘CF F) = CF-ty G ∘ CF-ty F
CF-tm (_∘CF_ {ℰ = ℰ} G F) {Γ} {A} t  =
  transport (λ i → tm ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (CF-ty G (CF-ty F A)))
    (CF-tm G (CF-tm F t))
CF-id (_∘CF_ {𝒞 = 𝒞} {𝒟} {ℰ} G F) {Γ} =
  map𝐸𝑙𝑠₁ (CF-tm (G ∘CF F)) (𝒾𝒹 𝒞 Γ)
    ≡⟨ map𝐸𝑙𝑠comp₂ (λ {A} → transport (λ i → tm ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) A))
      (CF-tm G ∘ CF-tm F) (𝒾𝒹 𝒞 Γ) ⁻¹ ⟩
  map𝐸𝑙𝑠 (λ {A} → transport (λ i → tm ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) A))
    (map𝐸𝑙𝑠₁ (λ x → CF-tm G (CF-tm F x)) (𝒾𝒹 𝒞 Γ))
    ≡⟨ map𝑇𝑚𝑠comp₃ {tm₁ = tm 𝒞} {tm 𝒟} {tm ℰ} (CF-tm G) (CF-tm F) (𝒾𝒹 𝒞 Γ) ⟩
  transport (λ i → tms ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i))
    (CF-tms G (CF-tms F (𝒾𝒹 𝒞 Γ)))
    ≡⟨ (λ i → transport (λ i → tms ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i)
      (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i)) (CF-tms G (CF-id F i))) ⟩
  transport (λ i → tms ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i))
    (CF-tms G (𝒾𝒹 𝒟 (CF-ctx F Γ)))
    ≡⟨ (λ i → transport (λ i → tms ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i)
      (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i)) (CF-id G i)) ⟩
  transport (λ i → tms ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i))
    (𝒾𝒹 ℰ (CF-ctx G (CF-ctx F Γ)))
    ≡⟨ transp𝒾𝒹 ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ) ⟩
  𝒾𝒹 ℰ (map𝐶𝑡𝑥 (CF-ty G ∘ CF-ty F) Γ)
    ∎   
CF-sub (_∘CF_ {𝒞 = 𝒞} {𝒟} {ℰ} G F) {Γ} {Δ} {A} t σ =
  transport (λ i → tm ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (CF-ty G (CF-ty F A)))
    (CF-tm G (CF-tm F (t C.⟦ σ ⟧)))
    ≡⟨ (λ i → transport (λ i → tm ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (CF-ty G (CF-ty F A)))
      (CF-tm G (CF-sub F t σ i))) ⟩
  transport (λ i → tm ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (CF-ty G (CF-ty F A)))
    (CF-tm G (CF-tm F t D.⟦ CF-tms F σ ⟧))
    ≡⟨ (λ i → transport (λ i → tm ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (CF-ty G (CF-ty F A)))
      (CF-sub G (CF-tm F t) (CF-tms F σ) i)) ⟩
  transport (λ i → tm ℰ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (CF-ty G (CF-ty F A)))
    (CF-tm G (CF-tm F t) E.⟦ CF-tms G (CF-tms F σ) ⟧)
    ≡⟨ E.transp⟦⟧ (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ) (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Δ)
      (CF-tm G (CF-tm F t)) (CF-tms G (CF-tms F σ)) ⟩
  transport (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Δ i) (CF-ty G (CF-ty F A)))
    (CF-tm G (CF-tm F t)) E.⟦ transport (λ i → E.tms (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i)
      (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Δ i)) (CF-tms G (CF-tms F σ)) ⟧
    ≡⟨ (λ i → transport (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Δ i) (CF-ty G (CF-ty F A)))
      (CF-tm G (CF-tm F t)) E.⟦ map𝑇𝑚𝑠comp₃ {tm₁ = C.tm} {D.tm} {E.tm}
      (CF-tm G) (CF-tm F) σ (~ i) ⟧) ⟩
  transport (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Δ i) (CF-ty G (CF-ty F A)))
    (CF-tm G (CF-tm F t)) E.⟦ map𝐸𝑙𝑠 (λ {B} → transport
      (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) B)) (map𝐸𝑙𝑠₁ (CF-tm G ∘ CF-tm F) σ) ⟧
    ≡⟨ (λ i → transport (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Δ i) (CF-ty G (CF-ty F A)))
      (CF-tm G (CF-tm F t)) E.⟦ map𝐸𝑙𝑠comp₂ {el₂ = E.tm _} (λ {B} → transport
        (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) B)) (CF-tm G ∘ CF-tm F) σ i ⟧) ⟩
  transport (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Δ i) (CF-ty G (CF-ty F A)))
    (CF-tm G (CF-tm F t)) E.⟦ map𝐸𝑙𝑠₁ (λ {B} s → transport 
      (λ i → E.tm (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ i) (CF-ty G (CF-ty F B)))
      (CF-tm G (CF-tm F s))) σ ⟧
    ∎ where
    module C = Contextual 𝒞
    module D = Contextual 𝒟
    module E = Contextual ℰ

idCF-CCCPres : (𝒞 : Contextual ℓ₁ ℓ₂) ⦃ 𝒞CCC : CCC 𝒞 ⦄ → CCCPreserving (idCF 𝒞)
pres-⇛ (idCF-CCCPres 𝒞) A B = refl
pres-𝐴𝑝𝑝 (idCF-CCCPres 𝒞 ⦃ 𝒞CCC ⦄) {Γ} t =
  CF-tm (idCF 𝒞) (𝐴𝑝𝑝 t)
    ≡⟨ transp𝐴𝑝𝑝 (map𝐶𝑡𝑥id Γ ⁻¹) t ⟩
  𝐴𝑝𝑝 (CF-tm (idCF 𝒞) t)
    ≡⟨ (λ i → 𝐴𝑝𝑝 (transportRefl (CF-tm (idCF 𝒞) t) (~ i))) ⟩
  𝐴𝑝𝑝 (transport refl (CF-tm (idCF 𝒞) t))
    ∎ where
  open CCC 𝒞CCC

module _ {𝒞 : Contextual ℓ₁ ℓ₂} {𝒟 : Contextual ℓ₃ ℓ₄} {ℰ : Contextual ℓ₅ ℓ₆}
         ⦃ 𝒞CCC : CCC 𝒞 ⦄ ⦃ 𝒟CCC : CCC 𝒟 ⦄ ⦃ ℰCCC : CCC ℰ ⦄
         {G : ContextualFunctor 𝒟 ℰ} {F : ContextualFunctor 𝒞 𝒟} where
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
      ≡⟨ Ec.transp𝐴𝑝𝑝 (map𝐶𝑡𝑥comp (CF-ty G) (CF-ty F) Γ) (transport (λ i → E.tm
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
