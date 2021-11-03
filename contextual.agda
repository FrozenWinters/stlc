{-# OPTIONS --cubical #-}

module contextual where

open import lists public

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Data.Nat renaming (zero to Z; suc to S)

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

-- This new definition of a contextual category arose as a way to de-boilerplate the code;
-- it is the most natural variation of the definition to use in an implementation.

record Contextual (ℓ₁ ℓ₂ : Level) : Type (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    ty : Type ℓ₁
    
  ctx = RL ty
  
  field
    tm : ctx → ty → Type ℓ₂

  tms = IL tm

  infixl 30 _⟦_⟧
  field
    _⟦_⟧ : {Γ Δ : ctx} {A : ty} → tm Δ A → tms Γ Δ → tm Γ A

  infixl 20 _⊚_
  _⊚_ : {Γ Δ Σ : ctx} → tms Δ Σ → tms Γ Δ → tms Γ Σ
  σ ⊚ τ = mapIL _⟦ τ ⟧ σ

  field
    𝒾𝒹 : (Γ : ctx) → tms Γ Γ
    𝒾𝒹L : {Γ Δ : ctx} (σ : tms Γ Δ) → 𝒾𝒹 Δ ⊚ σ ≡ σ
    𝒾𝒹⟦⟧ : {Γ : ctx} {A : ty} (t : tm Γ A) → t ⟦ 𝒾𝒹 Γ ⟧ ≡ t
    ⟦⟧⟦⟧ : {Γ Δ Σ : ctx} {A : ty} (t : tm Σ A) (σ : tms Δ Σ) (τ : tms Γ Δ) →
      t ⟦ σ ⟧ ⟦ τ ⟧ ≡ t ⟦ σ ⊚ τ ⟧
    isSetTm : {Γ : ctx} {A : ty} → isSet (tm Γ A)

  𝒾𝒹R : {Γ Δ : ctx} (σ : tms Γ Δ) → σ ⊚ 𝒾𝒹 Γ ≡ σ
  𝒾𝒹R ! = refl
  𝒾𝒹R (σ ⊕ t) i = 𝒾𝒹R σ i ⊕ 𝒾𝒹⟦⟧ t i

  ⊚Assoc : {Γ Δ Σ Ω : ctx} (σ : tms Σ Ω) (τ : tms Δ Σ) (μ : tms Γ Δ) →
    σ ⊚ τ ⊚ μ ≡ σ ⊚ (τ ⊚ μ)
  ⊚Assoc ! τ μ = refl
  ⊚Assoc (σ ⊕ t) τ μ i = ⊚Assoc σ τ μ i ⊕ ⟦⟧⟦⟧ t τ μ i

  private
    module P = ILPath tm isSetTm

  isSetTms = P.isSetTms

  -- Every contextual category has an ambient category of contexts and terms

  open Precategory

  ambCat : Precategory ℓ₁ (ℓ₁ ⊔ ℓ₂)
  ob ambCat = ctx
  Hom[_,_] ambCat Γ Δ = tms Γ Δ
  Precategory.id ambCat Γ = 𝒾𝒹 Γ
  _⋆_ ambCat τ σ = σ ⊚ τ
  ⋆IdL ambCat = 𝒾𝒹R
  ⋆IdR ambCat = 𝒾𝒹L
  ⋆Assoc ambCat μ τ σ = ⊚Assoc σ τ μ ⁻¹

  instance
    isCatAmbCat : isCategory ambCat
    isSetHom isCatAmbCat = isSetTms

  -- The identity function includes with it a notion of internal variables

  data IntVar : ctx → ty → Type ℓ₁ where
    𝑧V : {Γ : ctx} {A : ty} → IntVar (Γ ⊹ A) A
    𝑠V : {Γ : ctx} {A B : ty} → IntVar Γ A → IntVar (Γ ⊹ B) A

  {-dropVar : {Γ : ctx} {A : ty} → IntVar Γ A → ctx
  dropVar {Γ ⊹ A} 𝑧V = Γ
  dropVar (𝑠V v) = dropVar v-}

  dropVar : {Γ : ctx} {A : ty} → IntVar Γ A → ctx
  dropVar {Γ} 𝑧V = Γ
  dropVar {Γ ⊹ B} (𝑠V v) = Γ

  --dropTm : {Γ Δ : ctx} {A : ty} → tms Γ (Δ ⊹ A) → 

  {-dropVar : (n : ℕ) {Γ : ctx} {A : ty} → IntVar Γ A → ctx
  {-dropVar n {Γ} 𝑧V = Γ
  dropVar Z {Γ} (𝑠V v) = Γ
  dropVar (S n) (𝑠V v) = dropVar n v-}
  dropVar Z {Γ} v = Γ
  dropVar (S n) {Γ} 𝑧V = Γ
  dropVar (S n) (𝑠V v) = dropVar n v-}

  {-dropVarπ : (n : ℕ) {Γ : ctx} {A : ty} → IntVar Γ A → ctx
  dropVarπ n {Γ ⊹ A} 𝑧V = Γ
  dropVarπ Z {Γ ⊹ B} (𝑠V v) = Γ
  dropVarπ (S n) (𝑠V v) = dropVarπ n v
  {-dropVarπ Z {Γ ⊹ A} 𝑧V = Γ
  dropVarπ Z {Γ ⊹ B} (𝑠V v) = Γ
  dropVarπ (S n) {Γ ⊹ A} 𝑧V = Γ
  dropVarπ (S n) (𝑠V v) = dropVarπ n v-}

  dropVar𝑧 : (n : ℕ) {Γ : ctx} {A : ty} → IntVar Γ A → ty
  dropVar𝑧 n {Γ ⊹ A} 𝑧V = A
  dropVar𝑧 Z {Γ ⊹ B} (𝑠V v) = B
  dropVar𝑧 (S n) (𝑠V v) = dropVar𝑧 n v
  {-dropVar𝑧 Z {Γ} v = ?
  dropVar𝑧 (S n) {Γ ⊹ A} 𝑧V = ?
  dropVar𝑧 (S n) (𝑠V v) = dropVar𝑧 n v-}

  dropVar : (n : ℕ) {Γ : ctx} {A : ty} → IntVar Γ A → ctx
  dropVar n v = dropVarπ n v ⊹ dropVar𝑧 n v-}

  {-drop𝒾𝒹 : (n : ℕ) {Γ : ctx} {A : ty} (w : IntVar Γ A) (v : IntVar (dropVar n w) A) →
    tms Γ (dropVar n w)
  drop𝒾𝒹 Z {Γ} v w = 𝒾𝒹 Γ
  drop𝒾𝒹 (S n) 𝑧V w = {!!}
  drop𝒾𝒹 (S n) (𝑠V v) w = {!!}-}
  {-drop𝒾𝒹 n {Γ} 𝑧V w = 𝒾𝒹 Γ
  drop𝒾𝒹 Z {Γ} (𝑠V v) w = {!!}
  drop𝒾𝒹 (S n) (𝑠V v) w = {!drop𝒾𝒹 n (𝑠V v) ? !}-}
  {-drop𝒾𝒹 Z {Γ} w v = 𝒾𝒹 Γ
  drop𝒾𝒹 (S n) {Γ} 𝑧V v = {!𝒾𝒹 Γ!}
  drop𝒾𝒹 (S n) (𝑠V w) v = {!!}-}

  {-drop𝒾𝒹 : (Γ : ctx) {A : ty} (v : IntVar Γ A) → tms Γ (dropVar v ⊹ A)
  drop𝒾𝒹 v = {!!}-}

  {-dropπ : (n : ℕ) → ctx → ty → ctx
  dropπ Z Γ A = Γ
  dropπ (S n) ∅ A = ∅
  dropπ (S n) (Γ ⊹ B) A = dropπ n Γ B

  drop𝑧 : (n : ℕ) → ctx → ty → ty
  drop𝑧 Z Γ A = A
  drop𝑧 (S n) ∅ A = A
  drop𝑧 (S n) (Γ ⊹ B) A = drop𝑧 n Γ B

  -- Will stop dropping at a size one context
  -- Done in two parts so it's judgmentally non-empty

  drop : (n : ℕ) → ctx → ty → ctx
  drop n Γ A = dropπ n Γ A ⊹ drop𝑧 n Γ A

  typeAt : (n : ℕ) → ctx → ty → ty
  typeAt n Γ A = drop𝑧 n Γ A

  dropTm : (n : ℕ) {Γ Δ : ctx} {A : ty} → tms Γ (Δ ⊹ A) → tms Γ (drop n Δ A)
  dropTm Z σ = σ
  dropTm (S n) (! ⊕ t) = ! ⊕ t
  dropTm (S n) (σ ⊕ s ⊕ t) = dropTm n (σ ⊕ s)

  dropCtx : {Γ : ctx} {A : ty} → IntVar Γ A → ctx
  dropCtx {Γ} 𝑧V = Γ
  dropCtx (𝑠V v) = dropCtx v

  dropVar : {Γ : ctx} {A : ty} (v : IntVar Γ A) → tms Γ (dropCtx v)
  dropVar {Γ ⊹ A} 𝑧V = 𝒾𝒹 (Γ ⊹ A)
  dropVar (𝑠V v) = {!!}-}

  --drop𝒾𝒹 : (n : ℕ) (Γ : Ctx) (A : Ty) → tms (Γ ⊹ A) 

  {-drop𝒾𝒹 : (n : ℕ) (Γ : ctx) (A : ty) → tms (Γ ⊹ A) (drop n Γ A)
  drop𝒾𝒹 Z Γ A = 𝒾𝒹 (Γ ⊹ A)
  drop𝒾𝒹 (S n) ∅ A = 𝒾𝒹 (∅ ⊹ A)
  drop𝒾𝒹 (S n) (Γ ⊹ B) A = {!πIL (drop𝒾𝒹 n (Γ ⊹ B) A)!}-}

  π : {Γ : ctx} {A : ty} → tms (Γ ⊹ A) Γ
  π {Γ} {A} = πIL (𝒾𝒹 (Γ ⊹ A))

  𝑧 : {Γ : ctx} {A : ty} → tm (Γ ⊹ A) A
  𝑧 {Γ} {A} = 𝑧IL (𝒾𝒹 (Γ ⊹ A))

  makeVar : {Γ : ctx} {A : ty} → IntVar Γ A → tm Γ A
  makeVar 𝑧V = 𝑧
  makeVar (𝑠V v) = makeVar v ⟦ π ⟧

  IntRen = IL IntVar

  W₁IntRen : {Γ Δ : ctx} (A : ty) → IntRen Γ Δ → IntRen (Γ ⊹ A) Δ
  W₁IntRen A σ = mapIL 𝑠V σ

  W₂IntRen : {Γ Δ : ctx} (A : ty) → IntRen Γ Δ → IntRen (Γ ⊹ A) (Δ ⊹ A)
  W₂IntRen A σ = W₁IntRen A σ ⊕ 𝑧V

  --IntIdRen : 

  𝒾𝒹η : {Γ : ctx} {A : ty} → π ⊕ 𝑧 ≡ 𝒾𝒹 (Γ ⊹ A) 
  𝒾𝒹η {Γ} {A} = π𝑧ηIL (𝒾𝒹 (Γ ⊹ A))

  π𝑧η : {Γ Δ : ctx} {A : ty} (σ : tms Γ (Δ ⊹ A)) →
    (π ⊚ σ) ⊕ (𝑧 ⟦ σ ⟧) ≡ σ
  π𝑧η {Γ} {Δ} {A} σ =
    π ⊚ σ ⊕ 𝑧 ⟦ σ ⟧
      ≡⟨ ap (_⊚ σ) 𝒾𝒹η ⟩
    𝒾𝒹 (Δ ⊹ A) ⊚ σ
      ≡⟨ 𝒾𝒹L σ ⟩
    σ
      ∎

  πβ : {Γ Δ : ctx} {A : ty} (σ : tms Γ Δ) (t : tm Γ A) →
    π ⊚ (σ ⊕ t) ≡ σ
  πβ σ t = ap πIL (π𝑧η (σ ⊕ t))

  𝑧β : {Γ Δ : ctx} {A : ty} (σ : tms Γ Δ) (t : tm Γ A) →
    𝑧 ⟦ σ ⊕ t ⟧ ≡ t
  𝑧β σ t = ap 𝑧IL (π𝑧η (σ ⊕ t))

-- The idea is that a contextual functor preserves the contextual structure

record ContextualFunctor (𝒞 : Contextual ℓ₁ ℓ₂) (𝒟 : Contextual ℓ₃ ℓ₄)
       : Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  open Contextual

  private
    module C = Contextual 𝒞
    module D = Contextual 𝒟
  
  field
    CF-ty : ty 𝒞 → ty 𝒟

  CF-ctx : ctx 𝒞 → ctx 𝒟
  CF-ctx Γ = mapRL CF-ty Γ

  field
    CF-tm : {Γ : ctx 𝒞} {A : ty 𝒞} → tm 𝒞 Γ A → tm 𝒟 (CF-ctx Γ) (CF-ty A)

  CF-tms : {Γ Δ : ctx 𝒞} → tms 𝒞 Γ Δ → tms 𝒟 (CF-ctx Γ) (CF-ctx Δ)
  CF-tms σ = mapIL₁ CF-tm σ

  field
    CF-id : {Γ : ctx 𝒞} → CF-tms (𝒾𝒹 𝒞 Γ) ≡ 𝒾𝒹 𝒟 (CF-ctx Γ)
    CF-sub : {Γ Δ : ctx 𝒞} {A : ty 𝒞} (t : tm 𝒞 Δ A) (σ : tms 𝒞 Γ Δ) →
      CF-tm (t C.⟦ σ ⟧) ≡ CF-tm t D.⟦ CF-tms σ ⟧

  CF-comp : {Γ Δ Σ : ctx 𝒞} (σ : tms 𝒞 Δ Σ) (τ : tms 𝒞 Γ Δ) →
    CF-tms (σ C.⊚ τ) ≡ (CF-tms σ) D.⊚ (CF-tms τ)
  CF-comp ! τ = refl
  CF-comp (σ ⊕ t) τ i = CF-comp σ τ i ⊕ CF-sub t τ i

  open Functor

  -- A contextual functor induces a functor between the ambient categories

  ambFun : Functor (ambCat 𝒞) (ambCat 𝒟)
  F-ob ambFun = CF-ctx
  F-hom ambFun = CF-tms
  F-id ambFun = CF-id
  F-seq ambFun τ σ = CF-comp σ τ
