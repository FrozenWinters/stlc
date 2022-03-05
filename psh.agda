{-# OPTIONS --cubical --allow-unsolved-metas #-}

module psh where

open import lists
open import contextual
open import ccc

open import Cubical.Data.Sigma

module Presheaf {ℓ : Level} (𝒞 : Category ℓ ℓ) where
  open Category 𝒞

  record PSh : Type (lsuc ℓ) where
    field
      sec : 𝑜𝑏 → Type ℓ
      isSetSec : {A : 𝑜𝑏} → isSet (sec A)
      hom : {A B : 𝑜𝑏} → 𝑚𝑜𝑟 A B → sec B → sec A
      id-hom : {A : 𝑜𝑏} (𝓈 : sec A) →
        hom (𝒾𝒹 A) 𝓈 ≡ 𝓈
      ⊚-hom : {A B C : 𝑜𝑏} (f : 𝑚𝑜𝑟 B C) (g : 𝑚𝑜𝑟 A B) (𝓈 : sec C) →
        hom (f ⊚ g) 𝓈 ≡ hom g (hom f 𝓈)

  open PSh

  PShs = 𝐶𝑡𝑥 PSh

  secs : PShs → 𝑜𝑏 → Type (lsuc ℓ)
  secs γ A = 𝐸𝑙𝑠 (λ α → sec α A) γ

  homs : (γ : PShs) {A B : 𝑜𝑏} → 𝑚𝑜𝑟 A B → secs γ B → secs γ A
  homs γ f 𝓈s = map𝐸𝑙𝑠 (λ {α} → hom α f) 𝓈s

  id-homs : (γ : PShs) {A : 𝑜𝑏} (𝓈s : secs γ A) →
    homs γ (𝒾𝒹 A) 𝓈s ≡ 𝓈s
  id-homs ∅ ! = refl
  id-homs (γ ⊹ α) (𝓈s ⊕ 𝓈) i = id-homs γ 𝓈s i ⊕ id-hom α 𝓈 i

  ⊚-homs : (γ : PShs) {A B C : 𝑜𝑏} (f : 𝑚𝑜𝑟 B C) (g : 𝑚𝑜𝑟 A B) (𝓈s : secs γ C) →
    homs γ (f ⊚ g) 𝓈s ≡ homs γ g (homs γ f 𝓈s)
  ⊚-homs ∅ f g ! = refl
  ⊚-homs (γ ⊹ α) f g (𝓈s ⊕ 𝓈) i = ⊚-homs γ f g 𝓈s i ⊕ ⊚-hom α f g 𝓈 i

  record PShMor (γ : PShs) (α : PSh) : Type (lsuc ℓ) where
    field
      ob : {A : 𝑜𝑏} → secs γ A → sec α A
      nat : {A B : 𝑜𝑏} (f : 𝑚𝑜𝑟 A B) (𝓈s : secs γ B) →
        ob (homs γ f 𝓈s) ≡ hom α f (ob 𝓈s)

  open PShMor

  ≡PShMor : {γ : PShs} {α : PSh} {t s : PShMor γ α} →
    ({A : 𝑜𝑏} (𝓈s : secs γ A) → ob t 𝓈s ≡ ob s 𝓈s) → t ≡ s
  ob (≡PShMor p i) 𝓈s = p 𝓈s i
  nat (≡PShMor {γ} {α} {t} {s} p i) f 𝓈s j =
    isSet→SquareP (λ i j → isSetSec α)
      (nat t f 𝓈s)
      (nat s f 𝓈s)
      (p (homs γ f 𝓈s))
      (λ k → hom α f (p 𝓈s k)) i j

  PShMors = 𝑇𝑚𝑠 PShMor

  obs : {γ δ : PShs} → PShMors γ δ → {A : 𝑜𝑏} → secs γ A → secs δ A
  obs ! 𝓈s = !
  obs (σ ⊕ t) 𝓈s = obs σ 𝓈s ⊕ ob t 𝓈s

  nats : {γ δ : PShs} (σ : PShMors γ δ) {A B : 𝑜𝑏} (f : 𝑚𝑜𝑟 A B) (𝓈s : secs γ B) →
    obs σ (homs γ f 𝓈s) ≡ homs δ f (obs σ 𝓈s)
  nats ! f 𝓈s = refl
  nats (σ ⊕ t) f 𝓈s i = nats σ f 𝓈s i ⊕ nat t f 𝓈s i

  infixl 30 _[_]PSh
  _[_]PSh : {γ δ : PShs} {α : PSh} → PShMor δ α → PShMors γ δ → PShMor γ α
  ob (t [ σ ]PSh) 𝓈s = ob t (obs σ 𝓈s)
  nat (_[_]PSh {γ} {δ} {α} t σ) f 𝓈s =
    ob t (obs σ (homs γ f 𝓈s))
      ≡⟨ ap (ob t) (nats σ f 𝓈s) ⟩
    ob t (homs δ f (obs σ 𝓈s))
      ≡⟨ nat t f (obs σ 𝓈s) ⟩
    hom α f (ob t (obs σ 𝓈s))
      ∎

  _∘PSh_ : {γ δ ε : PShs} → PShMors δ ε → PShMors γ δ → PShMors γ ε
  σ ∘PSh τ = map𝐸𝑙𝑠 _[ τ ]PSh σ

  obs∘PSh : {γ δ ε : PShs} (σ : PShMors δ ε) (τ : PShMors γ δ) {A : 𝑜𝑏} (𝓈s : secs γ A) →
    obs (σ ∘PSh τ) 𝓈s ≡ obs σ (obs τ 𝓈s)
  obs∘PSh ! τ 𝓈s = refl
  obs∘PSh (σ ⊕ t) τ 𝓈s i = obs∘PSh σ τ 𝓈s i ⊕ ob t (obs τ 𝓈s)

  [][]PSh : {γ δ ε : PShs} {α : PSh} (t : PShMor ε α) (σ : PShMors δ ε) (τ : PShMors γ δ) →
    t [ σ ]PSh [ τ ]PSh ≡ t [ σ ∘PSh τ ]PSh
  [][]PSh t σ τ = ≡PShMor (λ 𝓈s i → ob t (obs∘PSh σ τ 𝓈s (~ i)))

  𝑧PSh : {γ : PShs} {α : PSh} → PShMor (γ ⊹ α) α
  ob 𝑧PSh (𝓈s ⊕ 𝓈) = 𝓈
  nat 𝑧PSh f (𝓈s ⊕ 𝓈) = refl

  W₁PSh : {γ : PShs} (α : PSh) {β : PSh} → PShMor γ β → PShMor (γ ⊹ α) β
  ob (W₁PSh α t) (𝓈s ⊕ 𝓈) = ob t 𝓈s
  nat (W₁PSh α t) f (𝓈s ⊕ 𝓈) = nat t f 𝓈s

  W₁PShs : {γ δ : PShs} (α : PSh) → PShMors γ δ → PShMors (γ ⊹ α) δ
  W₁PShs α σ = map𝐸𝑙𝑠 (W₁PSh α) σ

  W₂PShs : {γ δ : PShs} (α : PSh) → PShMors γ δ → PShMors (γ ⊹ α) (δ ⊹ α)
  W₂PShs α σ = W₁PShs α σ ⊕ 𝑧PSh

  idPSh : (γ : PShs) → PShMors γ γ
  idPSh ∅ = !
  idPSh (γ ⊹ α) = W₂PShs α (idPSh γ)

  obsW : {γ δ : PShs} (α : PSh) {A : 𝑜𝑏} (σ : PShMors γ δ) (𝓈s : secs γ A) (𝓈 : sec α A) →
    obs (W₁PShs α σ) (𝓈s ⊕ 𝓈) ≡ obs σ 𝓈s
  obsW α ! 𝓈s 𝓈 = refl
  obsW α (σ ⊕ t) 𝓈s 𝓈 i = obsW α σ 𝓈s 𝓈 i ⊕ ob t 𝓈s 

  obsId : {γ : PShs} {A : 𝑜𝑏} (𝓈s : secs γ A) → obs (idPSh γ) 𝓈s ≡ 𝓈s
  obsId ! = refl
  obsId {γ = γ ⊹ α} (𝓈s ⊕ 𝓈) =
    obs (W₁PShs α (idPSh γ)) (𝓈s ⊕ 𝓈) ⊕ 𝓈
      ≡⟨ (λ i → obsW α (idPSh γ) 𝓈s 𝓈 i ⊕ 𝓈) ⟩
    obs (idPSh γ) 𝓈s ⊕ 𝓈
      ≡⟨ (λ i → obsId 𝓈s i ⊕ 𝓈) ⟩
    𝓈s ⊕ 𝓈
      ∎

  WPShLem1 : {γ δ : PShs} {α β : PSh} (t : PShMor δ β) (τ : PShMors γ δ) (s : PShMor γ α) →
    W₁PSh α t [ τ ⊕ s ]PSh ≡ t [ τ ]PSh
  WPShLem1 σ τ t = ≡PShMor (λ 𝓈s → refl)

  WPShLem2 : {γ δ ε : PShs} {α : PSh} (σ : PShMors δ ε) (τ : PShMors γ δ) (s : PShMor γ α) →
    W₁PShs α σ ∘PSh (τ ⊕ s) ≡ σ ∘PSh τ
  WPShLem2 ! τ s = refl
  WPShLem2 (σ ⊕ t) τ s i = WPShLem2 σ τ s i ⊕ WPShLem1 t τ s i

  WPShLem3 : {γ δ : PShs} {α β : PSh} (t : PShMor δ β) (σ : PShMors γ δ) →
    t [ W₁PShs α σ ]PSh ≡ W₁PSh α (t [ σ ]PSh)
  WPShLem3 {α = α} t σ = ≡PShMor (λ {(𝓈s ⊕ 𝓈) → ap (ob t) (obsW α σ 𝓈s 𝓈)})

  WPShLem4 : {γ δ ε : PShs} {α : PSh} (σ : PShMors δ ε) (τ : PShMors γ δ) →
    σ ∘PSh W₁PShs α τ ≡ W₁PShs α (σ ∘PSh τ)
  WPShLem4 ! τ = refl
  WPShLem4 (σ ⊕ t) τ i = WPShLem4 σ τ i ⊕ WPShLem3 t τ i

  𝑧PShLem : {γ δ : PShs} {α : PSh} (σ : PShMors γ δ) (t : PShMor γ α) →
    𝑧PSh [ σ ⊕ t ]PSh ≡ t
  𝑧PShLem σ t = ≡PShMor (λ 𝓈s → refl)

  idLPSh : {γ δ : PShs} (σ : PShMors γ δ) → idPSh δ ∘PSh σ ≡ σ
  idLPSh ! = refl
  idLPSh {δ = δ ⊹ α} (σ ⊕ t) =
    W₂PShs α (idPSh δ) ∘PSh (σ ⊕ t)
      ≡⟨ (λ i → WPShLem2 (idPSh δ) σ t i ⊕ 𝑧PShLem σ t i) ⟩
    (idPSh δ ∘PSh σ) ⊕ t
      ≡⟨ (λ i → idLPSh σ i ⊕ t) ⟩
    σ ⊕ t
      ∎

  id[]PSh : {γ : PShs} {α : PSh} (t : PShMor γ α) → t [ idPSh γ ]PSh ≡ t
  id[]PSh t = ≡PShMor (λ 𝓈s i → ob t (obsId 𝓈s i))

  open Contextual

  𝒫𝒮𝒽 : Contextual (lsuc ℓ) (lsuc ℓ)
  ty 𝒫𝒮𝒽 = PSh
  tm 𝒫𝒮𝒽 = PShMor
  _⟦_⟧ 𝒫𝒮𝒽 = _[_]PSh
  𝒾𝒹 𝒫𝒮𝒽 = idPSh
  𝒾𝒹L 𝒫𝒮𝒽 = idLPSh
  𝒾𝒹⟦⟧ 𝒫𝒮𝒽 = id[]PSh
  ⟦⟧⟦⟧ 𝒫𝒮𝒽 = [][]PSh
  isSetTm 𝒫𝒮𝒽 = {!!}

  record PShMorCart (α β : PSh) : Type ℓ where
    field
      ob : {A : 𝑜𝑏} → sec α A → sec β A
      nat : {A B : 𝑜𝑏} (f : 𝑚𝑜𝑟 A B) (𝓈 : sec α B) →
        ob (hom α f 𝓈) ≡ hom β f (ob 𝓈)

  open PShMorCart

  ≡PShMorCart : {α β : PSh} {t s : PShMorCart α β} →
    ({A : 𝑜𝑏} (𝓈 : sec α A) → ob t 𝓈 ≡ ob s 𝓈) → t ≡ s
  ob (≡PShMorCart p i) 𝓈 = p 𝓈 i
  nat (≡PShMorCart {α} {β} {t} {s} p i) f 𝓈 j =
    isSet→SquareP (λ i j → isSetSec β)
      (nat t f 𝓈)
      (nat s f 𝓈)
      (p (hom α f 𝓈))
      (λ k → hom β f (p 𝓈 k)) i j

  isSetPShMorCart : {α β : PSh} → isSet (PShMorCart α β)
  isSetPShMorCart = {!!}

module PresheafCCC {ℓ : Level} (𝒞 : Category ℓ ℓ) where
  open Category 𝒞
  open Presheaf 𝒞
  
  private
    module P = Contextual 𝒫𝒮𝒽

  open PSh
  open PShMor
  open PShMorCart

  よ : 𝑜𝑏 → PSh
  sec (よ A) B = 𝑚𝑜𝑟 B A
  isSetSec (よ A) = isSetMor
  hom (よ A) f g = g ⊚ f
  id-hom (よ A) f = 𝒾𝒹R f
  ⊚-hom (よ A) f g h = ⊚Assoc h f g ⁻¹

  _×PSh_ : PSh → PSh → PSh
  sec (α ×PSh β) A = sec α A × sec β A
  isSetSec (α ×PSh β) = isSet× (isSetSec α) (isSetSec β)
  hom (α ×PSh β) f (𝓈 , 𝓉) = hom α f 𝓈 , hom β f 𝓉
  id-hom (α ×PSh β) (𝓈 , 𝓉) i = id-hom α 𝓈 i , id-hom β 𝓉 i
  ⊚-hom (α ×PSh β) f g (𝓈 , 𝓉) i = ⊚-hom α f g 𝓈 i , ⊚-hom β f g 𝓉 i

  _⇒PSh_ : PSh → PSh → PSh
  sec (α ⇒PSh β) A = PShMorCart (よ A ×PSh α) β
  isSetSec (α ⇒PSh β) = isSetPShMorCart
  ob (hom (α ⇒PSh β) f t) (g , 𝓈) = ob t (f ⊚ g , 𝓈)
  nat (hom (α ⇒PSh β) f t) g (h , 𝓈) =
    ob t (f ⊚ (h ⊚ g) , hom α g 𝓈)
      ≡⟨ (λ i → ob t (⊚Assoc f h g (~ i) , hom α g 𝓈)) ⟩
    ob t (f ⊚ h ⊚ g , hom α g 𝓈)
      ≡⟨ nat t g (f ⊚ h , 𝓈) ⟩
    hom β g (ob t (f ⊚ h , 𝓈))
      ∎
  id-hom (α ⇒PSh β) t =
    ≡PShMorCart (λ {(f , 𝓈) i → ob t (𝒾𝒹L f i , 𝓈)})
  ⊚-hom (α ⇒PSh β) f g t =
    ≡PShMorCart (λ {(h , 𝓈) i → ob t (⊚Assoc f g h i , 𝓈)})

  ΛPSh : {γ : PShs} {α β : PSh} → PShMor (γ ⊹ α) β → PShMor γ (α ⇒PSh β)
  ob (ob (ΛPSh {γ} t) 𝓈s) (f , 𝓈) = ob t (homs γ f 𝓈s ⊕ 𝓈) 
  nat (ob (ΛPSh {γ} {α} {β} t) 𝓈s) f (g , 𝓈) =
    ob t (homs γ (g ⊚ f) 𝓈s ⊕ hom α f 𝓈)
      ≡⟨ (λ i → ob t (⊚-homs γ g f 𝓈s i ⊕ hom α f 𝓈)) ⟩
    ob t (homs (γ ⊹ α) f (homs γ g 𝓈s ⊕ 𝓈))
      ≡⟨ nat t f (homs γ g 𝓈s ⊕ 𝓈) ⟩
    hom β f (ob t (homs γ g 𝓈s ⊕ 𝓈))
      ∎
  nat (ΛPSh {γ} t) f 𝓈s =
    ≡PShMorCart (λ {(g , 𝓈) i → ob t (⊚-homs γ f g 𝓈s (~ i) ⊕ 𝓈)})

  AppPSh : {γ : PShs} {α β : PSh} → PShMor γ (α ⇒PSh β) → PShMor γ α → PShMor γ β
  ob (AppPSh t s) {A} 𝓈s = ob (ob t 𝓈s) (𝒾𝒹 A , ob s 𝓈s)
  nat (AppPSh {γ} {α} {β} t s) {A} {B} f 𝓈s =
    ob (ob t (homs γ f 𝓈s)) (𝒾𝒹 A , ob s (homs γ f 𝓈s))
      ≡⟨ (λ i → ob (nat t f 𝓈s i) (𝒾𝒹 A , nat s f 𝓈s i)) ⟩
    ob (ob t 𝓈s) (f ⊚ 𝒾𝒹 A , hom α f (ob s 𝓈s))
      ≡⟨ (λ i → ob (ob t 𝓈s) (𝒾𝒹L (𝒾𝒹R f i) (~ i) , hom α f (ob s 𝓈s))) ⟩
    ob (ob t 𝓈s) (𝒾𝒹 B ⊚ f , hom α f (ob s 𝓈s))
      ≡⟨ nat (ob t 𝓈s) f (𝒾𝒹 B , ob s 𝓈s) ⟩
    hom β f (ob (ob t 𝓈s) (𝒾𝒹 B , ob s 𝓈s))
      ∎

  ≡PShMor⇒ : {γ : PShs} {α β : PSh} {t s : PShMor γ (α ⇒PSh β)} →
    ({A B : 𝑜𝑏} (𝓈s : secs γ A) (f : 𝑚𝑜𝑟 B A) (𝓈 : sec α B) →
      ob (ob t 𝓈s) (f , 𝓈) ≡ ob (ob s 𝓈s) (f , 𝓈)) → t ≡ s
  ≡PShMor⇒ {t = t} p = ≡PShMor (λ 𝓈s → ≡PShMorCart (λ {(f , 𝓈) → p 𝓈s f 𝓈}))

  ΛnatPSh : {γ δ : PShs} {α β : PSh} (t : PShMor (δ ⊹ α) β) (σ : PShMors γ δ) →
    ΛPSh t P.⟦ σ ⟧ ≡ ΛPSh (t P.⟦ P.W₂tms α σ ⟧)
  ΛnatPSh {γ} {δ} {α} {β} t σ =
    ≡PShMor⇒ {α = α} {β}
      (λ 𝓈s f 𝓈 →
        ob t (homs δ f (obs σ 𝓈s) ⊕ 𝓈)
          ≡⟨ (λ i → ob t (nats σ f 𝓈s (~ i) ⊕ 𝓈)) ⟩
        ob t (obs σ (homs γ f 𝓈s) ⊕ 𝓈)
          ≡⟨ (λ i → ob t (obs σ (obsId (homs γ f 𝓈s) (~ i)) ⊕ 𝓈)) ⟩
        ob t (obs σ (obs (P.𝒾𝒹 γ) (homs γ f 𝓈s)) ⊕ 𝓈)
          ≡⟨ (λ i → ob t (obs σ (obsW α (P.𝒾𝒹 γ) (homs γ f 𝓈s) 𝓈 (~ i)) ⊕ 𝓈)) ⟩
        ob t (obs σ (obs (W₁PShs α (P.𝒾𝒹 γ)) (homs γ f 𝓈s ⊕ 𝓈)) ⊕ 𝓈)
          ≡⟨ (λ i → ob t (obs∘PSh σ (W₁PShs α (P.𝒾𝒹 γ)) (homs γ f 𝓈s ⊕ 𝓈) (~ i) ⊕ 𝓈)) ⟩
        ob t (obs (σ P.⊚ W₁PShs α (P.𝒾𝒹 γ)) (homs γ f 𝓈s ⊕ 𝓈) ⊕ 𝓈)
          ∎)

  AppβPSh : {γ : PShs} {α β : PSh} (t : PShMor (γ ⊹ α) β) (s : PShMor γ α) →
    AppPSh (ΛPSh t) s ≡ (t P.⟦ P.𝒾𝒹 γ ⊕ s ⟧)
  AppβPSh {γ} t s =
    ≡PShMor
      (λ {A} 𝓈s →
        ob t (homs γ (𝒾𝒹 A) 𝓈s ⊕ ob s 𝓈s)
          ≡⟨ (λ i → ob t (id-homs γ 𝓈s i ⊕ ob s 𝓈s)) ⟩
        ob t (𝓈s ⊕ ob s 𝓈s)
          ≡⟨ (λ i → ob t (obsId 𝓈s (~ i) ⊕ ob s 𝓈s)) ⟩
        ob t (obs (idPSh γ) 𝓈s ⊕ ob s 𝓈s)
          ∎)

  𝐴𝑝𝑝PSh : {γ : PShs} {α β : PSh} → PShMor γ (α ⇒PSh β) → PShMor (γ ⊹ α) β
  𝐴𝑝𝑝PSh {γ} {α} {β} t = AppPSh {γ ⊹ α} {α} {β} (t P.⟦ P.π ⟧) (P.𝑧)

  AppηPSh : {γ : PShs} {α β : PSh} (t : PShMor γ (α ⇒PSh β)) →
    t ≡ ΛPSh (𝐴𝑝𝑝PSh {γ} {α} {β} t)
  AppηPSh {γ} {α} {β} t =
    ≡PShMor⇒ {α = α} {β}
      (λ {Γ} {Δ} 𝓈s f 𝓈 →
        ob (ob t 𝓈s) (f , 𝓈)
          ≡⟨ (λ i → ob (ob t 𝓈s) (𝒾𝒹R f (~ i) , 𝓈)) ⟩
        ob (ob t 𝓈s) (f ⊚ 𝒾𝒹 Δ , 𝓈)
          ≡⟨ (λ i → ob (nat t f 𝓈s (~ i)) (𝒾𝒹 Δ , 𝓈)) ⟩
        ob (ob t (homs γ f 𝓈s)) (𝒾𝒹 Δ , 𝓈)
          ≡⟨ (λ i → ob (ob t (obsId (homs γ f 𝓈s) (~ i))) (𝒾𝒹 Δ , 𝓈)) ⟩
        ob (ob t (obs (idPSh γ) (homs γ f 𝓈s))) (𝒾𝒹 Δ , 𝓈)
          ≡⟨ (λ i → ob (ob t (obsW α (idPSh γ) (homs γ f 𝓈s) 𝓈 (~ i))) (𝒾𝒹 Δ , 𝓈)) ⟩
        ob (ob t (obs (W₁PShs α (idPSh γ)) (homs γ f 𝓈s ⊕ 𝓈))) (𝒾𝒹 Δ , 𝓈)
          ∎)

  open CCC

  𝒫𝒮𝒽CCC : CCC 𝒫𝒮𝒽
  _⇛_ 𝒫𝒮𝒽CCC = _⇒PSh_
  Λ 𝒫𝒮𝒽CCC = ΛPSh
  𝑎𝑝𝑝 𝒫𝒮𝒽CCC = AppPSh
  Λnat 𝒫𝒮𝒽CCC = ΛnatPSh
  𝑎𝑝𝑝β 𝒫𝒮𝒽CCC = AppβPSh
  𝑎𝑝𝑝η 𝒫𝒮𝒽CCC {γ} {α} {β} = AppηPSh {γ} {α} {β}

{-module PShWeave {ℓ : Level} (𝒞 : Category ℓ ℓ) where
  open Presheaf 𝒞
  open Category 𝒞
  open PSh
  open PShMor

  record PShMorCart (α β : PSh) : Type ℓ where
    field
      ob : {A : 𝑜𝑏} → sec α A → sec β A
      nat : {A B : 𝑜𝑏} (f : 𝑚𝑜𝑟 A B) (𝓈 : sec α B) →
        ob (hom α f 𝓈) ≡ hom β f (ob 𝓈)

  open PShMorCart

  ≡PShMorCart : {α β : PSh} {t s : PShMorCart α β} →
    ({A : 𝑜𝑏} (𝓈 : sec α A) → ob t 𝓈 ≡ ob s 𝓈) → t ≡ s
  ob (≡PShMorCart p i) 𝓈 = p 𝓈 i
  nat (≡PShMorCart {α} {β} {t} {s} p i) f 𝓈 j =
    isSet→SquareP (λ i j → isSetSec β)
      (nat t f 𝓈)
      (nat s f 𝓈)
      (p (hom α f 𝓈))
      (λ k → hom β f (p 𝓈 k)) i j

  WγPSh : {α β : PSh} (γ : PShs) → PShMorCart α β → PShMor (γ ⊹ α) β
  ob (WγPSh γ t) (𝓈s ⊕ 𝓈) = ob t 𝓈
  nat (WγPSh γ t) f (𝓈s ⊕ 𝓈) = nat t f 𝓈

  _⊗PSh_ : {γ δ : PShs} {α β : PSh} → PShMors γ δ → PShMorCart α β → PShMors (γ ⊹ α) (δ ⊹ β)
  _⊗PSh_ {γ} {δ} {α} σ t = W₁PShs α σ ⊕ WγPSh γ t

  module _ {ℓ₁} {ty : Type ℓ₁} where
    PShFamily = ty → PSh
    PShsFamily = 𝐶𝑡𝑥 ty → PShs

    plurify : PShFamily → PShsFamily
    plurify 𝒫 = map𝐶𝑡𝑥 𝒫

    ⟪secs⟫ : (𝒫 : PShFamily) (Γ : 𝐶𝑡𝑥 ty) → 𝑜𝑏 → Type (ℓ ⊔ ℓ₁)
    ⟪secs⟫ 𝒫 Γ A = 𝐸𝑙𝑠 (λ B → sec (𝒫 B) A) Γ

    ⇓ : {𝒫 : PShFamily} {Γ : 𝐶𝑡𝑥 ty} {A : 𝑜𝑏} →
      secs (plurify 𝒫 Γ) A → ⟪secs⟫ 𝒫 Γ A
    ⇓ {Γ = ∅} 𝓈s = !
    ⇓ {Γ = Γ ⊹ A} (𝓈s ⊕ 𝓈) = ⇓ 𝓈s ⊕ 𝓈

    ⇑ : {𝒫 : PShFamily} {Γ : 𝐶𝑡𝑥 ty} {A : 𝑜𝑏} →
      ⟪secs⟫ 𝒫 Γ A → secs (plurify 𝒫 Γ) A
    ⇑ ! = !
    ⇑ (𝓈s ⊕ 𝓈) = ⇑ 𝓈s ⊕ 𝓈

    ⇓hom : {𝒫 : PShFamily} {Γ : 𝐶𝑡𝑥 ty} {A B : 𝑜𝑏} (f : 𝑚𝑜𝑟 A B) (𝓈s : secs (plurify 𝒫 Γ) B) →
      ⇓ (homs (plurify 𝒫 Γ) f 𝓈s) ≡ map𝐸𝑙𝑠 (λ {C} → hom (𝒫 C) f) (⇓ 𝓈s)
    ⇓hom {Γ = ∅} f 𝓈s = refl
    ⇓hom {𝒜} {Γ ⊹ A} f (𝓈s ⊕ 𝓈) i = ⇓hom f 𝓈s i ⊕ hom (𝒜 A) f 𝓈

    MorFamily : (𝒫 𝒬 : PShFamily) → Type (ℓ ⊔ ℓ₁)
    MorFamily 𝒫 𝒬 = (A : ty) → PShMorCart (𝒫 A) (𝒬 A)

    weaveMor : {𝒫 𝒬 : PShFamily} (𝒜 : MorFamily 𝒫 𝒬) →
      (Γ : 𝐶𝑡𝑥 ty) → PShMors (plurify 𝒫 Γ) (plurify 𝒬 Γ)
    weaveMor 𝒜 ∅ = !
    weaveMor 𝒜 (Γ ⊹ A) = weaveMor 𝒜 Γ ⊗PSh 𝒜 A

    ⟪obs⟫ : {𝒫 𝒬 : PShFamily} (𝒜 : MorFamily 𝒫 𝒬) (Γ : 𝐶𝑡𝑥 ty) {A : 𝑜𝑏} →
      ⟪secs⟫ 𝒫 Γ A → ⟪secs⟫ 𝒬 Γ A
    ⟪obs⟫ 𝒜 Γ 𝓈s = map𝐸𝑙𝑠 (λ {B} → ob (𝒜 B)) 𝓈s

    ⇓⇑ : {𝒫 𝒬 : PShFamily} (𝒜 : MorFamily 𝒫 𝒬) {Γ : 𝐶𝑡𝑥 ty} {A : 𝑜𝑏}
      (𝓈s : 𝐸𝑙𝑠 (λ B → sec (𝒫 B) A) Γ) →
      ⇓ (obs (weaveMor 𝒜 Γ) (⇑ 𝓈s)) ≡ ⟪obs⟫ 𝒜 Γ 𝓈s
    ⇓⇑ 𝒜 ! = refl
    ⇓⇑ {𝒫} 𝒜 {Γ = Γ ⊹ A} (𝓈s ⊕ 𝓈) =
      ⇓ (obs (W₁PShs (𝒫 A) (weaveMor 𝒜 Γ)) (⇑ 𝓈s ⊕ 𝓈)) ⊕ ob (𝒜 A) 𝓈
        ≡⟨ (λ i → ⇓ (obsW (𝒫 A) (weaveMor 𝒜 Γ) (⇑ 𝓈s) 𝓈 i) ⊕ ob (𝒜 A) 𝓈) ⟩
      ⇓ (obs (weaveMor 𝒜 Γ) (⇑ 𝓈s)) ⊕ ob (𝒜 A) 𝓈
        ≡⟨ (λ i → ⇓⇑ 𝒜 𝓈s i ⊕ ob (𝒜 A) 𝓈) ⟩
      map𝐸𝑙𝑠 (λ {B} → ob (𝒜 B)) 𝓈s ⊕ ob (𝒜 A) 𝓈
        ∎

  infixl 20 _∘𝒩_
  _∘𝒩_ : {α β ζ : PSh} → PShMorCart β ζ → PShMorCart α β → PShMorCart α ζ
  ob (t ∘𝒩 s) 𝓈 = ob t (ob s 𝓈)
  nat (_∘𝒩_ {α} {β} {ζ} t s) f 𝓈 =
    ob t (ob s (hom α f 𝓈))
      ≡⟨ ap (ob t) (nat s f 𝓈) ⟩
    ob t (hom β f (ob s 𝓈))
      ≡⟨ nat t f (ob s 𝓈) ⟩
    hom ζ f (ob t (ob s 𝓈))
      ∎

  ∘𝒩Assoc : {α β ζ ξ : PSh} (t : PShMorCart ζ ξ) (s : PShMorCart β ζ) (r : PShMorCart α β) →
    (t ∘𝒩 s) ∘𝒩 r ≡ t ∘𝒩 (s ∘𝒩 r)
  ∘𝒩Assoc t s r = ≡PShMorCart (λ 𝓈 → refl)

  infixl 20 _[_]PShCart
  _[_]PShCart : {γ : PShs} {α β : PSh} → PShMorCart α β → PShMor γ α → PShMor γ β
  ob (t [ s ]PShCart) 𝓈s = ob t (ob s 𝓈s)
  nat (_[_]PShCart {γ} {α} {β} t s) f 𝓈s =
    ob t (ob s (homs γ f 𝓈s))
      ≡⟨ ap (ob t) (nat s f 𝓈s) ⟩
    ob t (hom α f (ob s 𝓈s))
      ≡⟨ nat t f (ob s 𝓈s) ⟩
    hom β f (ob t (ob s 𝓈s))
      ∎

  WγPShLem : {α β : PSh} {γ δ : PShs} (t : PShMorCart α β) (τ : PShMors γ δ) (s : PShMor γ α) →
    WγPSh δ t [ τ ⊕ s ]PSh ≡ t [ s ]PShCart
  WγPShLem t τ s = ≡PShMor (λ 𝓈s → refl)

  []WγPShCart : {γ : PShs} {α β ζ : PSh} (t : PShMorCart β ζ) (s : PShMorCart α β) →
    t [ WγPSh γ s ]PShCart ≡ WγPSh γ (t ∘𝒩 s)
  []WγPShCart t s = ≡PShMor (λ {(𝓈s ⊕ 𝓈) → refl})
  
  ⊗lem1 : {γ δ ε : PShs} {α β : PSh} (σ : PShMors δ ε) (t : PShMorCart α β)
    (τ : PShMors γ δ) (s : PShMor γ α) →
    (σ ⊗PSh t) ∘PSh (τ ⊕ s) ≡ (σ ∘PSh τ) ⊕ (t [ s ]PShCart)
  ⊗lem1 σ t τ s i = WPShLem2 σ τ s i ⊕ WγPShLem t τ s i

  ⊗lem2 : {γ δ ε : PShs} {α β ζ : PSh} (σ : PShMors δ ε) (t : PShMorCart β ζ)
    (τ : PShMors γ δ) (s : PShMorCart α β) →
    (σ ⊗PSh t) ∘PSh (τ ⊗PSh s) ≡ (σ ∘PSh τ) ⊗PSh (t ∘𝒩 s)
  ⊗lem2 {γ = γ} {α = α} σ t τ s =
    (σ ⊗PSh t) ∘PSh (τ ⊗PSh s)
      ≡⟨ (λ i → WPShLem2 σ (W₁PShs α τ) (WγPSh γ s) i ⊕ WγPShLem t (W₁PShs α τ) (WγPSh γ s) i) ⟩
    (σ ∘PSh W₁PShs α τ) ⊕ (t [ WγPSh γ s ]PShCart)
      ≡⟨ (λ i → WPShLem4 σ τ i ⊕ []WγPShCart t s i) ⟩
    (σ ∘PSh τ) ⊗PSh (t ∘𝒩 s)
      ∎

  ⊗IndLem : {γ δ : PShs} {α β : PSh} (σ : PShMors γ δ) (t : PShMorCart α β)
    {A : 𝑜𝑏} (𝓈s : secs γ A) (𝓈 : sec α A) →
    obs (σ ⊗PSh t) (𝓈s ⊕ 𝓈) ≡ obs σ 𝓈s ⊕ ob t 𝓈
  ⊗IndLem {α = α} σ t 𝓈s 𝓈 i = obsW α σ 𝓈s 𝓈 i ⊕ ob t 𝓈-}
