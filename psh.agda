{-# OPTIONS --cubical --allow-unsolved-metas #-}

module psh where

open import contextual
open import ccc
open import cart

open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets hiding (isSetLift)
open import Cubical.Data.Unit as ⊤ renaming (Unit to ⊤)
open import Cubical.Data.Empty as ⊥

-- In this file, we exhibit the Cartesian Closed structure of presheaves

private
  isSetLift : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → isSet A → isSet (Lift {ℓ₁} {ℓ₂} A)
  isSetLift p (lift x) (lift y) a b = ap (ap lift) (p x y (ap lower a) (ap lower b))

  isSet→ : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) {B : Set ℓ₂} → isSet B → isSet (A → B)
  isSet→ A p f g α β i j x = p (f x) (g x) (λ k → α k x) (λ k → β k x) i j

-- First we establish some easy structure of SET

module SETCartesian {ℓ : Level} where
  open Precategory

  1SET : ob (SET ℓ)
  1SET = Lift ⊤ , isSetLift isSetUnit

  infixl 20 _×SET_
  _×SET_ : (A B : ob (SET ℓ)) → ob (SET ℓ)
  (A , p) ×SET (B , q) = (A × B) , isSet× p q

  infixl 15 _⇒SET_
  _⇒SET_ : (A B : ob (SET ℓ)) → ob (SET ℓ)
  (A , _) ⇒SET (B , q) = (A → B) , isSet→ A q

-- Onto presheaves

module _ where
  open import Cubical.Categories.Presheaf

  PSh : ∀ {ℓ} (𝒞 : Precategory ℓ ℓ) → ⦃ isCategory 𝒞 ⦄ → Precategory (lsuc ℓ) ℓ
  PSh {ℓ} 𝒞  = PreShv 𝒞 ℓ

module PShCartesian {ℓ : Level} (𝒞 : Precategory ℓ ℓ) ⦃ C-cat : isCategory 𝒞 ⦄ where
  open import Cubical.Categories.NaturalTransformation
  open Precategory
  open Functor
  open NatTrans
  open SETCartesian
  open import Cubical.Categories.Presheaf

  private
    C = 𝒞
    ℐ𝒹 = Precategory.id C
    _𝒩∘_ = comp' (PSh 𝒞)
    infixl 15 _★_
    _★_ = C ._⋆_

  よ : ob C → ob (PSh 𝒞)
  よ = Yoneda.yo C

  -- Terminal Object

  1PSh : ob (PSh 𝒞)
  1PSh .F-ob x = 1SET
  1PSh .F-hom x t = t
  1PSh .F-id = refl
  1PSh .F-seq a b = refl

  !PSh : {F : ob (PSh 𝒞)} → PSh 𝒞 [ F , 1PSh ]
  !PSh .N-ob x t = lift tt
  !PSh .N-hom a = refl

  !ηPSh : {F : ob (PSh 𝒞)} → (α : PSh 𝒞 [ F , 1PSh ]) → α ≡ !PSh
  !ηPSh α i .N-ob x t = lift tt
  !ηPSh α i .N-hom a = refl

  -- Products

  ×PSh : ob (PSh 𝒞) → ob (PSh 𝒞) → ob (PSh 𝒞)
  ×PSh F G .F-ob x = F ⟅ x ⟆ ×SET G ⟅ x ⟆
  ×PSh F G .F-hom a (t , s) = F-hom F a t , F-hom G a s
  ×PSh F G .F-id i (t , s) = F-id F i t , F-id G i s
  ×PSh F G .F-seq a b i (t , s) = F-seq F a b i t , F-seq G a b i s

  PairPSh : {F G H : ob (PSh 𝒞)} → PSh 𝒞 [ F , G ] → PSh 𝒞 [ F , H ] →
    PSh 𝒞 [ F , ×PSh G H ]
  PairPSh α β .N-ob x t = N-ob α x t , N-ob β x t
  PairPSh α β .N-hom a i t = N-hom α a i t , N-hom β a i t

  π₁PSh : (F G : ob (PSh 𝒞)) → PSh 𝒞 [ ×PSh F G , F ]
  π₁PSh F G .N-ob x (t , s) = t
  π₁PSh F G .N-hom a = refl

  π₁βPSh : {F G H : ob (PSh 𝒞)} (α : PSh 𝒞 [ F , G ]) (β : PSh 𝒞 [ F , H ]) →
    π₁PSh G H 𝒩∘ PairPSh α β ≡ α
  π₁βPSh α β i .N-ob = N-ob α
  π₁βPSh {F} {G} {H} α β i .N-hom {x} {y} a j t =
    isSet→SquareP (λ i j → snd (F-ob G y))
      (λ k → (π₁PSh G H 𝒩∘ PairPSh α β) .N-hom a k t)
      (λ k → N-hom α a k t)
      (λ k → N-ob α y (F-hom F a t))
      (λ k → F-hom G a (N-ob α x t)) i j

  π₂PSh : (F G : ob (PSh 𝒞)) → PSh 𝒞 [ ×PSh F G , G ]
  π₂PSh F G .N-ob x (t , s) = s
  π₂PSh F G .N-hom a = refl

  π₂βPSh : {F G H : ob (PSh 𝒞)} (α : PSh 𝒞 [ F , G ]) (β : PSh 𝒞 [ F , H ]) →
    π₂PSh G H 𝒩∘ PairPSh α β ≡ β
  π₂βPSh α β i .N-ob = N-ob β
  π₂βPSh {F} {G} {H} α β i .N-hom {x} {y} a j t =
    isSet→SquareP (λ i j → snd (F-ob H y))
      (λ k → (π₂PSh G H 𝒩∘ PairPSh α β) .N-hom a k t)
      (λ k → N-hom β a k t)
      (λ k → N-ob β y (F-hom F a t))
      (λ k → F-hom H a (N-ob β x t)) i j

  πηPSh : (F G H : ob (PSh 𝒞)) (α : PSh 𝒞 [ F , ×PSh G H ]) →
    PairPSh (π₁PSh G H 𝒩∘ α) (π₂PSh G H 𝒩∘ α) ≡ α
  πηPSh F G H α i .N-ob x t = N-ob α x t
  πηPSh F G H α i .N-hom {x} {y} a j t =
    isSet→SquareP (λ i j → snd (G ⟅ y ⟆ ×SET H ⟅ y ⟆))
      (λ k → PairPSh (π₁PSh G H 𝒩∘ α) (π₂PSh G H 𝒩∘ α) .N-hom a k t)
      (λ k → N-hom α a k t)
      (λ k → N-ob α y (F-hom F a t))
      (λ k → F-hom G a (fst (N-ob α x t)) , F-hom H a (snd (N-ob α x t))) i j

  -- Exponentials

  ⇒PSh : ob (PSh 𝒞) → ob (PSh 𝒞) → ob (PSh 𝒞)
  ⇒PSh F G .F-ob x = PSh 𝒞 [ ×PSh (よ x) F , G ] , isSetNat
  ⇒PSh F G .F-hom a α .N-ob x (b , t) = N-ob α x (b ⋆⟨ C ⟩ a , t)
  ⇒PSh F G .F-hom a α .N-hom b i (c , t) =
    (N-ob α _ (b ★ c ★ a , F-hom F b t)
      ≡⟨ (λ j → N-ob α _ (⋆Assoc C b c a j , F-hom F b t)) ⟩
    N-ob α _ (b ★ (c ★ a) , F-hom F b t)
      ≡⟨ (λ j → N-hom α b j (c ★ a , t)) ⟩
    F-hom G b (N-ob α _ (c ★ a , t))
      ∎) i
  ⇒PSh F G .F-id i α .N-ob x (a , t) = N-ob α x (⋆IdR C a i , t)
  ⇒PSh F G .F-id {x} i α .N-hom {y₁} {y₂} a j (b , t) =
    isSet→SquareP (λ i j → snd (F-ob G y₂))
      (λ k → F-hom (⇒PSh F G) (ℐ𝒹 x) α .N-hom a k (b , t))
      (λ k → N-hom α a k (b , t))
      (λ k → N-ob α y₂ (⋆IdR C (a ★ b) k , F-hom F a t))
      (λ k → F-hom G a (N-ob α y₁ (⋆IdR C b k , t))) i j
  ⇒PSh F G .F-seq a b i α .N-ob x (c , t) = N-ob α x (⋆Assoc C c b a (~ i) , t)
  ⇒PSh F G .F-seq a b i α .N-hom {z₁} {z₂} c j (d , t) =
    isSet→SquareP (λ i j → snd (F-ob G z₂))
      (λ k → F-hom (⇒PSh F G) (b ★ a) α .N-hom c k (d , t))
      (λ k → F-hom (⇒PSh F G) b (F-hom (⇒PSh F G) a α) .N-hom c k (d , t))
      (λ k → N-ob α z₂ (⋆Assoc C (c ★ d) b a (~ k) , F-hom F c t))
      (λ k → F-hom G c (N-ob α z₁ (⋆Assoc C d b a (~ k) , t))) i j

  ΛPSh : (F G H : ob (PSh 𝒞)) → PSh 𝒞 [ ×PSh F G , H ] → PSh 𝒞 [ F , ⇒PSh G H ]
  ΛPSh F G H α .N-ob x t .N-ob y (a , s) = N-ob α y (F-hom F a t , s)
  ΛPSh F G H α .N-ob x t .N-hom a i (b , s) =
    (N-ob α _ (F-hom F (a ★ b) t , F-hom G a s)
      ≡⟨ (λ j → N-ob α _ (F-seq F b a j t , F-hom G a s)) ⟩
    N-ob α _ (F-hom F a (F-hom F b t) , F-hom G a s)
      ≡⟨ (λ j → N-hom α a j (F-hom F b t , s)) ⟩
    F-hom H a (N-ob α _ (F-hom F b t , s))
      ∎) i
  ΛPSh F G H α .N-hom a i t .N-ob x (b , s) = N-ob α x (F-seq F a b (~ i) t , s)
  ΛPSh F G H α .N-hom {x₁} {x₂} a i t .N-hom {y₁} {y₂} b j (c , s) =
    isSet→SquareP (λ i j → snd (F-ob H y₂))
     (λ k → (N-ob (ΛPSh F G H α) x₂ (F-hom F a t)) .N-hom b k (c , s))
     (λ k → (F-hom (⇒PSh G H) a (N-ob (ΛPSh F G H α) x₁ t)) .N-hom b k (c , s))
     (λ k → N-ob α y₂ (F-seq F a (b ★ c) (~ k) t , F-hom G b s))
     (λ k → F-hom H b (N-ob α y₁ (F-seq F a c (~ k) t , s))) i j

  AppPSh : (F G H : ob (PSh 𝒞)) → PSh 𝒞 [ F , ⇒PSh G H ] → PSh 𝒞 [ F , G ] → PSh 𝒞 [ F , H ]
  AppPSh F G H α β .N-ob x t = N-ob (N-ob α x t) x (ℐ𝒹 x , N-ob β x t)
  AppPSh F G H α β .N-hom {x₁} {x₂} a i t =
    (N-ob (N-ob α x₂ (F-hom F a t)) x₂ (ℐ𝒹 x₂ , N-ob β x₂ (F-hom F a t))
      ≡⟨ (λ k → N-ob (N-hom α a k t) x₂ (ℐ𝒹 x₂ , N-hom β a k t )) ⟩
    N-ob (N-ob α x₁ t) x₂ (ℐ𝒹 x₂ ★ a , F-hom G a (N-ob β x₁ t))
      ≡⟨ (λ k → N-ob (N-ob α x₁ t) x₂ (⋆IdL C a k , F-hom G a (N-ob β x₁ t))) ⟩
    N-ob (N-ob α x₁ t) x₂ (a , F-hom G a (N-ob β x₁ t))
      ≡⟨ (λ k → N-ob (N-ob α x₁ t) x₂ (⋆IdR C a (~ k) , F-hom G a (N-ob β x₁ t))) ⟩
    N-ob (N-ob α x₁ t) x₂ (a ★ ℐ𝒹 x₁ , F-hom G a (N-ob β x₁ t))
      ≡⟨ (λ k → N-hom (N-ob α x₁ t) a k (ℐ𝒹 x₁ , N-ob β x₁ t)) ⟩
    F-hom H a (N-ob (N-ob α x₁ t) x₁ (ℐ𝒹 x₁ , N-ob β x₁ t))
      ∎) i

  eval : (F G : ob (PSh 𝒞)) → PSh 𝒞 [ ×PSh (⇒PSh F G) F , G ]
  eval F G = AppPSh (×PSh (⇒PSh F G) F) F G (π₁PSh (⇒PSh F G) F) (π₂PSh (⇒PSh F G) F)

  ΛnatPSh : (F F' G H : ob (PSh 𝒞)) (α : PSh 𝒞 [ F , F' ]) (β : PSh 𝒞 [ ×PSh F' G , H ]) →
    ΛPSh F G H (β 𝒩∘ PairPSh (α 𝒩∘ π₁PSh F G) (π₂PSh F G)) ≡ ΛPSh F' G H β 𝒩∘ α
  ΛnatPSh F F' G H α β i .N-ob x t .N-ob y (a , s) = N-ob β y (N-hom α a i t , s)
  ΛnatPSh F F' G H α β i .N-ob x t .N-hom {x₁} {x₂} a j (b , s) =
    isSet→SquareP (λ i j → snd (F-ob H x₂))
      (λ k →
        N-hom (N-ob (ΛPSh F G H (β 𝒩∘ PairPSh (α 𝒩∘ π₁PSh F G) (π₂PSh F G))) x t) a k (b , s))
      (λ k → N-hom (N-ob (ΛPSh F' G H β 𝒩∘ α) x t) a k (b , s))
      (λ k → N-ob β x₂ (N-hom α (a ★ b) k t , F-hom G a s))
      (λ k → F-hom H a (N-ob β x₁ (N-hom α b k t , s))) i j
  ΛnatPSh F F' G H α β i .N-hom {x₁} {x₂} a j t =
    isSet→SquareP (λ i j → isSetNat)
      (λ k → N-hom (ΛPSh F G H (β 𝒩∘ PairPSh (α 𝒩∘ π₁PSh F G) (π₂PSh F G))) a k t)
      (λ k → N-hom (ΛPSh F' G H β 𝒩∘ α) a k t)
      (λ k → N-ob (ΛnatPSh F F' G H α β k) x₂ (F-hom F a t))
      (λ k → F-hom (⇒PSh G H) a (N-ob (ΛnatPSh F F' G H α β k) x₁ t)) i j

  AppβPSh : (F G H : ob (PSh 𝒞)) (α : PSh 𝒞 [ ×PSh F G , H ]) (β : PSh 𝒞 [ F , G ]) →
    AppPSh F G H (ΛPSh F G H α) β ≡ α 𝒩∘ (PairPSh (idTrans F) β)
  AppβPSh F G H α β i .N-ob x t = N-ob α x (F-id F i t , N-ob β x t)
  AppβPSh F G H α β i .N-hom {x₁} {x₂} a j t =
    isSet→SquareP (λ i j → snd (F-ob H x₂))
      (λ k → N-hom (AppPSh F G H (ΛPSh F G H α) β) a k t)
      (λ k → N-hom (α 𝒩∘ (PairPSh (idTrans F) β)) a k t)
      (λ k → N-ob α x₂ (F-id F k (F-hom F a t) , N-ob β x₂ (F-hom F a t)))
      (λ k → F-hom H a (N-ob α x₁ (F-id F k t , N-ob β x₁ t))) i j

  AppηPSh : (F G H : ob (PSh 𝒞)) (α : PSh 𝒞 [ F , ⇒PSh G H ]) →
    ΛPSh F G H (AppPSh (×PSh F G) G H (α 𝒩∘ π₁PSh F G) (π₂PSh F G)) ≡ α
  AppηPSh F G H α i .N-ob x t .N-ob y (a , s) =
    (N-ob (N-ob α y (F-hom F a t)) y (ℐ𝒹 y , s)
      ≡⟨ (λ k → N-ob (N-hom α a k t) y (ℐ𝒹 y , s)) ⟩
    N-ob (N-ob α x t) y (ℐ𝒹 y ★ a , s)
      ≡⟨ (λ k → N-ob (N-ob α x t) y (⋆IdL C a k , s)) ⟩
    N-ob (N-ob α x t) y (a , s)
      ∎) i
  AppηPSh F G H α i .N-ob x t .N-hom {y₁} {y₂} a j (b , s) =
    isSet→SquareP (λ i j → snd (F-ob H y₂))
     (λ k → N-hom (N-ob
         (ΛPSh F G H (AppPSh (×PSh F G) G H (α 𝒩∘ π₁PSh F G) (π₂PSh F G))) x t) a k (b , s))
     (λ k → N-hom (N-ob α x t) a k (b , s))
     (λ k → (N-ob (AppηPSh F G H α k .N-ob x t) y₂) (F-hom (×PSh (よ x) G) a (b , s)))
     (λ k → (F-hom H a) (N-ob (N-ob (AppηPSh F G H α k) x t) y₁ (b , s))) i j
  AppηPSh F G H α i .N-hom {y₁} {y₂} a j t =
    isSet→SquareP (λ i j → isSetNat)
      (λ k → N-hom (ΛPSh F G H (AppPSh (×PSh F G) G H (seqTrans (π₁PSh F G) α) (π₂PSh F G))) a k t)
      (λ k → N-hom α a k t)
      (λ k → N-ob (AppηPSh F G H α k) y₂ (F-hom F a t))
      (λ k → F-hom (⇒PSh G H) a (N-ob (AppηPSh F G H α k) y₁ t)) i j

module _ {ℓ : Level} {𝒞 : Precategory ℓ ℓ} ⦃ C-cat : isCategory 𝒞 ⦄ where
  open import Cubical.Categories.Presheaf
  open PShCartesian 𝒞
  open Cartesian

  instance
    PShCat : isCategory (PSh 𝒞)
    PShCat = isCatPreShv {C = 𝒞}

  instance
    PShCart : Cartesian (PSh 𝒞)
    PShCart .C-1 = 1PSh
    PShCart .C-! = !PSh
    PShCart .C-!η = !ηPSh
    PShCart .C-× = ×PSh
    PShCart .C-pair = PairPSh
    PShCart .C-π₁ = π₁PSh
    PShCart .C-π₂ = π₂PSh
    PShCart .C-π₁β = π₁βPSh
    PShCart .C-π₂β = π₂βPSh
    PShCart .C-πη = πηPSh
    PShCart .C-⇒ = ⇒PSh
    PShCart .C-Λ = ΛPSh
    PShCart .C-App = AppPSh
    PShCart .C-Λnat = ΛnatPSh
    PShCart .C-Appβ = AppβPSh
    PShCart .C-Appη F G H α = AppηPSh F G H α ⁻¹

module _ {ℓ : Level} (𝒞 : Precategory ℓ ℓ) ⦃ C-cat : isCategory 𝒞 ⦄ where
   open CartToCCC (PSh 𝒞)

   𝒫𝒮𝒽 = ambCC
   𝒫𝒮𝒽CCC = ambCCC

open import ren

module _ where
  open Contextual (𝒫𝒮𝒽 REN)
  open Precategory (PSh REN) hiding (_∘_)
  open CartToCCC (PSh REN)
  open CCC (𝒫𝒮𝒽CCC REN)

  private
    module C = Contextual ρεν
    
  infixr 20 _𝒩∘_
  _𝒩∘_ = comp' (PSh REN ⦃ C.isCatAmbCat ⦄)

  PresheafFamily = C.ty → ob
  PresheavesFamily = C.ctx → ctx

  plurify : PresheafFamily → PresheavesFamily
  plurify 𝒫 = map𝐶𝑡𝑥 𝒫

  TransFamily : (𝒫 𝒬 : PresheafFamily) → Type lzero
  TransFamily 𝒫 𝒬 = (A : C.ty) → Hom[ 𝒫 A , 𝒬 A ]

  infixl 30 _×tm_
  _×tm_ : {Γ Δ : ctx} {A B : ty} → tms Γ Δ → Hom[ A , B ] → tms (Γ ⊹ A) (Δ ⊹ B)
  _×tm_ {Γ} σ t = σ ⊚ π ⊕ (t 𝒩∘ (𝑧 {Γ}))
  
  weaveTrans : {𝒫 𝒬 : PresheafFamily} (𝒜 : TransFamily 𝒫 𝒬) →
    (Γ : C.ctx) → tms (plurify 𝒫 Γ) (plurify 𝒬 Γ)
  weaveTrans 𝒜 ∅ = !
  weaveTrans 𝒜 (Γ ⊹ A) = weaveTrans 𝒜 Γ ×tm 𝒜 A

  ×tmLem1 : {Γ Δ Σ : ctx} {A B : ty} (σ : tms Δ Σ) (t : Hom[ A , B ])
    (τ : tms Γ Δ) (s : tm Γ A ) →
    (σ ×tm t) ⊚ (τ ⊕ s) ≡ (σ ⊚ τ) ⊕ (t 𝒩∘ s)
  ×tmLem1 {Γ} {Δ} σ t τ s =
    σ ⊚ π ⊕ (t 𝒩∘ 𝑧 {Δ}) ⊚ (τ ⊕ s)
      ≡⟨ ⊕⊚ (σ ⊚ π) (t 𝒩∘ 𝑧 {Δ}) (τ ⊕ s) ⟩
    σ ⊚ π ⊚ (τ ⊕ s) ⊕ (t 𝒩∘ 𝑧 {Δ}) ⟦ τ ⊕ s ⟧
      ≡⟨ (λ i → ⊚Assoc σ π (τ ⊕ s) i ⊕ ⊚πlem t τ s i) ⟩
    σ ⊚ (π ⊚ (τ ⊕ s)) ⊕ (t 𝒩∘ s)
      ≡⟨ (λ i → σ ⊚ (πβ (τ ⊕ s) i) ⊕ (t 𝒩∘ s)) ⟩
    σ ⊚ τ ⊕ (t 𝒩∘ s)
      ∎

  ×tmLem2 : {Γ Δ Σ : ctx} {A B C : ty} (σ : tms Δ Σ) (t : Hom[ B , C ])
    (τ : tms Γ Δ) (s : Hom[ A , B ]) →
    (σ ×tm t) ⊚ (τ ×tm s) ≡ (σ ⊚ τ) ×tm (t 𝒩∘ s)
  ×tmLem2 {Γ} {Δ} σ t τ s =
    (σ ×tm t) ⊚ (τ ⊚ π ⊕ (s 𝒩∘ (𝑧 {Γ})))
      ≡⟨ ×tmLem1 σ t (τ ⊚ π) (s 𝒩∘ (𝑧 {Γ})) ⟩
    σ ⊚ (τ ⊚ π) ⊕ (t 𝒩∘ s 𝒩∘ (𝑧 {Γ}))
      ≡⟨ (λ i → ⊚Assoc σ τ π (~ i) ⊕ ⋆Assoc (𝑧 {Γ}) s t i) ⟩
    (σ ⊚ τ) ×tm (t 𝒩∘ s)
      ∎

  ⇓PSh = ⇓ctx
  ⇓PShMor = ⇓tms
  ⇓∘PShMor = ⇓∘tms
  ⇓πPSh = ⇓π
  ⇓idPSh = ⇓idtms

  
