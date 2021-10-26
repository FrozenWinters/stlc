{-# OPTIONS --cubical --allow-unsolved-metas #-}

module syn2 where

open import cartesian

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Agda.Builtin.Char
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything renaming (cong to ap)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ public
open import Cubical.Data.Unit as ⊤ renaming (Unit to ⊤)
open import Cubical.Data.List renaming ([_] to ⟦_⟧)

infixr 20 _⇒_
data Ty : Set where
  Base : Char → Ty
  _⇒_ : Ty → Ty → Ty

infixl 20 _⊹_
data Ctx : Set where
  ∅ : Ctx
  _⊹_ : Ctx → Ty → Ctx

data Var : Ctx → Ty → Set where
  Zv : {Γ : Ctx} {A : Ty} → Var (Γ ⊹ A) A
  Sv : {Γ : Ctx} {A B : Ty} → Var Γ A → Var (Γ ⊹ B) A

infixl 20 _⊕R_
data Ren : Ctx → Ctx → Set where
  !R : {Γ : Ctx} → Ren Γ ∅
  _⊕R_ : {Γ Δ : Ctx} {A : Ty} → Ren Γ Δ → Var Γ A → Ren Γ (Δ ⊹ A)

W₁Ren : {Γ Δ : Ctx} (A : Ty) → Ren Γ Δ → Ren (Γ ⊹ A) Δ
W₁Ren A !R = !R
W₁Ren A (σ ⊕R v) = W₁Ren A σ ⊕R Sv v

W₂Ren : {Γ Δ : Ctx} (A : Ty) → Ren Γ Δ → Ren (Γ ⊹ A) (Δ ⊹ A)
W₂Ren A σ = W₁Ren A σ ⊕R Zv

idRen : (Γ : Ctx) → Ren Γ Γ
idRen ∅ = !R
idRen (Γ ⊹ A) = W₂Ren A (idRen Γ)

data Tm : Ctx → Ty → Set
data Tms : Ctx → Ctx → Set

infixl 20 _∘Tms_
_∘Tms_ : {Γ Δ Σ : Ctx} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
idTms : (Γ : Ctx) → Tms Γ Γ
W₁Tms : {Γ Δ : Ctx} (A : Ty) → Tms Γ Δ → Tms (Γ ⊹ A) Δ
W₂Tms : {Γ Δ : Ctx} (A : Ty) → Tms Γ Δ → Tms (Γ ⊹ A) (Δ ⊹ A)

infixl 20 _⊕_
data Tms where
  ! : {Γ : Ctx} → Tms Γ ∅
  _⊕_  : {Γ Δ : Ctx} {A : Ty} → Tms Γ Δ → Tm Γ A → Tms Γ (Δ ⊹ A)

infixl 30 _[_]
data Tm where
  V : {Γ : Ctx} {A : Ty} → Var Γ A → Tm Γ A
  Lam : {Γ : Ctx} {A B : Ty} → Tm (Γ ⊹ A) B → Tm Γ (A ⇒ B)
  App : {Γ : Ctx} {A B : Ty} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  _[_] : {Γ Δ : Ctx} {A : Ty} → Tm Δ A → Tms Γ Δ → Tm Γ A
  W₁ : {Γ : Ctx} (A : Ty) {B : Ty} → Tm Γ B → Tm (Γ ⊹ A) B

  β : {Γ : Ctx} {A B : Ty} (t : Tm (Γ ⊹ A) B) (s : Tm Γ A) →
    App (Lam t) s ≡ t [ idTms Γ ⊕ s ]
  η : {Γ : Ctx} {A B : Ty} (t : Tm Γ (A ⇒ B)) →
    t ≡ Lam (App (t [ W₁Tms A (idTms Γ) ]) (V Zv))

  Zv[] : {Γ Δ : Ctx} {A : Ty} (σ : Tms Γ Δ) (t : Tm Γ A)
    → V Zv [ σ ⊕ t ] ≡ t
  Sv[] : {Γ Δ : Ctx} {A B : Ty} (v : Var Δ A) (σ : Tms Γ Δ) (t : Tm Γ B) →
    V (Sv v) [ σ ⊕ t ] ≡ V v [ σ ]
  Lam[] : {Γ Δ : Ctx} {A B : Ty} (t : Tm (Δ ⊹ A) B) (σ : Tms Γ Δ) →
    Lam t [ σ ] ≡ Lam (t [ W₂Tms A σ ])
  App[] : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ (A ⇒ B)) (s : Tm Δ A) (σ : Tms Γ Δ) →
    App t s [ σ ] ≡ App (t [ σ ]) (s [ σ ])

  -- These two assumptions are superfluous
  [][] : {Γ Δ Σ : Ctx} {A : Ty} (t : Tm Σ A) (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
    t [ σ ] [ τ ] ≡ t [ σ ∘Tms τ ]
  [id] : {Γ : Ctx} {A : Ty} (t : Tm Γ A) →
    t [ idTms Γ ] ≡ t

  W₁V : {Γ : Ctx} {A B : Ty} (v : Var Γ B) →
    W₁ A (V v) ≡ V (Sv v)
  W₁Lam : {Γ : Ctx} {A B C : Ty} (t : Tm (Γ ⊹ B) C) →
    W₁ A (Lam t) ≡ Lam (t [ W₂Tms B (W₁Tms A (idTms Γ)) ])
  W₁App : {Γ : Ctx} {A B C : Ty} (t : Tm Γ (B ⇒ C)) (s : Tm Γ B) →
    W₁ A (App t s) ≡ App (W₁ A t) (W₁ A s)

  isSetTm : {Γ : Ctx} {A : Ty} → isSet (Tm Γ A)

! ∘Tms τ = !
(σ ⊕ t) ∘Tms τ = (σ ∘Tms τ) ⊕ t [ τ ]

varify : {Γ Δ : Ctx} → Ren Γ Δ → Tms Γ Δ
varify !R = !
varify (σ ⊕R v) = varify σ ⊕ (V v)

idTms Γ = varify (idRen Γ)

W₁Tms A ! = !
W₁Tms A (σ ⊕ t) = W₁Tms A σ ⊕ W₁ A t

W₂Tms A σ = W₁Tms A σ ⊕ V Zv

Vlem1 : {Γ Δ : Ctx} {A : Ty} (σ : Ren Γ Δ) →
  varify (W₁Ren A σ) ≡ W₁Tms A (varify σ)
Vlem1 !R = refl
Vlem1 (σ ⊕R v) i = Vlem1 σ i ⊕ W₁V v (~ i)

Vlem2 : {Γ : Ctx} {A : Ty} → W₂Tms A (idTms Γ) ≡ idTms (Γ ⊹ A)
Vlem2 {∅} = refl
Vlem2 {Γ ⊹ B} {A} i = Vlem1 (W₁Ren B (idRen Γ)) (~ i) ⊕ W₁V Zv i ⊕ V Zv

∘Assoc : {Γ Δ Σ Ω : Ctx} (σ : Tms Σ Ω) (τ : Tms Δ Σ) (μ : Tms Γ Δ) →
  σ ∘Tms τ ∘Tms μ ≡ σ ∘Tms (τ ∘Tms μ)
∘Assoc ! τ μ = refl
∘Assoc (σ ⊕ t) τ μ i = ∘Assoc σ τ μ i ⊕ [][] t τ μ i

∘IdR : {Γ Δ : Ctx} (σ : Tms Γ Δ) →
  σ ∘Tms idTms Γ ≡ σ
∘IdR ! = refl
∘IdR (σ ⊕ t) i = ∘IdR σ i ⊕ [id] t i

∘IdL : {Γ Δ : Ctx} (σ : Tms Γ Δ) →
  idTms Δ ∘Tms σ ≡ σ
∘IdL ! = refl
∘IdL {Δ = Δ ⊹ A} (σ ⊕ t) =
  varify (W₁Ren A (idRen Δ)) ∘Tms (σ ⊕ t) ⊕ V Zv [ σ ⊕ t ]
    ≡⟨ (λ i → Vlem1 (idRen Δ) i ∘Tms (σ ⊕ t) ⊕ Zv[] σ t i) ⟩
  W₁Tms A (varify (idRen Δ)) ∘Tms (σ ⊕ t) ⊕ t
    ≡⟨ {!!} ⟩
  σ ⊕ t
    ∎

Wlem0 : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) (s : Tm Γ A) →
  W₁ A t [ σ ⊕ s ] ≡ t [ σ ]
Wlem0 t σ s = {!!}

-- encode-decode argument to show that Tms is a set
module TmsPath where
  Code : {Γ Δ : Ctx} → Tms Γ Δ → Tms Γ Δ → Set
  Code ! ! = ⊤
  Code (σ ⊕ t) (τ ⊕ s) = (t ≡ s) × Code σ τ

  reflCode : {Γ Δ : Ctx} (σ : Tms Γ Δ) → Code σ σ
  reflCode ! = tt
  reflCode (σ ⊕ t) = refl , reflCode σ

  encode : {Γ Δ : Ctx} (σ τ : Tms Γ Δ) → σ ≡ τ → Code σ τ
  encode σ τ = J (λ μ _ → Code σ μ) (reflCode σ)

  encodeRefl : {Γ Δ : Ctx} (σ : Tms Γ Δ) → encode σ σ refl ≡ reflCode σ
  encodeRefl σ = JRefl (λ τ _ → Code σ τ) (reflCode σ)

  decode : {Γ Δ : Ctx} (σ τ : Tms Γ Δ) → Code σ τ → σ ≡ τ
  decode ! ! x = refl
  decode (σ ⊕ t) (τ ⊕ s) (p , q) i = decode σ τ q i ⊕ p i

  decodeRefl : {Γ Δ : Ctx} (σ : Tms Γ Δ) → decode σ σ (reflCode σ) ≡ refl
  decodeRefl ! = refl
  decodeRefl (σ ⊕ t) = ap (ap (_⊕ t)) (decodeRefl σ)

  decodeEncode : {Γ Δ : Ctx} (σ τ : Tms Γ Δ) (p : σ ≡ τ) → decode σ τ (encode σ τ p) ≡ p
  decodeEncode σ τ =
    J (λ μ q → decode σ μ (encode σ μ q) ≡ q)
      (ap (decode σ σ) (encodeRefl σ) ∙ decodeRefl σ)

  isPropCode : {Γ Δ : Ctx} (σ τ : Tms Γ Δ) → isProp (Code σ τ)
  isPropCode ! ! = isPropUnit
  isPropCode (σ ⊕ t) (τ ⊕ s) = isPropΣ (isSetTm t s) (λ _ → isPropCode σ τ)

isSetTms : {Γ Δ : Ctx} → isSet (Tms Γ Δ)
isSetTms σ τ =
  isOfHLevelRetract 1
    (TmsPath.encode σ τ)
    (TmsPath.decode σ τ)
    (TmsPath.decodeEncode σ τ)
    (TmsPath.isPropCode σ τ)

module SampleSyn where

  ChurchType : Ty → Ty
  ChurchType A = (A ⇒ A) ⇒ A ⇒ A

  ChurchTwo : {Γ : Ctx} {A : Ty} → Tm Γ (ChurchType A)
  ChurchTwo = Lam (Lam (App (V (Sv Zv)) (App (V (Sv Zv)) (V Zv))))

  PlusType : Ty → Ty
  PlusType A = ChurchType A ⇒ ChurchType A ⇒ ChurchType A

  Plus : {Γ : Ctx} {A : Ty} → Tm Γ (PlusType A)
  Plus = Lam (Lam (Lam (Lam (App (App (V (Sv (Sv (Sv Zv)))) (V (Sv Zv)))
                                 (App (App (V (Sv (Sv Zv))) (V (Sv Zv))) (V Zv))))))

  TwoPlusTwo : {A : Ty} → Tm ∅ (ChurchType A)
  TwoPlusTwo = App (App Plus ChurchTwo) ChurchTwo
