{-# OPTIONS --cubical --allow-unsolved-metas #-}

module syn where

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

W₁Ren : {Γ Δ : Ctx} {A : Ty} → Ren Γ Δ → Ren (Γ ⊹ A) Δ
W₁Ren !R = !R
W₁Ren (σ ⊕R v) = W₁Ren σ ⊕R Sv v

W₂Ren : {Γ Δ : Ctx} {A : Ty} → Ren Γ Δ → Ren (Γ ⊹ A) (Δ ⊹ A)
W₂Ren σ = W₁Ren σ ⊕R Zv

idRen : {Γ : Ctx} → Ren Γ Γ
idRen {∅} = !R
idRen {Γ ⊹ A} = W₂Ren idRen

data Tm : Ctx → Ty → Set

infixl 20 _⊕_
{-# NO_POSITIVITY_CHECK #-}
data Tms : Ctx → Ctx → Set where
  ! : {Γ : Ctx} → Tms Γ ∅
  _⊕_  : {Γ Δ : Ctx} {A : Ty} → Tms Γ Δ → Tm Γ A → Tms Γ (Δ ⊹ A)

W₁Tm : {Γ : Ctx} {A B : Ty} → Tm Γ A → Tm (Γ ⊹ B) A

W₁Tms : {Γ Δ : Ctx} {A : Ty} → Tms Γ Δ → Tms (Γ ⊹ A) Δ
W₁Tms ! = !
W₁Tms (σ ⊕ t) = W₁Tms σ ⊕ W₁Tm t

{-# TERMINATING #-}
W₂Tms : {Γ Δ : Ctx} {A : Ty} → Tms Γ Δ → Tms (Γ ⊹ A) (Δ ⊹ A)

_∘Tms_ : {Γ Δ Σ : Ctx} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ

idTms : {Γ : Ctx} → Tms Γ Γ

infixl 30 _[_]
{-# NO_POSITIVITY_CHECK #-}
data Tm where
  V : {Γ : Ctx} {A : Ty} → Var Γ A → Tm Γ A
  Lam : {Γ : Ctx} {A B : Ty} → Tm (Γ ⊹ A) B → Tm Γ (A ⇒ B)
  App : {Γ : Ctx} {A B : Ty} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  _[_] : {Γ Δ : Ctx} {A : Ty} → Tm Δ A → Tms Γ Δ → Tm Γ A

  Zv[] : {Γ Δ : Ctx} {A : Ty} (σ : Tms Γ Δ) (t : Tm Γ A)
    → V Zv [ σ ⊕ t ] ≡ t
  Sv[] : {Γ Δ : Ctx} {A B : Ty} (v : Var Δ A) (σ : Tms Γ Δ) (t : Tm Γ B) →
    V (Sv v) [ σ ⊕ t ] ≡ V v [ σ ]
  Lam[] : {Γ Δ : Ctx} {A B : Ty} (σ : Tms Γ Δ) (t : Tm (Δ ⊹ A) B) →
    Lam t [ σ ] ≡ Lam (t [ W₂Tms σ ])
  App[] : {Γ Δ : Ctx} {A B : Ty} (σ : Tms Γ Δ) (t : Tm Δ (A ⇒ B)) (s : Tm Δ A) →
    App t s [ σ ] ≡ App (t [ σ ]) (s [ σ ])
  [][] : {Γ Δ Σ : Ctx} {A : Ty} (t : Tm Σ A) (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
    t [ σ ] [ τ ] ≡ t [ σ ∘Tms τ ]

  β : {Γ : Ctx} {A B : Ty} (t : Tm (Γ ⊹ A) B) (s : Tm Γ A) →
    App (Lam t) s ≡ t [ idTms ⊕ s ]
  η : {Γ : Ctx} {A B : Ty} (t : Tm Γ (A ⇒ B)) →
    t ≡ Lam (App (t [ W₁Tms idTms ]) (V Zv))

  isSetTm : {Γ : Ctx} {A : Ty} → isSet (Tm Γ A)

W₂Tms σ = W₁Tms σ ⊕ V Zv

! ∘Tms τ = !
(σ ⊕ t) ∘Tms τ = (σ ∘Tms τ) ⊕ t [ τ ]

varify : {Γ Δ : Ctx} → Ren Γ Δ → Tms Γ Δ
varify !R = !
varify (σ ⊕R v) = varify σ ⊕ (V v)

idTms = varify idRen

Vlem0 : {Γ Δ : Ctx} {A : Ty} → (σ : Ren Γ Δ) →
  varify (W₁Ren {A = A} σ) ≡ W₁Tms (varify σ)

Vlem1 : {Γ : Ctx} {A : Ty} → W₂Tms {Γ} {Γ} {A} idTms ≡ idTms
Vlem1 i = Vlem0 idRen (~ i) ⊕  V Zv

∘TmsAssoc : {Γ Δ Σ Ω : Ctx} (σ : Tms Σ Ω) (τ : Tms Δ Σ) (μ : Tms Γ Δ) →
  (σ ∘Tms τ) ∘Tms μ ≡ σ ∘Tms (τ ∘Tms μ)
∘TmsAssoc ! τ μ = refl
∘TmsAssoc (σ ⊕ t) τ μ i = ∘TmsAssoc σ τ μ i ⊕ [][] t τ μ i

Wlem0 : {Γ Δ : Ctx} {A B : Ty} (s : Tm Δ A) (σ : Tms Γ Δ) (t : Tm Γ B) →
  W₁Tm s [ σ ⊕ t ] ≡ s [ σ ]

Wlem1 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) (t : Tm Γ A) →
  W₁Tms σ ∘Tms (τ ⊕ t) ≡ σ ∘Tms τ
Wlem1 ! τ t = refl
Wlem1 (σ ⊕ s) τ t i = Wlem1 σ τ t i ⊕ Wlem0 s τ t i

Wlem2 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
  σ ∘Tms W₁Tms τ ≡ W₁Tms {A = A} (σ ∘Tms τ)
Wlem2 ! τ = refl
Wlem2 (σ ⊕ t) τ i = Wlem2 σ τ i ⊕ t [ W₁Tms τ ]

Wlem3 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
  W₁Tms {A = A} σ ∘Tms W₂Tms τ ≡ W₁Tms (σ ∘Tms τ)
Wlem3 σ τ =
  W₁Tms σ ∘Tms (W₁Tms τ ⊕ V Zv)
    ≡⟨ Wlem1 σ (W₁Tms τ) (V Zv) ⟩
  σ ∘Tms W₁Tms τ
    ≡⟨ Wlem2 σ τ ⟩
  W₁Tms (σ ∘Tms τ)
    ∎

Wlem4 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
  (W₂Tms {A = A} σ ∘Tms W₂Tms τ) ≡ W₂Tms (σ ∘Tms τ)
Wlem4 σ τ i = Wlem3 σ τ i ⊕ Zv[] (W₁Tms τ) (V Zv) i

[id] : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → t [ idTms ] ≡ t

∘TmsIdR : {Γ Δ : Ctx} (σ : Tms Γ Δ) → σ ∘Tms idTms ≡ σ
∘TmsIdR ! = refl
∘TmsIdR (σ ⊕ t) i = ∘TmsIdR σ i ⊕ [id] t i

∘TmsIdL : {Γ Δ : Ctx} (σ : Tms Γ Δ) → idTms ∘Tms σ ≡ σ
∘TmsIdL ! = refl
∘TmsIdL (σ ⊕ t) i =
  ((varify (W₁Ren idRen) ∘Tms (σ ⊕ t)) ⊕ V Zv [ σ ⊕ t ]
    ≡⟨ (λ k → (Vlem0 idRen k ∘Tms (σ ⊕ t)) ⊕ Zv[] σ t k) ⟩
  (W₁Tms idTms ∘Tms (σ ⊕ t)) ⊕ t
    ≡⟨ ap (_⊕ t) (Wlem1 idTms σ t) ⟩
  (idTms ∘Tms σ) ⊕ t
    ≡⟨ ap (_⊕ t) (∘TmsIdL σ) ⟩
  σ ⊕ t
    ∎) i

W₁Tm (V v) = V (Sv v)
W₁Tm (Lam t) = Lam (t [ varify (W₁Ren (W₁Ren idRen)) ⊕ V Zv ])
W₁Tm (App t s) = App (W₁Tm t) (W₁Tm s)
W₁Tm (t [ σ ]) = t [ W₁Tms σ ]

W₁Tm (Zv[] σ t i) = Zv[] (W₁Tms σ) (W₁Tm t) i
W₁Tm (Sv[] v σ t i) = Sv[] v (W₁Tms σ) (W₁Tm t) i
W₁Tm (Lam[] σ t i) =
  (Lam (t [ W₂Tms σ ] [ varify (W₁Ren (W₁Ren idRen)) ⊕ V Zv ])
    ≡⟨ ap Lam ([][] t (W₂Tms σ) (varify (W₁Ren (W₁Ren idRen)) ⊕ V Zv)) ⟩
  Lam (t [ (W₁Tms σ ∘Tms (varify (W₁Ren (W₁Ren idRen)) ⊕ V Zv))
    ⊕ V Zv [ varify (W₁Ren (W₁Ren idRen)) ⊕ V Zv ] ])
    ≡⟨ (λ j → Lam (t [ Wlem1 σ (Vlem0 (W₁Ren idRen) j ) (V Zv) j
      ⊕  (Zv[] (varify (W₁Ren (W₁Ren idRen))) (V Zv) j) ])) ⟩
  Lam (t [ (σ ∘Tms W₁Tms (varify (W₁Ren idRen))) ⊕ V Zv ])
    ≡⟨ (λ j → Lam (t [ Wlem2 σ (Vlem0 idRen j) j ⊕ V Zv ])) ⟩
  Lam (t [ W₁Tms (σ ∘Tms W₁Tms idTms) ⊕ V Zv ])
    ≡⟨ (λ j → Lam (t [ W₁Tms (Wlem2 σ idTms j) ⊕  V Zv ])) ⟩
  Lam (t [ W₁Tms (W₁Tms (σ ∘Tms idTms)) ⊕ V Zv ])
    ≡⟨ (λ j → Lam (t [ W₁Tms (W₁Tms (∘TmsIdR σ j)) ⊕ V Zv ])) ⟩
  Lam (t [ W₂Tms (W₁Tms σ) ])
    ≡⟨ Lam[] (W₁Tms σ) t ⁻¹ ⟩
  Lam t [ W₁Tms σ ]
    ∎) (~ i)
W₁Tm (App[] σ t s i) = App[] (W₁Tms σ) t s i
W₁Tm ([][] t σ τ i) =
  (t [ σ ] [ W₁Tms τ ]
    ≡⟨ [][] t σ (W₁Tms τ) ⟩
  t [ σ ∘Tms W₁Tms τ ]
    ≡⟨ ap (t [_]) (Wlem2 σ τ) ⟩
  t [ W₁Tms (σ ∘Tms τ) ]
    ∎) i
W₁Tm (β t s i) =
  (App (Lam (t [ varify (W₁Ren (W₁Ren idRen)) ⊕ V Zv ])) (W₁Tm s)
    ≡⟨ (λ k → β (t [ Vlem0 (W₁Ren idRen) k ⊕ V Zv ]) (W₁Tm s) k) ⟩
  t [ W₁Tms (varify (W₁Ren idRen)) ⊕ V Zv ] [ idTms ⊕ W₁Tm s ]
    ≡⟨ (λ k → [][] t (W₁Tms (Vlem0 idRen k)  ⊕ V Zv) (idTms ⊕ W₁Tm s) k) ⟩
  t [(W₁Tms (W₁Tms idTms) ∘Tms (idTms ⊕ W₁Tm s)) ⊕ V Zv [ idTms ⊕ W₁Tm s ] ]
    ≡⟨ (λ k → t [ Wlem1 (W₁Tms (varify idRen)) idTms (W₁Tm s) k ⊕ Zv[] idTms (W₁Tm s) k ]) ⟩
  t [ (W₁Tms idTms ∘Tms (varify (W₁Ren idRen) ⊕ V Zv)) ⊕ W₁Tm s ]
    ≡⟨ (λ k → t [ Wlem1 idTms (Vlem0 idRen k) (V Zv) k ⊕ W₁Tm s ]) ⟩
  t [ (idTms ∘Tms W₁Tms idTms) ⊕ W₁Tm s ]
    ≡⟨ (λ k → t [ ∘TmsIdL (W₁Tms idTms) k ⊕ W₁Tm s ]) ⟩
  t [ W₁Tms idTms ⊕ W₁Tm s ]
    ∎) i
W₁Tm (η t i) =
  (Lam (App (t [ W₁Tms idTms ]) (V Zv) [ varify (W₁Ren (W₁Ren idRen)) ⊕ V Zv ])
    ≡⟨ ap Lam (App[] (varify (W₁Ren (W₁Ren idRen)) ⊕ V Zv) (t [ W₁Tms idTms ]) (V Zv)) ⟩
  Lam (App (t [ W₁Tms (varify idRen) ] [ varify (W₁Ren (W₁Ren idRen)) ⊕ V Zv ])
    (V Zv [ varify (W₁Ren (W₁Ren idRen)) ⊕ V Zv ]))
    ≡⟨ (λ k → Lam (App ([][] t (W₁Tms idTms) (Vlem0 (W₁Ren idRen) k ⊕ V Zv) k)
      (Zv[] (varify (W₁Ren (W₁Ren idRen))) (V Zv) k))) ⟩
   Lam (App (t [ W₁Tms idTms ∘Tms (W₁Tms (varify (W₁Ren idRen)) ⊕ V Zv) ]) (V Zv))
     ≡⟨ (λ k → Lam (App (t [ Wlem1 (varify idRen) (W₁Tms (varify (W₁Ren idRen))) (V Zv) k ]) (V Zv))) ⟩
   Lam (App (t [ idTms ∘Tms W₁Tms (varify (W₁Ren idRen)) ]) (V Zv))
     ≡⟨ (λ k → Lam (App (t [ ∘TmsIdL (W₁Tms (varify (W₁Ren idRen))) k ]) (V Zv))) ⟩
   Lam (App (t [ W₁Tms (varify (W₁Ren idRen)) ]) (V Zv))
     ≡⟨ (λ k → Lam (App (Wlem0 t (W₁Tms (varify (W₁Ren idRen))) (V (Sv Zv)) (~ k))  (V Zv))) ⟩
   Lam (App (W₁Tm t [ W₁Tms (varify (W₁Ren idRen)) ⊕ V (Sv Zv) ]) (V Zv))
     ≡⟨ η (W₁Tm t) ⁻¹ ⟩
   W₁Tm t
    ∎) (~ i)
W₁Tm (isSetTm t s p q i j) =
  isSet→SquareP (λ i j → isSetTm)
    (λ k → W₁Tm (p k))
    (λ k → W₁Tm (q k))
    (λ k → W₁Tm t)
    (λ k → W₁Tm s) i j

Vlem0 !R = refl
Vlem0 {A = A} (σ ⊕R v) = ap (_⊕ V (Sv v)) (Vlem0 {A = A} σ)

[id]Var : {Γ : Ctx} {A : Ty} (v : Var Γ A) → V v [ idTms ] ≡ V v
[id]Var Zv = Zv[] (varify (W₁Ren idRen)) (V Zv)
[id]Var (Sv v) =
  V (Sv v) [ idTms ]
    ≡⟨ Sv[] v (varify (W₁Ren idRen)) (V Zv) ⟩
  V v [ varify (W₁Ren idRen) ]
    ≡⟨ ap (V v [_]) (Vlem0 idRen) ⟩
  W₁Tm (V v [ idTms ])
    ≡⟨ ap W₁Tm ([id]Var v) ⟩
  V (Sv v)
    ∎

[id] (V v) = [id]Var v
[id] (Lam t) =
  Lam t [ idTms ]
    ≡⟨ Lam[] idTms t ⟩
  Lam (t [ W₂Tms idTms ])
    ≡⟨ (λ k → Lam (t [ Vlem1 k ])) ⟩
  Lam (t [ idTms ])
    ≡⟨ ap Lam ([id] t) ⟩
  Lam t
    ∎
[id] (App t s) =
  App t s [ idTms ]
    ≡⟨ App[] idTms t s ⟩
  App (t [ idTms ]) (s [ idTms ])
    ≡⟨ (λ k → App ([id] t k) ([id] s k)) ⟩
  App t s
    ∎
[id] (t [ σ ]) =
  t [ σ ] [ idTms ]
    ≡⟨ [][] t σ idTms ⟩
  t [ σ ∘Tms idTms ]
    ≡⟨ ap (t [_]) (∘TmsIdR σ) ⟩
  t [ σ ]
    ∎

[id] (Zv[] σ t i) j =
  isSet→SquareP (λ i j → isSetTm)
    ([id] (V Zv [ σ ⊕ t ]))
    ([id] t)
    (λ k → Zv[] σ t k [ idTms ])
    (Zv[] σ t) i j
[id] (Sv[] v σ t i) j =
  isSet→SquareP (λ i j → isSetTm)
    ([id] (V (Sv v) [ σ ⊕ t ]))
    ([id] (V v [ σ ]))
    (λ k → Sv[] v σ t k [ idTms ])
    (Sv[] v σ t) i j
[id] (Lam[] σ t i) j =
  isSet→SquareP (λ i j → isSetTm)
    ([id] (Lam t [ σ ]))
    ([id] (Lam (t [ W₂Tms σ ])))
    (λ k → Lam[] σ t k [ idTms ])
    (Lam[] σ t) i j
[id] (App[] σ t s i) j =
  isSet→SquareP (λ i j → isSetTm)
    ([id] (App t s [ σ ]))
    ([id] (App (t [ σ ]) (s [ σ ])))
    (λ k → App[] σ t s k [ idTms ])
    (App[] σ t s) i j
[id] ([][] t σ τ i) j =
  isSet→SquareP (λ i j → isSetTm)
    ([id] (t [ σ ] [ τ ]))
    ([id] (t [ σ ∘Tms τ ]))
    (λ k → [][] t σ τ k [ idTms ])
    ([][] t σ τ) i j
[id] (β t s i) j = {!!}
[id] (η t i) j = {!!}
[id] (isSetTm t s p q i j) =
  isSet→SquareP
    (λ i j →
      isSet→isGroupoid isSetTm
        (isSetTm t s p q i j [ idTms ])
        (isSetTm t s p q i j))
    (λ k → [id] (p k))
    (λ k → [id] (q k))
    (λ k → [id] t)
    (λ k → [id] s) i j

private
  Wlem1Varify : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Tms Γ Δ) (t : Tm Γ A) →
    W₁Tms (varify σ) ∘Tms (τ ⊕ t) ≡ (varify σ) ∘Tms τ
  Wlem1Varify !R τ t = refl
  Wlem1Varify (σ ⊕R v) τ t i = Wlem1Varify σ τ t i ⊕ Sv[] v τ t i

Wlem0 (V v) σ t = Sv[] v σ t
Wlem0 (Lam s) σ t =
  Lam (s [ varify (W₁Ren (W₁Ren idRen)) ⊕ V Zv ]) [ σ ⊕ t ]
    ≡⟨ (λ k → Lam (s [ Vlem0 (W₁Ren idRen) k ⊕ V Zv ]) [ σ ⊕ t ]) ⟩
  Lam (s [ W₂Tms (varify (W₁Ren idRen)) ]) [ σ ⊕ t ]
    ≡⟨ ap (_[ σ ⊕ t ]) (Lam[] (varify (W₁Ren idRen)) s ⁻¹) ⟩
  Lam s [ varify (W₁Ren idRen) ] [ σ ⊕ t ]
    ≡⟨ (λ k → [][] (Lam s) (Vlem0 idRen k) (σ ⊕ t) k) ⟩
  Lam s [ W₁Tms (varify idRen) ∘Tms (σ ⊕ t) ]
    ≡⟨ ap (Lam s [_]) (Wlem1Varify idRen σ t) ⟩
  Lam s [ varify idRen ∘Tms σ ]
    ≡⟨ ap (Lam s [_]) (∘TmsIdL σ) ⟩
  Lam s [ σ ]
    ∎
Wlem0 (App s₁ s₂) σ t =
  App (W₁Tm s₁) (W₁Tm s₂) [ σ ⊕ t ]
    ≡⟨ App[] (σ ⊕ t) (W₁Tm s₁) (W₁Tm s₂) ⟩
  App (W₁Tm s₁ [ σ ⊕ t ]) (W₁Tm s₂ [ σ ⊕ t ])
    ≡⟨ (λ k → App (Wlem0 s₁ σ t k) (Wlem0 s₂ σ t k)) ⟩
   App (s₁ [ σ ]) (s₂ [ σ ])
     ≡⟨ App[] σ s₁ s₂ ⁻¹ ⟩
   App s₁ s₂ [ σ ]
    ∎ 
Wlem0 (s [ τ ]) σ t =
  s [ W₁Tms τ ] [ σ ⊕ t ]
    ≡⟨ [][] s (W₁Tms τ) ( σ ⊕ t) ⟩
  s [ W₁Tms τ ∘Tms (σ ⊕ t) ]
    ≡⟨ ap (s [_]) (Wlem1 τ σ t) ⟩
  s [ τ ∘Tms σ ]
    ≡⟨ [][] s τ σ ⁻¹ ⟩
  s [ τ ] [ σ ]
    ∎

Wlem0 (Zv[] τ s i) σ t = {!!}
Wlem0 (Sv[] v τ s i) σ t = {!!}
Wlem0 (Lam[] τ s i) σ t = {!!}
Wlem0 (App[] τ s s₁ i) σ t = {!!}
Wlem0 ([][] s τ μ i) σ t = {!!}
Wlem0 (β s₁ s₂ i) σ t = {!!}
Wlem0 (η s i) σ t = {!!}
Wlem0 (isSetTm s₁ s₂ p q i j) σ t =
  isSet→SquareP
    (λ i j →
      isSet→isGroupoid isSetTm
        (W₁Tm (isSetTm s₁ s₂ p q i j) [ σ ⊕ t ] )
        (isSetTm s₁ s₂ p q i j [ σ ]))
    (λ k → Wlem0 (p k) σ t)
    (λ k → Wlem0 (q k) σ t)
    (λ k → Wlem0 s₁ σ t)
    (λ k → Wlem0 s₂ σ t) i j

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
      (encode σ τ)
      (decode σ τ)
      (decodeEncode σ τ)
      (isPropCode σ τ)

module _ where
  open Precategory renaming (id to 𝒾𝒹)
  open Functor

  SYN : Precategory lzero lzero
  SYN .ob = Ctx
  SYN .Hom[_,_] Γ Δ = Tms Γ Δ
  SYN .𝒾𝒹 Γ = idTms
  SYN ._⋆_ σ τ = τ ∘Tms σ
  SYN .⋆IdL = ∘TmsIdR
  SYN .⋆IdR = ∘TmsIdL
  SYN .⋆Assoc σ τ μ = ∘TmsAssoc μ τ σ ⁻¹

  instance
    isCatSYN : isCategory SYN
    isCatSYN .isSetHom = TmsPath.isSetTms

  TMS-SYN : Ctx → ob (PSh SYN)
  TMS-SYN Γ .F-ob Δ = Tms Δ Γ , TmsPath.isSetTms
  TMS-SYN Γ .F-hom σ τ = τ ∘Tms σ
  TMS-SYN Γ .F-id i σ = ∘TmsIdR σ i
  TMS-SYN Γ .F-seq σ τ i μ = ∘TmsAssoc μ σ τ (~ i)

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
