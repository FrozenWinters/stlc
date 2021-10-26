{-# OPTIONS --cubical #-}

module syn3 where

open import ren2

open import Cubical.Data.Unit as ⊤ renaming (Unit to ⊤)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category

data Tm : Ctx → Ty → Set
Tms = IL Tm

infixl 20 _∘Tms_
_∘Tms_ : {Γ Δ Σ : Ctx} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
idTms : (Γ : Ctx) → Tms Γ Γ
W₁Tms : {Γ Δ : Ctx} (A : Ty) → Tms Γ Δ → Tms (Γ ⊹ A) Δ
W₂Tms : {Γ Δ : Ctx} (A : Ty) → Tms Γ Δ → Tms (Γ ⊹ A) (Δ ⊹ A)

infixl 30 _[_]
data Tm where
  V : {Γ : Ctx} {A : Ty} → Var Γ A → Tm Γ A
  Lam : {Γ : Ctx} {A B : Ty} → Tm (Γ ⊹ A) B → Tm Γ (A ⇒ B)
  App : {Γ : Ctx} {A B : Ty} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  _[_] : {Γ Δ : Ctx} {A : Ty} → Tm Δ A → Tms Γ Δ → Tm Γ A

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

  -- This assumptions is superfluous
  [][] : {Γ Δ Σ : Ctx} {A : Ty} (t : Tm Σ A) (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
    t [ σ ] [ τ ] ≡ t [ σ ∘Tms τ ]

  trunc : {Γ : Ctx} {A : Ty} → isSet (Tm Γ A)

σ ∘Tms τ = mapIL _[ τ ] σ

varify : {Γ Δ : Ctx} → Ren Γ Δ → Tms Γ Δ
varify σ = mapIL V σ

idTms Γ = varify (idRen Γ)

W₁Tm : {Γ : Ctx} (A : Ty) {B : Ty} → Tm Γ B → Tm (Γ ⊹ A) B
W₁Tm {Γ} A t = t [ varify (W₁Ren A (idRen Γ)) ]

W₁Tms {Γ} A σ = σ ∘Tms varify (W₁Ren A (idRen Γ))

W₂Tms A σ = W₁Tms A σ ⊕ V Zv

∘TmsAssoc : {Γ Δ Σ Ω : Ctx} (σ : Tms Σ Ω) (τ : Tms Δ Σ) (μ : Tms Γ Δ) →
  σ ∘Tms τ ∘Tms μ ≡ σ ∘Tms (τ ∘Tms μ)
∘TmsAssoc ! τ μ = refl
∘TmsAssoc (σ ⊕ t) τ μ i = ∘TmsAssoc σ τ μ i ⊕ [][] t τ μ i

-- Lemmas on how varify acts

Vlem0 : {Γ Δ : Ctx} {A : Ty} (v : Var Δ A) (σ : Ren Γ Δ) →
  V (v [ σ ]R) ≡ (V v) [ varify σ ]
Vlem0 Zv (σ ⊕ w) = Zv[] (varify σ) (V w) ⁻¹
Vlem0 (Sv v) (σ ⊕ w) =
  V (v [ σ ]R)
    ≡⟨ Vlem0 v σ ⟩
  V v [ varify σ ]
    ≡⟨ Sv[] v (varify σ) (V w) ⁻¹ ⟩
  V (Sv v) [ varify σ ⊕ V w ]
    ∎

W₁V : {Γ : Ctx} {A B : Ty} (v : Var Γ B) →
  W₁Tm A (V v) ≡ V (Sv v)
W₁V {Γ} {A} v =
  V v [ varify (W₁Ren A (idRen Γ)) ]
    ≡⟨ Vlem0 v (W₁Ren A (idRen Γ)) ⁻¹ ⟩
  V (v [ W₁Ren A (idRen Γ) ]R)
    ≡⟨ ap V (Wlem2Ren v (idRen Γ)) ⟩
  V (Sv (v [ idRen Γ ]R))
    ≡⟨ ap V (ap Sv ([id]Ren v)) ⟩
  V (Sv v)
    ∎

Vlem1 : {Γ Δ Σ : Ctx} (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  varify (σ ∘Ren τ) ≡ varify σ ∘Tms varify τ
Vlem1 ! τ = refl
Vlem1 (σ ⊕ t) τ i = Vlem1 σ τ i ⊕ Vlem0 t τ i 

Vlem2 : {Γ Δ : Ctx} {A : Ty} (σ : Ren Γ Δ) →
  varify (W₁Ren A σ) ≡ W₁Tms A (varify σ)
Vlem2 ! = refl
Vlem2 (σ ⊕ v) i = Vlem2 σ i ⊕ W₁V v (~ i)

Vlem3 : {Γ : Ctx} {A : Ty} → W₂Tms A (idTms Γ) ≡ idTms (Γ ⊹ A)
Vlem3 {∅} = refl
Vlem3 {Γ ⊹ B} {A} i = Vlem2 (W₁Ren B (idRen Γ)) (~ i) ⊕ W₁V Zv i ⊕ V Zv

W₁Lam : {Γ : Ctx} {A B C : Ty} (t : Tm (Γ ⊹ B) C) →
  W₁Tm A (Lam t) ≡ Lam (t [ W₂Tms B (W₁Tms A (idTms Γ)) ])
W₁Lam {Γ} {A} {B} t =
  Lam t [ varify (W₁Ren A (idRen Γ)) ]
    ≡⟨ Lam[] t (varify (W₁Ren A (idRen Γ))) ⟩
  Lam (t [ W₂Tms B (varify (W₁Ren A (idRen Γ))) ])
    ≡⟨ (λ i → Lam (t [ W₂Tms B (Vlem2 (idRen Γ) i) ])) ⟩
  Lam (t [ W₂Tms B (W₁Tms A (idTms Γ)) ])
    ∎

W₁App : {Γ : Ctx} {A B C : Ty} (t : Tm Γ (B ⇒ C)) (s : Tm Γ B) →
  W₁Tm A (App t s) ≡ App (W₁Tm A t) (W₁Tm A s)
W₁App {Γ} {A} t s =
  App[] t s (varify (W₁Ren A (idRen Γ)))

W₁[] : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) →
  W₁Tm A (t [ σ ]) ≡ t [ W₁Tms A σ ]
W₁[] {Γ} {Δ} {A} t σ = [][] t σ (varify (W₁Ren A (idRen Γ)))

private
  Wlem1Varify : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Tms Γ Δ) (t : Tm Γ A) →
    varify (W₁Ren A σ) ∘Tms (τ ⊕ t) ≡ (varify σ) ∘Tms τ
  Wlem1Varify ! τ t = refl
  Wlem1Varify {A = A} (σ ⊕ v) τ t i = Wlem1Varify σ τ t i ⊕ Sv[] v τ t i

∘TmsIdL : {Γ Δ : Ctx} (σ : Tms Γ Δ) → idTms Δ ∘Tms σ ≡ σ
∘TmsIdL ! = refl
∘TmsIdL {Γ} {Δ ⊹ B} (σ ⊕ t) =
  varify (W₁Ren B (idRen Δ)) ∘Tms (σ ⊕ t) ⊕ V Zv [ σ ⊕ t ]
    ≡⟨ (λ i →  Wlem1Varify (idRen Δ) σ t i ⊕ Zv[] σ t i) ⟩
  idTms Δ ∘Tms σ ⊕ t
    ≡⟨ ap (_⊕ t) (∘TmsIdL σ) ⟩
  σ ⊕ t
    ∎

{-# TERMINATING #-}
[id] : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → t [ idTms Γ ] ≡ t

∘TmsIdR : {Γ Δ : Ctx} (σ : Tms Γ Δ) → σ ∘Tms (idTms Γ) ≡ σ
∘TmsIdR ! = refl
∘TmsIdR (σ ⊕ t) i = ∘TmsIdR σ i ⊕ [id] t i

[id]Var : {Γ : Ctx} {A : Ty} (v : Var Γ A) → V v [ idTms Γ ] ≡ V v
[id]Var {Γ ⊹ B} {A} Zv = Zv[] (varify (W₁Ren A (idRen Γ))) (V Zv)
[id]Var {Γ ⊹ B} {A} (Sv v) =
  V (Sv v) [ varify (W₁Ren B (idRen Γ)) ⊕ V Zv ]
    ≡⟨ Sv[] v (varify (W₁Ren B (idRen Γ))) (V Zv) ⟩
  V v [ varify (W₁Ren B (idRen Γ)) ]
    ≡⟨ ap (V v [_]) (Vlem2 (idRen Γ)) ⟩
  V v [ W₁Tms B (varify (idRen Γ)) ]
    ≡⟨ W₁[] (V v) (varify (idRen Γ)) ⁻¹ ⟩
  W₁Tm B (V v [ idTms Γ ])
    ≡⟨ ap (W₁Tm B) ([id]Var v) ⟩
  W₁Tm B (V v)
    ≡⟨ W₁V v ⟩
  V (Sv v)
    ∎

[id] (V v) = [id]Var v
[id] (Lam {Γ} {A} {B} t) =
  Lam t [ idTms Γ ]
    ≡⟨ Lam[] t (idTms Γ) ⟩
  Lam (t [ W₂Tms A (idTms Γ) ])
    ≡⟨ ap Lam (ap (t [_]) Vlem3) ⟩
  Lam (t [ idTms (Γ ⊹ A) ])
    ≡⟨ ap Lam ([id] t) ⟩
  Lam t
    ∎
[id] {Γ} (App t s) =
  App t s [ idTms Γ ]
    ≡⟨ App[] t s (idTms Γ) ⟩
  App (t [ idTms Γ ]) (s [ idTms Γ ])
    ≡⟨ (λ i → App ([id] t i) ([id] s i)) ⟩
  App t s
    ∎
[id] {Γ} (t [ σ ]) =
  t [ σ ] [ idTms Γ ]
    ≡⟨ [][] t σ (idTms Γ) ⟩
  t [ σ ∘Tms idTms Γ ]
    ≡⟨ ap (t [_]) (∘TmsIdR σ) ⟩
  t [ σ ]
    ∎

[id] {Γ} (β t s i) j =
  isSet→SquareP (λ i j → trunc)
    ([id] (App (Lam t) s))
    ([id] (t [ idTms Γ ⊕ s ]))
    (λ k →  β t s k [ idTms Γ ])
    (β t s) i j
[id] {Γ} {A ⇒ B} (η t i) j =
  isSet→SquareP (λ i j → trunc)
    ([id] t)
    ([id] (Lam (App (t [ W₁Tms A (idTms Γ) ]) (V Zv))))
    (λ k → η t k [ idTms Γ ])
    (η t) i j
[id] {Γ} (Zv[] σ t i) j =
  isSet→SquareP (λ i j → trunc)
    ([id] (V Zv [ σ ⊕ t ]))
    ([id] t)
    (λ k → Zv[] σ t k [ idTms Γ ])
    (Zv[] σ t) i j
[id] {Γ} (Sv[] v σ t i) j =
  isSet→SquareP (λ i j → trunc)
    ([id] (V (Sv v) [ σ ⊕ t ]))
    ([id] (V v [ σ ]))
    (λ k → Sv[] v σ t k [ idTms Γ ])
    (Sv[] v σ t) i j
[id] {Γ} {A ⇒ B} (Lam[] t σ i) j =
  isSet→SquareP (λ i j → trunc)
    ([id] (Lam t [ σ ]))
    ([id] (Lam (t [ W₂Tms A σ ])))
    (λ k →  Lam[] t σ k [ idTms Γ ])
    (Lam[] t σ) i j
[id] {Γ} (App[] t s σ i) j =
  isSet→SquareP (λ i j → trunc)
    ([id] (App t s [ σ ]))
    ([id] (App (t [ σ ]) (s [ σ ])))
    (λ k → App[] t s σ k [ idTms Γ ])
    (App[] t s σ) i j
[id] {Γ} ([][] t σ τ i) j =
  isSet→SquareP (λ i j → trunc)
    ([id] (t [ σ ] [ τ ]))
    ([id] (t [ σ ∘Tms τ ]))
    (λ k → [][] t σ τ k [ idTms Γ ])
    ([][] t σ τ) i j
[id] {Γ} (trunc t s p q i j) =
  isSet→SquareP
    (λ i j →
      isSet→isGroupoid trunc
        (trunc t s p q i j [ idTms Γ ])
        (trunc t s p q i j))
    (λ k → [id] (p k))
    (λ k → [id] (q k))
    (λ k → [id] t)
    (λ k → [id] s) i j

{-# TERMINATING #-}
Wlem0 : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) (s : Tm Γ A) →
  W₁Tm A t [ σ ⊕ s ] ≡ t [ σ ]

Wlem1 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) (t : Tm Γ A) →
  W₁Tms A σ ∘Tms (τ ⊕ t) ≡ σ ∘Tms τ
Wlem1 ! τ t = refl
Wlem1 (σ ⊕ s) τ t i = Wlem1 σ τ t i ⊕ Wlem0 s τ t i

Wlem0 {A = A} (V v) σ s =
  W₁Tm A (V v) [ σ ⊕ s ]
    ≡⟨ ap _[ σ ⊕ s ] (W₁V v) ⟩
  V (Sv v) [ σ ⊕ s ]
    ≡⟨ Sv[] v σ s ⟩
  V v [ σ ]
    ∎
Wlem0 {A = A} (Lam {Δ} {B} {C} t) σ s =
  W₁Tm A (Lam t) [ σ ⊕ s ]
    ≡⟨ ap _[ σ ⊕ s ] (W₁Lam t) ⟩
  Lam (t [ W₂Tms B (W₁Tms A (idTms Δ)) ]) [ σ ⊕ s ]
    ≡⟨ (λ i → Lam[] (t [ W₂Tms B (Vlem2 (idRen Δ) (~ i)) ]) (σ ⊕ s) i) ⟩
  Lam (t [ W₁Tms B (varify (W₁Ren A (idRen Δ))) ⊕ V Zv ] [ W₂Tms B (σ ⊕ s) ])
    ≡⟨ (λ i → Lam ([][] t (Vlem2 (W₁Ren A (idRen Δ)) (~ i) ⊕ V Zv) (W₂Tms B (σ ⊕ s)) i)) ⟩
  Lam (t [ varify (W₁Ren B (W₁Ren A (idRen Δ))) ∘Tms (W₁Tms B (σ ⊕ s) ⊕ V Zv)
    ⊕ V Zv [ W₁Tms B (σ ⊕ s) ⊕ V Zv ] ])
    ≡⟨ (λ i → Lam (t [ Wlem1Varify (W₁Ren A (idRen Δ)) (W₁Tms B (σ ⊕ s)) (V Zv) i
      ⊕ Zv[] (W₁Tms B (σ ⊕ s)) (V Zv) i ])) ⟩
  Lam (t [ varify (W₁Ren A (idRen Δ)) ∘Tms (W₁Tms B σ ⊕ W₁Tm B s) ⊕ V Zv ])
    ≡⟨ (λ i → Lam (t [ Wlem1Varify (idRen Δ) (W₁Tms B σ) (W₁Tm B s) i ⊕ V Zv ])) ⟩
  Lam (t [ idTms Δ ∘Tms W₁Tms B σ ⊕ V Zv ])
    ≡⟨ (λ i → Lam (t [ ∘TmsIdL (W₁Tms B σ) i ⊕ V Zv ])) ⟩
  Lam (t [ W₂Tms B σ ])
    ≡⟨ Lam[] t σ ⁻¹ ⟩
  Lam t [ σ ]
    ∎
Wlem0 {A = A} (App t₁ t₂) σ s =
  W₁Tm A (App t₁ t₂) [ σ ⊕ s ]
    ≡⟨ ap _[ σ ⊕ s ] (W₁App t₁ t₂) ⟩
  App (W₁Tm A t₁) (W₁Tm A t₂) [ σ ⊕ s ]
    ≡⟨ App[] (W₁Tm A t₁) (W₁Tm A t₂) (σ ⊕ s) ⟩
  App (W₁Tm A t₁ [ σ ⊕ s ]) (W₁Tm A t₂ [ σ ⊕ s ])
    ≡⟨ (λ k → App (Wlem0 t₁ σ s k) (Wlem0 t₂ σ s k)) ⟩
   App (t₁ [ σ ]) (t₂ [ σ ])
     ≡⟨ App[] t₁ t₂ σ ⁻¹ ⟩
   App t₁ t₂ [ σ ]
    ∎
Wlem0 {A = A} (t [ τ ]) σ s =
  W₁Tm A (t [ τ ]) [ σ ⊕ s ]
    ≡⟨ ap _[ σ ⊕ s ] (W₁[] t τ) ⟩
  t [ W₁Tms A τ ] [ σ ⊕ s ]
    ≡⟨ [][] t (W₁Tms A τ) (σ ⊕ s) ⟩
  t [ W₁Tms A τ ∘Tms (σ ⊕ s) ]
    ≡⟨ ap (t [_]) (Wlem1 τ σ s) ⟩
  t [ τ ∘Tms σ ]
    ≡⟨ [][] t τ σ ⁻¹ ⟩
  t [ τ ] [ σ ]
    ∎

Wlem0 {Γ} {Δ} {A} (β t₁ t₂ i) σ s j =
  isSet→SquareP (λ i j → trunc)
    (Wlem0 (App (Lam t₁)  t₂) σ s)
    (Wlem0 (t₁ [ idTms Δ ⊕ t₂ ]) σ s)
    (λ k → W₁Tm A (β t₁ t₂ k) [ σ ⊕ s ])
    (λ k → β t₁ t₂ k [ σ ]) i j
Wlem0 {A = A} (η {Δ} {C} t i) σ s j =
  isSet→SquareP (λ i j → trunc)
    (Wlem0 t σ s)
    (Wlem0 (Lam (App (t [ W₁Tms C (idTms Δ) ]) (V Zv))) σ s)
    (λ k → W₁Tm A (η t k) [ σ ⊕ s ])
    (λ k → η t k [ σ ]) i j
Wlem0 {Γ} {Δ} {A = A} (Zv[] τ t i) σ s j =
  isSet→SquareP (λ i j → trunc)
    (Wlem0 (V Zv [ τ ⊕ t ]) σ s)
    (Wlem0 t σ s)
    (λ k → W₁Tm A (Zv[] τ t k) [ σ ⊕ s ])
    (λ k → Zv[] τ t k [ σ ]) i j
Wlem0 {A = A} (Sv[] v τ t i) σ s j =
  isSet→SquareP (λ i j → trunc)
    (Wlem0 (V (Sv v) [ τ ⊕ t ]) σ s)
    (Wlem0 (V v [ τ ]) σ s)
    (λ k → W₁Tm A (Sv[] v τ t k) [ σ ⊕ s ])
    (λ k → Sv[] v τ t k [ σ ]) i j
Wlem0 {A = A} (Lam[] {Δ} {C} {D} t τ i) σ s j =
  isSet→SquareP (λ i j → trunc)
    (Wlem0 (Lam t [ τ ]) σ s)
    (Wlem0 (Lam (t [ W₂Tms D τ ])) σ s)
    (λ k → W₁Tm A (Lam[] t τ k) [ σ ⊕ s ])
    (λ k → Lam[] t τ k [ σ ]) i j
Wlem0 {A = A} (App[] t₁ t₂ τ i) σ s j =
  isSet→SquareP (λ i j → trunc)
    (Wlem0 (App t₁ t₂ [ τ ]) σ s)
    (Wlem0 (App (t₁ [ τ ]) (t₂ [ τ ])) σ s)
    (λ k → W₁Tm A (App[] t₁ t₂ τ k) [ σ ⊕ s ])
    (λ k → App[] t₁ t₂ τ k [ σ ]) i j
Wlem0 {A = A} ([][] t τ μ i) σ s j =
  isSet→SquareP (λ i j → trunc)
    (Wlem0 (t [ τ ] [ μ ]) σ s)
    (Wlem0 (t [ τ ∘Tms μ ]) σ s)
    (λ k → W₁Tm A ([][] t τ μ k) [ σ ⊕ s ])
    (λ k → [][] t τ μ k [ σ ]) i j
Wlem0 {A = A} (trunc t₁ t₂ p q i j) σ s =
  isSet→SquareP
    (λ i j →
      isSet→isGroupoid trunc
        (W₁Tm A (trunc t₁ t₂ p q i j) [ σ ⊕ s ])
        (trunc t₁ t₂ p q i j [ σ ]))
    (λ k → Wlem0 (p k) σ s)
    (λ k → Wlem0 (q k) σ s)
    (λ k → Wlem0 t₁ σ s)
    (λ k → Wlem0 t₂ σ s) i j
{-
_⇒Tms_ : (A : Ty) (Γ : Ctx) → Ctx
A ⇒Tms ∅ = ∅
A ⇒Tms (Γ ⊹ B) = (A ⇒Tms Γ) ⊹ (A ⇒ B)

LamTms : {Γ Δ : Ctx} {A : Ty} → Tms (Γ ⊹ A) Δ → Tms Γ (A ⇒Tms Δ)
LamTms ! = !
LamTms (σ ⊕ t) = LamTms σ ⊕ Lam t

eval : {A : Ty} {Γ : Ctx} → Tms ((A ⇒Tms Γ) ⊹ A) Γ
eval {Γ = ∅} = !
eval {A} {Γ ⊹ B} = {!!} ⊕ (App (V (Sv Zv)) (V Zv))
--W₁Tms A (W₁Tms (A ⇒ B) {!!})

LamNat₂ : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ B) (σ : Tms (Γ ⊹ A) Δ) →
  Lam (t [ σ ]) ≡ Lam {!!} [ LamTms σ ]
-}

module _ where
  open Contextual

  σιν : Contextual lzero lzero
  ty σιν = Ty
  tm σιν = Tm
  _⟦_⟧ σιν = _[_]
  𝒾𝒹 σιν = idTms
  𝒾𝒹L σιν = ∘TmsIdL
  𝒾𝒹⟦⟧ σιν = [id]
  ⟦⟧⟦⟧ σιν = [][]
  isSetTm σιν = trunc

  SYN : Precategory lzero lzero
  SYN = ambCat σιν
