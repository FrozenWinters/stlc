{-# OPTIONS --cubical #-}

module syn where

open import contextual
open import ccc

open import Cubical.Categories.Category

-- Here, we give a construction of the syntactic category. This defines the terms
-- that we will be normalising, as well as the rules by which we will do so.

module Syn where
  infixr 20 _⇒_
  data Ty : Type where
    Base : Char → Ty
    _⇒_ : Ty → Ty → Ty

  module _ where
    open Contextual

    𝑟𝑒𝑛 : Contextual lzero lzero
    ty 𝑟𝑒𝑛 = Ty
    tm 𝑟𝑒𝑛 = 𝑉𝑎𝑟 Ty
    _⟦_⟧ 𝑟𝑒𝑛 = _[_]𝑅
    𝒾𝒹 𝑟𝑒𝑛 = id𝑅𝑒𝑛
    𝒾𝒹L 𝑟𝑒𝑛 = ∘𝑅𝑒𝑛IdL
    𝒾𝒹⟦⟧ 𝑟𝑒𝑛 = [id]𝑅𝑒𝑛
    ⟦⟧⟦⟧ 𝑟𝑒𝑛 = [][]𝑅𝑒𝑛
    isSetTm 𝑟𝑒𝑛 = 𝑉𝑎𝑟Path.isSet𝑉𝑎𝑟

  open Contextual 𝑟𝑒𝑛

  Ctx = 𝐶𝑡𝑥 Ty
  Var = 𝑉𝑎𝑟 Ty
  Ren = 𝑅𝑒𝑛 Ty

  data Tm : Ctx → Ty → Type
  Tms = 𝑇𝑚𝑠 Tm

  infixl 20 _∘Tms_
  _∘Tms_ : {Γ Δ Σ : Ctx} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
  idTms : (Γ : Ctx) → Tms Γ Γ
  W₁Tms : {Γ Δ : Ctx} (A : Ty) → Tms Γ Δ → Tms (Γ ⊹ A) Δ
  W₂Tms : {Γ Δ : Ctx} (A : Ty) → Tms Γ Δ → Tms (Γ ⊹ A) (Δ ⊹ A)
  varify : {Γ Δ : Ctx} → Ren Γ Δ → Tms Γ Δ

  -- We use explicit substitutions and give rules for how to substitute into any term constructor.

  infixl 30 _[_]
  data Tm where
    V : {Γ : Ctx} {A : Ty} → Var Γ A → Tm Γ A
    Lam : {Γ : Ctx} {A B : Ty} → Tm (Γ ⊹ A) B → Tm Γ (A ⇒ B)
    App : {Γ : Ctx} {A B : Ty} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
    _[_] : {Γ Δ : Ctx} {A : Ty} → Tm Δ A → Tms Γ Δ → Tm Γ A

    β : {Γ : Ctx} {A B : Ty} (t : Tm (Γ ⊹ A) B) (s : Tm Γ A) →
      App (Lam t) s ≡ t [ idTms Γ ⊕ s ]
    η : {Γ : Ctx} {A B : Ty} (t : Tm Γ (A ⇒ B)) →
      t ≡ Lam (App (t [ varify π ]) (V 𝑧𝑣))

    𝑧𝑣[] : {Γ Δ : Ctx} {A : Ty} (σ : Tms Γ Δ) (t : Tm Γ A)
      → V 𝑧𝑣 [ σ ⊕ t ] ≡ t
    𝑠𝑣[] : {Γ Δ : Ctx} {A B : Ty} (v : Var Δ A) (σ : Tms Γ Δ) (t : Tm Γ B) →
      V (𝑠𝑣 v) [ σ ⊕ t ] ≡ V v [ σ ]
    Lam[] : {Γ Δ : Ctx} {A B : Ty} (t : Tm (Δ ⊹ A) B) (σ : Tms Γ Δ) →
      Lam t [ σ ] ≡ Lam (t [ W₂Tms A σ ])
    App[] : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ (A ⇒ B)) (s : Tm Δ A) (σ : Tms Γ Δ) →
      App t s [ σ ] ≡ App (t [ σ ]) (s [ σ ])

    -- This assumptions is superfluous
    [][] : {Γ Δ Σ : Ctx} {A : Ty} (t : Tm Σ A) (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
      t [ σ ] [ τ ] ≡ t [ σ ∘Tms τ ]

    trunc : {Γ : Ctx} {A : Ty} → isSet (Tm Γ A)

  σ ∘Tms τ = map𝑇𝑚𝑠 _[ τ ] σ

  varify σ = map𝑇𝑚𝑠 V σ

  idTms Γ = varify (𝒾𝒹 Γ)

  W₁Tm : {Γ : Ctx} (A : Ty) {B : Ty} → Tm Γ B → Tm (Γ ⊹ A) B
  W₁Tm {Γ} A t = t [ varify π ]

  W₁Tms {Γ} A σ = σ ∘Tms varify π

  W₂Tms A σ = W₁Tms A σ ⊕ V 𝑧𝑣

  ∘TmsAssoc : {Γ Δ Σ Ω : Ctx} (σ : Tms Σ Ω) (τ : Tms Δ Σ) (μ : Tms Γ Δ) →
    σ ∘Tms τ ∘Tms μ ≡ σ ∘Tms (τ ∘Tms μ)
  ∘TmsAssoc ! τ μ = refl
  ∘TmsAssoc (σ ⊕ t) τ μ i = ∘TmsAssoc σ τ μ i ⊕ [][] t τ μ i

  -- Lemmas on how varify and wekening acts

  Vlem0 : {Γ Δ : Ctx} {A : Ty} (v : Var Δ A) (σ : Ren Γ Δ) →
    V (v ⟦ σ ⟧) ≡ (V v) [ varify σ ]
  Vlem0 𝑧𝑣 (σ ⊕ w) = 𝑧𝑣[] (varify σ) (V w) ⁻¹
  Vlem0 (𝑠𝑣 v) (σ ⊕ w) =
    V (v ⟦ σ ⟧)
      ≡⟨ Vlem0 v σ ⟩
    V v [ varify σ ]
      ≡⟨ 𝑠𝑣[] v (varify σ) (V w) ⁻¹ ⟩
    V (𝑠𝑣 v) [ varify σ ⊕ V w ]
      ∎

  W₁V : {Γ : Ctx} {A B : Ty} (v : Var Γ B) →
    W₁Tm A (V v) ≡ V (𝑠𝑣 v)
  W₁V {Γ} {A} v =
    V v [ varify π ]
      ≡⟨ Vlem0 v π ⁻¹ ⟩
    V (v ⟦ π ⟧)
      ≡⟨ ap V (Wlem2𝑅𝑒𝑛 v (id𝑅𝑒𝑛 Γ)) ⟩
    V (𝑠𝑣 (v [ id𝑅𝑒𝑛 Γ ]𝑅))
      ≡⟨ ap V (ap 𝑠𝑣 ([id]𝑅𝑒𝑛 v)) ⟩
    V (𝑠𝑣 v)
      ∎
      
  Vlem1 : {Γ Δ Σ : Ctx} (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
    varify (σ ∘𝑅𝑒𝑛 τ) ≡ varify σ ∘Tms varify τ
  Vlem1 ! τ = refl
  Vlem1 (σ ⊕ t) τ i = Vlem1 σ τ i ⊕ Vlem0 t τ i 

  Vlem2 : {Γ Δ : Ctx} {A : Ty} (σ : Ren Γ Δ) →
    varify (W₁𝑅𝑒𝑛 A σ) ≡ W₁Tms A (varify σ)
  Vlem2 ! = refl
  Vlem2 (σ ⊕ v) i = Vlem2 σ i ⊕ W₁V v (~ i)

  Vlem3 : {Γ : Ctx} {A : Ty} → W₂Tms A (idTms Γ) ≡ idTms (Γ ⊹ A)
  Vlem3 {∅} = refl
  Vlem3 {Γ ⊹ B} {A} i = Vlem2 π (~ i) ⊕ W₁V 𝑧𝑣 i ⊕ V 𝑧𝑣

  W₁Lam : {Γ : Ctx} {A B C : Ty} (t : Tm (Γ ⊹ B) C) →
    W₁Tm A (Lam t) ≡ Lam (t [ W₂Tms B (varify π) ])
  W₁Lam t = Lam[] t (varify π)
  
  W₁App : {Γ : Ctx} {A B C : Ty} (t : Tm Γ (B ⇒ C)) (s : Tm Γ B) →
    W₁Tm A (App t s) ≡ App (W₁Tm A t) (W₁Tm A s)
  W₁App t s = App[] t s (varify π)

  W₁[] : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) →
    W₁Tm A (t [ σ ]) ≡ t [ W₁Tms A σ ]
  W₁[] t σ = [][] t σ (varify π)

  private
    Wlem1Varify : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Tms Γ Δ) (t : Tm Γ A) →
      varify (W₁𝑅𝑒𝑛 A σ) ∘Tms (τ ⊕ t) ≡ (varify σ) ∘Tms τ
    Wlem1Varify ! τ t = refl
    Wlem1Varify {A = A} (σ ⊕ v) τ t i = Wlem1Varify σ τ t i ⊕ 𝑠𝑣[] v τ t i

  ∘TmsIdL : {Γ Δ : Ctx} (σ : Tms Γ Δ) → idTms Δ ∘Tms σ ≡ σ
  ∘TmsIdL ! = refl
  ∘TmsIdL {Γ} {Δ ⊹ B} (σ ⊕ t) =
    varify (W₁𝑅𝑒𝑛 B (id𝑅𝑒𝑛 Δ)) ∘Tms (σ ⊕ t) ⊕ V 𝑧𝑣 [ σ ⊕ t ]
      ≡⟨ (λ i →  Wlem1Varify (id𝑅𝑒𝑛 Δ) σ t i ⊕ 𝑧𝑣[] σ t i) ⟩
    idTms Δ ∘Tms σ ⊕ t
      ≡⟨ ap (_⊕ t) (∘TmsIdL σ) ⟩
    σ ⊕ t
      ∎

  {-private
    record TmIndStr (P₁ P₂ : {Γ : Ctx} {A : Ty} → Tm Γ A → Tm Γ A) : Type where
      field
        caseV : {Γ : Ctx} {A : Ty} (v : Var Γ A) →
          P₁ (V v) ≡ P₂ (V v)
        caseLam : {Γ : Ctx} {A B : Ty} (t : Tm (Γ ⊹ A) B) →
          P₁ t ≡ P₂ t → P₁ (Lam t) ≡ P₂ (Lam t)
        caseApp : {Γ : Ctx} {A B : Ty} (t : Tm Γ (A ⇒ B)) (s : Tm Γ A) →
          P₁ t ≡ P₂ t → P₁ s ≡ P₂ s → P₁ (App t s) ≡ P₂ (App t s)
        case[] : {Γ Δ : Ctx} {A : Ty} (t : Tm Δ A) (σ : Tms Γ Δ) →
          P₁ t ≡ P₂ t → map𝑇𝑚𝑠 {tm₂ = Tm} P₁ σ ≡ map𝑇𝑚𝑠 P₂ σ → P₁ (t [ σ ]) ≡ P₂ (t [ σ ])

    open TmIndStr

    TmIndLem : {P₁ P₂ : {Γ : Ctx} {A : Ty} → Tm Γ A → Tm Γ A} → TmIndStr P₁ P₂ →
      ({Γ : Ctx} {A : Ty} (t : Tm Γ A) → P₁ t ≡ P₂ t)

    TmsIndLem : {P₁ P₂ : {Γ : Ctx} {A : Ty} → Tm Γ A → Tm Γ A} → TmIndStr P₁ P₂ →
      ({Γ Δ : Ctx} (σ : Tms Γ Δ) → map𝑇𝑚𝑠 {tm₂ = Tm} P₁ σ ≡ map𝑇𝑚𝑠 P₂ σ)
    TmsIndLem pf ! = refl
    TmsIndLem pf (σ ⊕ t) i = TmsIndLem pf σ i ⊕ TmIndLem pf t i

    TmIndLem pf (V v) = caseV pf v
    TmIndLem pf (Lam t) = caseLam pf t (TmIndLem pf t)
    TmIndLem pf (App t s) = caseApp pf t s (TmIndLem pf t) (TmIndLem pf s)
    TmIndLem pf (t [ σ ]) = case[] pf t σ (TmIndLem pf t) (TmsIndLem pf σ)
    
    TmIndLem {P₁} {P₂} pf (β {Γ} t s i) j =
      {!isSet→SquareP (λ i j → trunc)
        (caseApp pf (Lam t) s (caseLam pf t (TmIndLem pf t)) (TmIndLem pf s))
        (case[] pf t (idTms Γ ⊕ s) (TmIndLem pf t)
          (λ k → TmsIndLem pf (idTms Γ) k ⊕ TmIndLem pf s k))
        (λ k → P₁ (β t s k))
        (λ k → P₂ (β t s k)) i j!}
    {-TmIndLem {P₁} {P₂} pf (η t i) j =
      {!isSet→SquareP (λ i j → trunc)
        (TmIndLem pf t)
        (caseLam pf (App (t [ varify π ]) (V 𝑧𝑣)))
        (λ k → P₁ (η t k))
        (λ k → P₂ (η t k)) i j!}
    TmIndLem {P₁} {P₂} pf (𝑧𝑣[] σ t i) j =
      isSet→SquareP (λ i j → trunc)
        (case[] pf (V 𝑧𝑣) (σ ⊕ t))
        (TmIndLem pf t)
        (λ k → P₁ (𝑧𝑣[] σ t k))
        (λ k → P₂ (𝑧𝑣[] σ t k)) i j
    TmIndLem {P₁} {P₂} pf (𝑠𝑣[] v σ t i) j =
      isSet→SquareP (λ i j → trunc)
        (case[] pf (V (𝑠𝑣 v)) (σ ⊕ t))
        (case[] pf (V v) σ)
        (λ k → P₁ (𝑠𝑣[] v σ t k))
        (λ k → P₂ (𝑠𝑣[] v σ t k)) i j
    TmIndLem {P₁} {P₂} pf (Lam[] {A = A} t σ i) j =
      isSet→SquareP (λ i j → trunc)
        (case[] pf (Lam t) σ)
        (caseLam pf (t [ W₂Tms A σ ]))
        (λ k → P₁ (Lam[] t σ k))
        (λ k → P₂ (Lam[] t σ k)) i j
    TmIndLem {P₁} {P₂} pf (App[] t s σ i) j =
      isSet→SquareP (λ i j → trunc)
        (case[] pf (App t s) σ)
        (caseApp pf (t [ σ ]) (s [ σ ]))
        (λ k → P₁ (App[] t s σ k))
        (λ k → P₂ (App[] t s σ k)) i j
    TmIndLem {P₁} {P₂} pf ([][] t σ τ i) j =
      isSet→SquareP (λ i j → trunc)
        (case[] pf (t [ σ ]) τ)
        (case[] pf t (σ ∘Tms τ))
        (λ k → P₁ ([][] t σ τ k))
        (λ k → P₂ ([][] t σ τ k)) i j
    TmIndLem {P₁} {P₂} pf (trunc t s p q i j) =
      isSet→SquareP
      (λ i j →
        isSet→isGroupoid trunc
          (P₁ (trunc t s p q i j))
          (P₂ (trunc t s p q i j)))
        (λ k → TmIndLem pf (p k))
        (λ k → TmIndLem pf (q k))
        (λ k → TmIndLem pf t)
        (λ k → TmIndLem pf s) i j-}-}

  [id]Var : {Γ : Ctx} {A : Ty} (v : Var Γ A) → V v [ idTms Γ ] ≡ V v
  [id]Var {Γ ⊹ B} {A} 𝑧𝑣 =
    𝑧𝑣[] (varify (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ))) (V 𝑧𝑣)
  [id]Var {Γ ⊹ B} {A} (𝑠𝑣 v) =
    V (𝑠𝑣 v) [ varify π ⊕ V 𝑧𝑣 ]
      ≡⟨ 𝑠𝑣[] v (varify π) (V 𝑧𝑣) ⟩
    V v [ varify π ]
      ≡⟨ ap (V v [_]) (Vlem2 (id𝑅𝑒𝑛 Γ)) ⟩
    V v [ W₁Tms B (idTms Γ) ]
      ≡⟨ [][] (V v) (idTms Γ) (varify π) ⁻¹ ⟩
    W₁Tm B (V v [ idTms Γ ])
      ≡⟨ ap (W₁Tm B) ([id]Var v) ⟩
    W₁Tm B (V v)
      ≡⟨ W₁V v ⟩
    V (𝑠𝑣 v)
      ∎

  {-[id]pf : TmIndStr (λ t → t [ idTms _ ]) (λ t → t)
  caseV [id]pf v = [id]Var v
  caseLam [id]pf {Γ} {A} {B} t =
    {!Lam t [ idTms Γ ]
      ≡⟨ Lam[] t (idTms Γ) ⟩
    Lam (t [ W₂Tms A (idTms Γ) ])
      ≡⟨ ap Lam (ap (t [_]) Vlem3) ⟩
    Lam (t [ idTms (Γ ⊹ A) ])
      ≡⟨ ap Lam ([id] t) ⟩
    Lam t
      ∎!}
  caseApp [id]pf = {!!}
  case[] [id]pf = {!!}-}
    

  {-# TERMINATING #-}
  [id] : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → t [ idTms Γ ] ≡ t

  ∘TmsIdR : {Γ Δ : Ctx} (σ : Tms Γ Δ) → σ ∘Tms (idTms Γ) ≡ σ
  ∘TmsIdR ! = refl
  ∘TmsIdR (σ ⊕ t) i = ∘TmsIdR σ i ⊕ [id] t i

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
      ([id] (Lam (App (t [ varify π ]) (V 𝑧𝑣))))
      (λ k → η t k [ idTms Γ ])
      (η t) i j
  [id] {Γ} (𝑧𝑣[] σ t i) j =
    isSet→SquareP (λ i j → trunc)
      ([id] (V 𝑧𝑣 [ σ ⊕ t ]))
      ([id] t)
      (λ k → 𝑧𝑣[] σ t k [ idTms Γ ])
      (𝑧𝑣[] σ t) i j
  [id] {Γ} (𝑠𝑣[] v σ t i) j =
    isSet→SquareP (λ i j → trunc)
      ([id] (V (𝑠𝑣 v) [ σ ⊕ t ]))
      ([id] (V v [ σ ]))
      (λ k → 𝑠𝑣[] v σ t k [ idTms Γ ])
      (𝑠𝑣[] v σ t) i j
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

module _ where
  open Contextual
  open CCC
  open Syn

  -- Finally we define the contextual cateogy σιν and its ambient category SYN

  σιν : Contextual lzero lzero
  ty σιν = Ty
  tm σιν = Tm
  _⟦_⟧ σιν = _[_]
  𝒾𝒹 σιν = idTms
  𝒾𝒹L σιν = ∘TmsIdL
  𝒾𝒹⟦⟧ σιν = [id]
  ⟦⟧⟦⟧ σιν = [][]
  isSetTm σιν = trunc

  instance
    σινCCC : CCC σιν
    _⇛_ σινCCC = _⇒_
    Λ σινCCC = Lam
    𝑎𝑝𝑝 σινCCC = App
    Λnat σινCCC = Lam[]
    𝑎𝑝𝑝β σινCCC = β
    𝑎𝑝𝑝η σινCCC = η

  SYN : Precategory lzero lzero
  SYN = ambCat σιν

  instance
    isCatSyn : isCategory SYN
    isCatSyn .isSetHom = isSetTms σιν
