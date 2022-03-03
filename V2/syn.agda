{-# OPTIONS --cubical #-}

module syn where

open import lists
open import contextual
open import ccc

module Syn {X : Type} where

  infixr 20 _⇒_
  data Ty : Type where
    Base : X → Ty
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

  infixl 30 _[_] _[_]Ren

  _[_]Ren : {Γ Δ : Ctx} {A : Ty} → Tm Δ A → Ren Γ Δ → Tm Γ A
  _[_] : {Γ Δ : Ctx} {A : Ty} → Tm Δ A → Tms Γ Δ → Tm Γ A
  idTms : (Γ : Ctx) → Tms Γ Γ

  {-# NO_POSITIVITY_CHECK #-}
  data Tm where
    V : {Γ : Ctx} {A : Ty} → Var Γ A → Tm Γ A
    Lam : {Γ : Ctx} {A B : Ty} → Tm (Γ ⊹ A) B → Tm Γ (A ⇒ B)
    App : {Γ : Ctx} {A B : Ty} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

    β : {Γ : Ctx} {A B : Ty} (t : Tm (Γ ⊹ A) B) (s : Tm Γ A) →
      App (Lam t) s ≡ t [ idTms Γ ⊕ s ]
    η : {Γ : Ctx} {A B : Ty} (t : Tm Γ (A ⇒ B)) →
      t ≡ Lam (App (t [ π ]Ren) (V 𝑧𝑣))
    
    trunc : {Γ : Ctx} {A : Ty} → isSet (Tm Γ A)

  record Req : Type₁ where
    constructor 𝑅𝐸𝑄
    field
      rR : Ctx → Type
      rW : {Γ : Ctx} {A : Ty} → rR Γ → rR (Γ ⊹ A)

  open Req

  --{-# TERMINATING #-}
  {-TmIndLem : (req : Req)
    {P : (Γ : Ctx) → rR req Γ → Ctx} {Q : (A : Ty) → Ty}
    (f g : {Γ : Ctx} {A : Ty} (r : rR req Γ) → Tm Γ A → Tm (P Γ r) (Q A)) →
    ({Γ : Ctx} {A : Ty} (r : rR req Γ) (v : Var Γ A) → f r (V v) ≡ g r (V v)) →
    ({Γ : Ctx} {A B : Ty} (r : rR req Γ) (t : Tm (Γ ⊹ A) B) →
      f (rW req r) t ≡ g (rW req r) t → f r (Lam t) ≡ g r (Lam t)) →
    ({Γ : Ctx} {A B : Ty} (r : rR req Γ) (t : Tm Γ (A ⇒ B)) (s : Tm Γ A) →
      f r t ≡ g r t → f r s ≡ g r s → f r (App t s) ≡ g r (App t s)) →
    {Γ : Ctx} {A : Ty} (r : rR req Γ) (t : Tm Γ A) → f r t ≡ g r t
  TmIndLem req f g p-var p-lam p-app r (V v) = p-var r v
  TmIndLem req f g p-var p-lam p-app r (Lam t) =
    p-lam r t (TmIndLem req f g p-var p-lam p-app (rW req r) t)
  TmIndLem req f g p-var p-lam p-app r (App t s) =
    p-app r t s (TmIndLem req f g p-var p-lam p-app r t) (TmIndLem req f g p-var p-lam p-app r s)
  TmIndLem req f g p-var p-lam p-app r (β {Γ} t s i) j =
    isSet→SquareP (λ i j → trunc)
      (TmIndLem req f g p-var p-lam p-app r (App (Lam t) s))
      (TmIndLem req f g p-var p-lam p-app r (t [ idTms Γ ⊕ s ]))
      (λ k → f r (β t s k))
      (λ k → g r (β t s k)) i j
  TmIndLem req f g p-var p-lam p-app r (η t i) j =
    isSet→SquareP (λ i j → trunc)
      (TmIndLem req f g p-var p-lam p-app r t)
      (TmIndLem req f g p-var p-lam p-app r (Lam (App (t [ π ]Ren) (V 𝑧𝑣))))
      (λ k → f r (η t k))
      (λ k → g r (η t k)) i j
  TmIndLem req f g p-var p-lam p-app r (trunc t s p q i j) =
    isSet→SquareP
      (λ i j →
        isSet→isGroupoid trunc
          (f r (trunc t s p q i j))
          (g r (trunc t s p q i j)))
      (λ k → TmIndLem req f g p-var p-lam p-app r (p k))
      (λ k → TmIndLem req f g p-var p-lam p-app r (q k))
      (λ k → TmIndLem req f g p-var p-lam p-app r t)
      (λ k → TmIndLem req f g p-var p-lam p-app r s) i j-}

  {-# TERMINATING #-}
  TmIndLem' : (P : {Γ : Ctx} {A : Ty} → Tm Γ A → Type) →
    ({Γ : Ctx} {A : Ty} (t : Tm Γ A) → isProp (P t)) →
    ({Γ : Ctx} {A : Ty} (v : Var Γ A) → P (V v)) →
    ({Γ : Ctx} {A B : Ty} (t : Tm (Γ ⊹ A) B) → P t → P (Lam t)) →
    ({Γ : Ctx} {A B : Ty} (t : Tm Γ (A ⇒ B)) (s : Tm Γ A) → P t → P s → P (App t s)) →
    {Γ : Ctx} {A : Ty} (t : Tm Γ A) → P t
  TmIndLem' P p-prop p-var p-lam p-app (V v) = p-var v
  TmIndLem' P p-prop p-var p-lam p-app (Lam t) =
    p-lam t (TmIndLem' P p-prop p-var p-lam p-app t)
  TmIndLem' P p-prop p-var p-lam p-app (App t s) =
    p-app t s (TmIndLem' P p-prop p-var p-lam p-app t) (TmIndLem' P p-prop p-var p-lam p-app s)
  TmIndLem' P p-prop p-var p-lam p-app (β {Γ} t s i) =
    isProp→PathP (λ i → p-prop (β t s i))
      (TmIndLem' P p-prop p-var p-lam p-app (App (Lam t) s))
      (TmIndLem' P p-prop p-var p-lam p-app (t [ idTms Γ ⊕ s ])) i
  TmIndLem' P p-prop p-var p-lam p-app (η t i) =
    isProp→PathP (λ i → p-prop (η t i))
      (TmIndLem' P p-prop p-var p-lam p-app t)
      (TmIndLem' P p-prop p-var p-lam p-app (Lam (App (t [ π ]Ren) (V 𝑧𝑣)))) i
  TmIndLem' P p-prop p-var p-lam p-app (trunc t s p q i j) =
    isSet→SquareP
      (λ i j → (isProp→isSet (p-prop (trunc t s p q i j))))
      (λ k → TmIndLem' P p-prop p-var p-lam p-app (p k))
      (λ k → TmIndLem' P p-prop p-var p-lam p-app (q k))
      (λ k → TmIndLem' P p-prop p-var p-lam p-app t)
      (λ k → TmIndLem' P p-prop p-var p-lam p-app s) i j

  varify : {Γ Δ : Ctx} → Ren Γ Δ → Tms Γ Δ
  varify σ = map𝐸𝑙𝑠 V σ

  idTms Γ = varify (𝒾𝒹 Γ)

  _ᵣ∘Tms_ : {Γ Δ Σ : Ctx} → Ren Δ Σ → Tms Γ Δ → Tms Γ Σ
  σ ᵣ∘Tms τ = derive𝑅𝑒𝑛 τ σ

  _∘ᵣTms_ : {Γ Δ Σ : Ctx} → Tms Δ Σ → Ren Γ Δ → Tms Γ Σ
  σ ∘ᵣTms τ = map𝐸𝑙𝑠 _[ τ ]Ren σ

  switchLemRen : {Γ Δ : Ctx} {A : Ty} (σ : Ren Γ Δ) (t : Tm Δ A) →
    W₂𝑅𝑒𝑛 A σ ᵣ∘Tms (idTms Γ ⊕ t [ σ ]Ren) ≡ (idTms Δ ⊕ t) ∘ᵣTms σ

  []ᵣ[] : {Γ Δ Σ : Ctx} {A : Ty} (t : Tm Σ A) (σ : Ren Δ Σ) (τ : Tms Γ Δ) →
    t [ σ ]Ren [ τ ] ≡ t [ σ ᵣ∘Tms τ ]

  [][]ᵣ : {Γ Δ Σ : Ctx} {A : Ty} (t : Tm Σ A) (σ : Tms Δ Σ) (τ : Ren Γ Δ) →
    t [ σ ] [ τ ]Ren ≡ t [ σ ∘ᵣTms τ ]

  [][]Ren : {Γ Δ Σ : Ctx} {A : Ty} (t : Tm Σ A) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
    t [ σ ]Ren [ τ ]Ren ≡ t [ σ ⊚ τ ]Ren

  πlemRen : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ B) (σ : Ren Γ Δ) →
    t [ σ ]Ren [ π ]Ren ≡ t [ π ]Ren [ W₂𝑅𝑒𝑛 A σ ]Ren
  πlemRen {Γ} {Δ} {A} t σ =
    t [ σ ]Ren [ π ]Ren
      ≡⟨ [][]Ren t σ π ⟩
    t [ σ ⊚ π ]Ren
      ≡⟨ ap (t [_]Ren) (Wlem3𝑅𝑒𝑛 σ (𝒾𝒹 Γ)) ⟩
    t [ W₁𝑅𝑒𝑛 A (σ ⊚ 𝒾𝒹 Γ) ]Ren
      ≡⟨ (λ i → t [ W₁𝑅𝑒𝑛 A (𝒾𝒹L (𝒾𝒹R σ i) (~ i)) ]Ren) ⟩
    t [ W₁𝑅𝑒𝑛 A (𝒾𝒹 Δ ⊚ σ) ]Ren
      ≡⟨ ap (t [_]Ren) (Wlem5𝑅𝑒𝑛 (𝒾𝒹 Δ) σ ⁻¹) ⟩
    t [ π ⊚ W₂𝑅𝑒𝑛 A σ ]Ren
      ≡⟨ [][]Ren t π (W₂𝑅𝑒𝑛 A σ) ⁻¹ ⟩
    t [ π ]Ren [ W₂𝑅𝑒𝑛 A σ ]Ren
      ∎

  V v [ σ ]Ren = V (v ⟦ σ ⟧)
  Lam {A = A} t [ σ ]Ren = Lam (t [ W₂𝑅𝑒𝑛 A σ ]Ren )
  App t s [ σ ]Ren = App (t [ σ ]Ren) (s [ σ ]Ren)
  _[_]Ren {Γ} (β {Δ} {A} {B} t s i) σ =
    (App (Lam (t [ W₂𝑅𝑒𝑛 A σ ]Ren)) (s [ σ ]Ren)
      ≡⟨ β (t [ W₂𝑅𝑒𝑛 A σ ]Ren) (s [ σ ]Ren) ⟩
    t [ W₂𝑅𝑒𝑛 A σ ]Ren [ idTms Γ ⊕ s [ σ ]Ren ]
      ≡⟨ []ᵣ[] t (W₂𝑅𝑒𝑛 A σ) (idTms Γ ⊕ s [ σ ]Ren) ⟩
    t [ W₂𝑅𝑒𝑛 A σ ᵣ∘Tms (idTms Γ ⊕ s [ σ ]Ren) ]
      ≡⟨ ap (t [_]) (switchLemRen σ s) ⟩
    t [ (idTms Δ ⊕ s) ∘ᵣTms σ ]
      ≡⟨ [][]ᵣ t (idTms Δ ⊕ s) σ ⁻¹ ⟩
    t [ idTms Δ ⊕ s ] [ σ ]Ren
      ∎) i
  _[_]Ren {Γ} (η {Δ} {A} t i) σ =
    (t [ σ ]Ren
      ≡⟨ η (t [ σ ]Ren) ⟩
    Lam (App (t [ σ ]Ren [ π ]Ren) (V 𝑧𝑣))
      ≡⟨ (λ i → Lam (App (πlemRen t σ i) (V 𝑧𝑣))) ⟩
    Lam (App (t [ π ]Ren [ W₂𝑅𝑒𝑛 A σ ]Ren) (V 𝑧𝑣))
      ∎) i
  trunc t s p q i j [ σ ]Ren =
    isSet→SquareP (λ i j → trunc)
      (λ k → p k [ σ ]Ren)
      (λ k → q k [ σ ]Ren)
      (λ k → t [ σ ]Ren)
      (λ k → s [ σ ]Ren) i j

  switchLemRen {Γ} {Δ} σ t =
    derive𝑅𝑒𝑛 (idTms Γ ⊕ t [ σ ]Ren) (map𝐸𝑙𝑠 𝑠𝑣 σ) ⊕ t [ σ ]Ren
      ≡⟨ ap (_⊕ t [ σ ]Ren) (deriveW (idTms Γ) (t [ σ ]Ren) σ) ⟩
    derive𝑅𝑒𝑛 (idTms Γ) σ ⊕ t [ σ ]Ren
      ≡⟨ ap (_⊕ t [ σ ]Ren) (derive𝑅𝑒𝑛Map V (id𝑅𝑒𝑛 Γ) σ) ⟩
    varify (derive𝑅𝑒𝑛 (id𝑅𝑒𝑛 Γ) σ) ⊕ t [ σ ]Ren
      ≡⟨ (λ i → varify (𝒾𝒹L (𝒾𝒹R σ i) (~ i)) ⊕ t [ σ ]Ren) ⟩
    map𝐸𝑙𝑠 V (map𝐸𝑙𝑠 (derive σ) (id𝑅𝑒𝑛 Δ)) ⊕ t [ σ ]Ren
      ≡⟨ ap (_⊕ t [ σ ]Ren) (map𝐸𝑙𝑠comp V (derive σ) (id𝑅𝑒𝑛 Δ)) ⟩
    map𝐸𝑙𝑠 (V ∘ derive σ) (id𝑅𝑒𝑛 Δ) ⊕ t [ σ ]Ren
      ≡⟨ ap (_⊕ t [ σ ]Ren) (map𝐸𝑙𝑠comp _[ σ ]Ren V (id𝑅𝑒𝑛 Δ) ⁻¹) ⟩
    map𝐸𝑙𝑠 _[ σ ]Ren (idTms Δ) ⊕ t [ σ ]Ren
      ∎

  [][]Ren {Γ} {Δ} {Σ} {A} t σ τ =
    TmIndLem'
      (λ {Σ} {A} t → (Γ Δ : Ctx) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
        t [ σ ]Ren [ τ ]Ren ≡ t [ σ ⊚ τ ]Ren)
      (λ {Σ} {A} t → isPropΠ4 (λ Γ Δ σ τ → trunc (t [ σ ]Ren [ τ ]Ren) (t [ σ ⊚ τ ]Ren)))
      (λ v Γ Δ σ τ →
        ap V (⟦⟧⟦⟧ v σ τ))
      (λ {Σ} {A} t p Γ Δ σ τ →
        Lam (t [ W₂𝑅𝑒𝑛 A σ ]Ren [ W₂𝑅𝑒𝑛 A τ ]Ren)
          ≡⟨ ap Lam (p (Γ ⊹ A) (Δ ⊹ A) (W₂𝑅𝑒𝑛 A σ) (W₂𝑅𝑒𝑛 A τ)) ⟩
        Lam (t [ W₂𝑅𝑒𝑛 A σ ⊚ W₂𝑅𝑒𝑛 A τ ]Ren)
          ≡⟨ (λ i → Lam (t [ Wlem4𝑅𝑒𝑛 σ τ i ]Ren)) ⟩
        Lam (t [ W₂𝑅𝑒𝑛 A (σ ⊚ τ) ]Ren)
          ∎)
      (λ t s p q Γ Δ σ τ i → App (p Γ Δ σ τ i) (q Γ Δ σ τ i))
      t Γ Δ σ τ

  {-[][]Ren {Γ} {Δ} {Σ} {A} t σ τ =
    TmIndLem (𝑅𝐸𝑄 req Wreq)
      (λ r t → (t [ rσ r ]Ren) [ rτ r ]Ren)
      (λ r t → t [ rσ r ⊚ rτ r ]Ren)
      (λ r v →
        ap V (⟦⟧⟦⟧ v (rσ r) (rτ r)))
      (λ {Σ} {A} r t p →
        Lam (t [ W₂𝑅𝑒𝑛 A (rσ r) ]Ren [ W₂𝑅𝑒𝑛 A (rτ r) ]Ren)
          ≡⟨ ap Lam p ⟩
        Lam (t [ W₂𝑅𝑒𝑛 A (rσ r) ⊚ W₂𝑅𝑒𝑛 A (rτ r) ]Ren)
          ≡⟨ (λ i → Lam (t [ Wlem4𝑅𝑒𝑛 (rσ r) (rτ r) i ]Ren)) ⟩
        Lam (t [ W₂𝑅𝑒𝑛 A (rσ r ⊚ rτ r) ]Ren)
          ∎)
      (λ r t s p q i → App (p i) (q i))
      (𝑅𝑒𝑞 Γ Δ σ τ) t where
    record req (Σ : Ctx) : Type where
      constructor 𝑅𝑒𝑞
      field
        rΓ rΔ : Ctx
        rσ : Ren rΔ Σ
        rτ : Ren rΓ rΔ
    open req
    Wreq : {Σ : Ctx} {A : Ty} → req Σ → req (Σ ⊹ A)
    rΓ (Wreq {Σ} {A} r) = rΓ r ⊹ A
    rΔ (Wreq {Σ} {A} r) = rΔ r ⊹ A
    rσ (Wreq {Σ} {A} r) = W₂𝑅𝑒𝑛 A (rσ r)
    rτ (Wreq {Σ} {A} r) = W₂𝑅𝑒𝑛 A (rτ r)-}

  W₁Tm : {Γ : Ctx} (A : Ty) {B : Ty} → Tm Γ B → Tm (Γ ⊹ A) B
  W₁Tm A t = t [ π ]Ren

  W₁Tms : {Γ Δ : Ctx} (A : Ty) → Tms Γ Δ → Tms (Γ ⊹ A) Δ
  W₁Tms A σ = map𝐸𝑙𝑠 (W₁Tm A) σ

  W₂Tms : {Γ Δ : Ctx} (A : Ty) → Tms Γ Δ → Tms (Γ ⊹ A) (Δ ⊹ A)
  W₂Tms A σ = W₁Tms A σ ⊕ V 𝑧𝑣

  _∘Tms_ : {Γ Δ Σ : Ctx} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
  σ ∘Tms τ = map𝐸𝑙𝑠 _[ τ ] σ

  [][] : {Γ Δ Σ : Ctx} {A : Ty} (t : Tm Σ A) (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
    t [ σ ] [ τ ] ≡ t [ σ ∘Tms τ ]

  switchLem : {Γ Δ : Ctx} {A : Ty} (σ : Tms Γ Δ) (t : Tm Δ A) →
    W₂Tms A σ ∘Tms (idTms Γ ⊕ t [ σ ]) ≡ (idTms Δ ⊕ t) ∘Tms σ

  πlem : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) →
    t [ σ ] [ π ]Ren ≡ t [ π ]Ren [ W₂Tms A σ ]

  V v [ σ ] = derive σ v
  Lam {Δ} {A} t [ σ ] = Lam (t [ W₂Tms A σ ])
  App t s [ σ ] = App (t [ σ ]) (s [ σ ])
  _[_] {Γ} (β {Δ} {A} {B} t s i) σ =
    (App (Lam (t [ W₂Tms A σ ])) (s [ σ ])
      ≡⟨ β (t [ W₂Tms A σ ]) (s [ σ ]) ⟩
    t [ W₂Tms A σ ] [ idTms Γ ⊕ s [ σ ] ]
      ≡⟨ [][] t (W₂Tms A σ) (idTms Γ ⊕ s [ σ ]) ⟩
    t [ W₂Tms A σ ∘Tms (idTms Γ ⊕ s [ σ ]) ]
      ≡⟨ ap (t [_]) (switchLem σ s) ⟩
    t [ (idTms Δ ⊕ s) ∘Tms σ ]
      ≡⟨ [][] t (idTms Δ ⊕ s) σ ⁻¹ ⟩
    t [ idTms Δ ⊕ s ] [ σ ]
      ∎) i
  η {Δ} {A} t i [ σ ] =
    (t [ σ ]
      ≡⟨ η (t [ σ ]) ⟩
    Lam (App (t [ σ ] [ π ]Ren) (V 𝑧𝑣))
      ≡⟨ (λ i → Lam (App (πlem t σ i) (V 𝑧𝑣))) ⟩
    Lam (App (t [ π ]Ren [ W₂Tms A σ ]) (V 𝑧𝑣))
      ∎) i
  trunc t s p q i j [ σ ] =
    isSet→SquareP (λ i j → trunc)
      (λ k → p k [ σ ])
      (λ k → q k [ σ ])
      (λ k → t [ σ ])
      (λ k → s [ σ ]) i j

  ᵣ∘TmsIdL : {Γ Δ : Ctx} (σ : Tms Γ Δ) → id𝑅𝑒𝑛 Δ ᵣ∘Tms σ ≡ σ
  ᵣ∘TmsIdL ! = refl
  ᵣ∘TmsIdL {Γ} {Δ = Δ ⊹ A} (σ ⊕ t) =
    derive𝑅𝑒𝑛 (σ ⊕ t) π ⊕ t
      ≡⟨ ap (_⊕ t) (deriveW σ t (id𝑅𝑒𝑛 Δ)) ⟩
    derive𝑅𝑒𝑛 σ (id𝑅𝑒𝑛 Δ) ⊕ t
      ≡⟨ ap (_⊕ t) (deriveId σ) ⟩
    σ ⊕ t
      ∎

  [id]ᵣ : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → t [ id𝑅𝑒𝑛 Γ ]Ren ≡ t
  [id]ᵣ t =
    TmIndLem'
      (λ {Γ} t → t [ id𝑅𝑒𝑛 Γ ]Ren ≡ t)
      (λ {Γ} t → trunc (t [ id𝑅𝑒𝑛 Γ ]Ren) t)
      (λ v → ap V (𝒾𝒹⟦⟧ v))
      (λ t p → ap Lam p)
      (λ t s p q i → App (p i) (q i))
      t

  {-[id]ᵣ : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → t [ id𝑅𝑒𝑛 Γ ]Ren ≡ t
  [id]ᵣ t =
    TmIndLem (𝑅𝐸𝑄 (λ Γ → ⊤) (λ t → t))
      (λ {Γ} r t → t [ id𝑅𝑒𝑛 Γ ]Ren)
      (λ r t → t)
      (λ r v → ap V (𝒾𝒹⟦⟧ v))
      (λ {Γ} {A} r t p → ap Lam p)
      (λ r t s p q i → App (p i) (q i))
      tt t-}

  ∘ᵣTmsIdR : {Γ Δ : Ctx} (σ : Tms Γ Δ) → σ ∘ᵣTms (id𝑅𝑒𝑛 Γ) ≡ σ
  ∘ᵣTmsIdR ! = refl
  ∘ᵣTmsIdR (σ ⊕ t) i = ∘ᵣTmsIdR σ i ⊕ [id]ᵣ t i

  WTmLem1Ren : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ B) (σ : Ren Γ Δ) →
    t [ W₁𝑅𝑒𝑛 A σ ]Ren ≡ W₁Tm A (t [ σ ]Ren)
  WTmLem1Ren {A = A} σ τ =
    σ [ W₁𝑅𝑒𝑛 A τ ]Ren
      ≡⟨ ap (σ [_]Ren) (𝒾𝒹R (W₁𝑅𝑒𝑛 A τ) ⁻¹) ⟩
    σ [ makeRen (W₁𝑅𝑒𝑛 A τ) ]Ren
      ≡⟨ ap (σ [_]Ren) (makeW τ) ⟩
    σ [ makeRen τ ⊚ π ]Ren
      ≡⟨ (λ i → [][]Ren σ (𝒾𝒹R τ i) π (~ i)) ⟩
    W₁Tm A (σ [ τ ]Ren)
      ∎

  WTmLem2Ren : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Ren Γ Δ) →
    σ ∘ᵣTms W₁𝑅𝑒𝑛 A τ ≡ W₁Tms A (σ ∘ᵣTms τ)
  WTmLem2Ren ! τ = refl
  WTmLem2Ren {A = A} (σ ⊕ t) τ i = WTmLem2Ren σ τ i ⊕ WTmLem1Ren t τ i

  WTmLem5Ren : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Tms Γ Δ) →
    W₁𝑅𝑒𝑛 A σ ᵣ∘Tms W₂Tms A τ ≡ W₁Tms A (σ ᵣ∘Tms τ)
  WTmLem5Ren ! τ = refl
  WTmLem5Ren (σ ⊕ v) τ i  = WTmLem5Ren σ τ i ⊕ deriveMap _[ π ]Ren τ v i

  πlem {Γ} {Δ} {A} t σ =
    t [ σ ] [ π ]Ren
      ≡⟨ [][]ᵣ t σ π ⟩
    t [ σ ∘ᵣTms π ]
      ≡⟨ ap (t [_]) (WTmLem2Ren σ (id𝑅𝑒𝑛 Γ)) ⟩
    t [ W₁Tms A (σ ∘ᵣTms id𝑅𝑒𝑛 Γ) ]
      ≡⟨ (λ i → t [ W₁Tms A (ᵣ∘TmsIdL (∘ᵣTmsIdR σ i) (~ i)) ]) ⟩
    t [ W₁Tms A (id𝑅𝑒𝑛 Δ ᵣ∘Tms σ) ]
      ≡⟨ ap (t [_]) (WTmLem5Ren (id𝑅𝑒𝑛 Δ) σ ⁻¹) ⟩
    t [ π ᵣ∘Tms W₂Tms A σ ]
      ≡⟨ []ᵣ[] t π (W₂Tms A σ) ⁻¹ ⟩
    t [ π ]Ren [ W₂Tms A σ ]
      ∎

  W₂ᵣ∘Tms : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Tms Γ Δ) →
    W₂𝑅𝑒𝑛 A σ ᵣ∘Tms W₂Tms A τ ≡ W₂Tms A (σ ᵣ∘Tms τ)
  W₂ᵣ∘Tms ! τ = refl
  W₂ᵣ∘Tms {A = A} (σ ⊕ v) τ i = π𝐸𝑙𝑠 (W₂ᵣ∘Tms σ τ i) ⊕ (deriveMap (W₁Tm A) τ v i) ⊕ V 𝑧𝑣

  []ᵣ[] {Γ} {Δ} {Σ} {A} t σ τ =
    TmIndLem'
      (λ {Σ} {A} t → (Γ Δ : Ctx) (σ : Ren Δ Σ) (τ : Tms Γ Δ) →
        t [ σ ]Ren [ τ ] ≡ t [ σ ᵣ∘Tms τ ])
      (λ t → isPropΠ4 (λ Γ Δ σ τ → trunc (t [ σ ]Ren [ τ ]) (t [ σ ᵣ∘Tms τ ])))
      (λ v Γ Δ σ τ → deriveMap (derive τ) σ v ⁻¹)
      (λ {Σ} {A} {B} t p Γ Δ σ τ  →
        Lam (t [ W₂𝑅𝑒𝑛 A σ ]Ren [ W₂Tms A τ ])
          ≡⟨ ap Lam (p (Γ ⊹ A) (Δ ⊹ A) (W₂𝑅𝑒𝑛 A σ) (W₂Tms A τ)) ⟩
        Lam (t [ W₂𝑅𝑒𝑛 A σ ᵣ∘Tms W₂Tms A τ ])
          ≡⟨ (λ i → Lam (t [ W₂ᵣ∘Tms σ τ i ])) ⟩
        Lam (t [ W₂Tms A (σ ᵣ∘Tms τ) ])
          ∎)
      (λ t s p q Γ Δ σ τ i → App (p Γ Δ σ τ i) (q Γ Δ σ τ i))
      t Γ Δ σ τ

  {-[]ᵣ[] {Γ} {Δ} {Σ} {A} t σ τ =
    TmIndLem (𝑅𝐸𝑄 req Wreq)
      (λ r t → (t [ rσ r ]Ren) [ rτ r ])
      (λ r t → t [ rσ r ᵣ∘Tms rτ r ])
      (λ r v →
        deriveMap (derive (rτ r)) (rσ r) v ⁻¹)
      (λ {Γ} {A} {B} r t p →
        Lam (t [ W₂𝑅𝑒𝑛 A (rσ r) ]Ren [ W₂Tms A (rτ r) ])
          ≡⟨ ap Lam p ⟩
        Lam (t [ W₂𝑅𝑒𝑛 A (rσ r) ᵣ∘Tms W₂Tms A (rτ r) ])
          ≡⟨ (λ i → Lam (t [ W₂ᵣ∘Tms (rσ r) (rτ r) i ])) ⟩
        Lam (t [ W₂Tms A (rσ r ᵣ∘Tms rτ r) ])
          ∎)
      (λ r t s p q i →
         App (p i) (q i))
      (𝑅𝑒𝑞 Γ Δ σ τ) t where
    record req (Σ : Ctx) : Type where
      constructor 𝑅𝑒𝑞
      field
        rΓ rΔ : Ctx
        rσ : Ren rΔ Σ
        rτ : Tms rΓ rΔ
    open req
    Wreq : {Σ : Ctx} {A : Ty} → req Σ → req (Σ ⊹ A)
    rΓ (Wreq {Σ} {A} r) = rΓ r ⊹ A
    rΔ (Wreq {Σ} {A} r) = rΔ r ⊹ A
    rσ (Wreq {Σ} {A} r) = W₂𝑅𝑒𝑛 A (rσ r)
    rτ (Wreq {Σ} {A} r) = W₂Tms A (rτ r)-}


  W₂∘ᵣTms : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Ren Γ Δ) →
    W₂Tms A σ ∘ᵣTms W₂𝑅𝑒𝑛 A τ ≡ W₂Tms A (σ ∘ᵣTms τ)
  W₂∘ᵣTms ! τ = refl
  W₂∘ᵣTms (σ ⊕ t) τ i = π𝐸𝑙𝑠 (W₂∘ᵣTms σ τ i) ⊕ πlemRen t τ (~ i) ⊕ V 𝑧𝑣

  [][]ᵣ {Γ} {Δ} {Σ} {A} t σ τ =
    TmIndLem'
      (λ {Σ} {A} t → (Γ Δ : Ctx) (σ : Tms Δ Σ) (τ : Ren Γ Δ) →
        t [ σ ] [ τ ]Ren ≡ t [ σ ∘ᵣTms τ ])
      (λ t → isPropΠ4 (λ Γ Δ σ τ → trunc (t [ σ ] [ τ ]Ren) (t [ σ ∘ᵣTms τ ])))
      (λ v Σ Δ σ τ → deriveMap _[ τ ]Ren σ v ⁻¹)
      (λ {Σ} {A} {B} t p Γ Δ σ τ →
        Lam (t [ W₂Tms A σ ] [ W₂𝑅𝑒𝑛 A τ ]Ren)
          ≡⟨ ap Lam (p (Γ ⊹ A) (Δ ⊹ A) (W₂Tms A σ) (W₂𝑅𝑒𝑛 A τ)) ⟩
        Lam (t [ W₂Tms A σ ∘ᵣTms W₂𝑅𝑒𝑛 A τ ])
          ≡⟨ (λ i → Lam (t [ W₂∘ᵣTms σ τ i ])) ⟩
        Lam (t [ W₂Tms A (σ ∘ᵣTms τ) ])
          ∎)
      (λ t s p q Γ Δ σ τ i → App (p Γ Δ σ τ i) (q Γ Δ σ τ i))
      t Γ Δ σ τ

  WTm[] : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) (s : Tm Γ A) →
    W₁Tm A t [ σ ⊕ s ] ≡ t [ σ ]
  WTm[] {Γ} {Δ} {A} {B} t σ s =
    TmIndLem'
      (λ {Δ} {B} t → (Γ : Ctx) (A : Ty) (σ : Tms Γ Δ) (s : Tm Γ A) →
        W₁Tm A t [ σ ⊕ s ] ≡ t [ σ ])
      (λ t → isPropΠ4 (λ Γ A σ s → trunc (W₁Tm A t [ σ ⊕ s ]) (t [ σ ])))
      (λ v Γ A σ s → ap (derive (σ ⊕ s)) (𝒾𝒹⟦⟧ (𝑠𝑣 v)))
      (λ {Δ} {B} t p Γ A σ s  →
        Lam (t [ W₂𝑅𝑒𝑛 B π ]Ren [ W₂Tms B (σ ⊕ s) ])
          ≡⟨ ap Lam ([]ᵣ[] t (W₂𝑅𝑒𝑛 B π) (W₂Tms B (σ ⊕ s))) ⟩
        Lam (t [ W₂𝑅𝑒𝑛 B π ᵣ∘Tms W₂Tms B (σ ⊕ s) ])
          ≡⟨ (λ i → Lam (t [ W₂ᵣ∘Tms π (σ ⊕ s) i ])) ⟩
        Lam (t [ W₂Tms B (π ᵣ∘Tms (σ ⊕ s)) ])
          ≡⟨ (λ i → Lam (t [ W₂Tms B (map𝐸𝑙𝑠comp (derive (σ ⊕ s)) 𝑠𝑣 (id𝑅𝑒𝑛 Δ) i) ])) ⟩
        Lam (t [ W₂Tms B (id𝑅𝑒𝑛 Δ ᵣ∘Tms σ) ])
          ≡⟨ (λ i → Lam (t [ W₂Tms B (deriveId σ i) ])) ⟩
        Lam (t [ W₂Tms B σ ])
          ∎)
      (λ t s p q Γ A σ s i → App (p Γ A σ s i) (q Γ A σ s i))
      t Γ A σ s
      

  {-[][]ᵣ {Γ} {Δ} {Σ} {A} t σ τ =
    TmIndLem (𝑅𝐸𝑄 req Wreq)
      (λ r t → (t [ rσ r ]) [ rτ r ]Ren)
      (λ r t → t [ rσ r ∘ᵣTms rτ r ])
      (λ r v →
        deriveMap _[ rτ r ]Ren (rσ r) v ⁻¹)
      (λ {Γ} {A} {B} r t p →
        Lam (t [ W₂Tms A (rσ r) ] [ W₂𝑅𝑒𝑛 A (rτ r) ]Ren)
          ≡⟨ ap Lam p ⟩
        Lam (t [ W₂Tms A (rσ r) ∘ᵣTms W₂𝑅𝑒𝑛 A (rτ r) ])
          ≡⟨ (λ i → Lam (t [ W₂∘ᵣTms (rσ r) (rτ r) i ])) ⟩
        Lam (t [ W₂Tms A (rσ r ∘ᵣTms rτ r) ])
          ∎)
      (λ r t s p q i → App (p i) (q i))
      (𝑅𝑒𝑞 Γ Δ σ τ) t where
    record req (Σ : Ctx) : Type where
      constructor 𝑅𝑒𝑞
      field
        rΓ rΔ : Ctx
        rσ : Tms rΔ Σ
        rτ : Ren rΓ rΔ
    open req
    Wreq : {Σ : Ctx} {A : Ty} → req Σ → req (Σ ⊹ A)
    rΓ (Wreq {Σ} {A} r) = rΓ r ⊹ A
    rΔ (Wreq {Σ} {A} r) = rΔ r ⊹ A
    rσ (Wreq {Σ} {A} r) = W₂Tms A (rσ r)
    rτ (Wreq {Σ} {A} r) = W₂𝑅𝑒𝑛 A (rτ r)

  WTm[] : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) (s : Tm Γ A) →
    W₁Tm A t [ σ ⊕ s ] ≡ t [ σ ]
  WTm[] {Γ} {Δ} {A} {B} t σ s =
    TmIndLem (𝑅𝐸𝑄 req Wreq)
      (λ r t → W₁Tm (rA r) t [ rσ r ⊕ rs r ])
      (λ r t → t [ rσ r ])
      (λ r v →
        ap (derive (rσ r ⊕ rs r)) (𝒾𝒹⟦⟧ (𝑠𝑣 v)))
      (λ {Δ} {A} r t p →
        Lam (t [ W₂𝑅𝑒𝑛 A π ]Ren [ W₂Tms A (rσ r ⊕ rs r) ])
          ≡⟨ ap Lam ([]ᵣ[] t (W₂𝑅𝑒𝑛 A π) (W₂Tms A (rσ r ⊕ rs r))) ⟩
        Lam (t [ W₂𝑅𝑒𝑛 A π ᵣ∘Tms W₂Tms A (rσ r ⊕ rs r) ])
          ≡⟨ (λ i → Lam (t [ W₂ᵣ∘Tms π (rσ r ⊕ rs r) i ])) ⟩
        Lam (t [ W₂Tms A (π ᵣ∘Tms (rσ r ⊕ rs r)) ])
          ≡⟨ (λ i → Lam (t [ W₂Tms A (map𝐸𝑙𝑠comp (derive (rσ r ⊕ rs r)) 𝑠𝑣 (id𝑅𝑒𝑛 Δ) i) ])) ⟩
        Lam (t [ W₂Tms A (id𝑅𝑒𝑛 Δ ᵣ∘Tms rσ r) ])
          ≡⟨ (λ i → Lam (t [ W₂Tms A (deriveId (rσ r) i) ])) ⟩
        Lam (t [ W₂Tms A (rσ r) ])
          ∎)
      (λ r t s p q i →
        App (p i) (q i))
      (𝑅𝑒𝑞 Γ A σ s) t where
    record req (Δ : Ctx) : Type where
      constructor 𝑅𝑒𝑞
      field
        rΓ : Ctx
        rA : Ty
        rσ : Tms rΓ Δ
        rs : Tm rΓ rA
    open req
    Wreq : {Σ : Ctx} {A : Ty} → req Σ → req (Σ ⊹ A)
    rΓ (Wreq {Σ} {A} r) = rΓ r ⊹ A
    rA (Wreq {Σ} {A} r) = rA r
    rσ (Wreq {Σ} {A} r) = W₂Tms A (rσ r)
    rs (Wreq {Σ} {A} r) = W₁Tm A (rs r)-}

  WTm∘ : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) (s : Tm Γ A) →
    W₁Tms A σ ∘Tms (τ ⊕ s) ≡ σ ∘Tms τ
  WTm∘ ! τ s = refl
  WTm∘ (σ ⊕ t) τ s i = WTm∘ σ τ s i ⊕ WTm[] t τ s i

  WTmLem1 : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) →
    t [ W₁Tms A σ ] ≡ W₁Tm A (t [ σ ])
  WTmLem1 t σ = [][]ᵣ t σ π ⁻¹

  WTmLem2 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
    σ ∘Tms W₁Tms A τ ≡ W₁Tms A (σ ∘Tms τ)
  WTmLem2 ! τ = refl
  WTmLem2 (σ ⊕ t) τ i = WTmLem2 σ τ i ⊕ WTmLem1 t τ i

  WTmLem3 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
    W₁Tms A σ ∘Tms W₂Tms A τ ≡ W₁Tms A (σ ∘Tms τ)
  WTmLem3 {A = A} σ τ =
    W₁Tms A σ ∘Tms (W₁Tms A τ ⊕ V 𝑧𝑣)
      ≡⟨ WTm∘ σ (W₁Tms A τ) (V 𝑧𝑣) ⟩
    σ ∘Tms W₁Tms A τ
      ≡⟨ WTmLem2 σ τ ⟩
    W₁Tms A (σ ∘Tms τ)
      ∎

  WTmLem4 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
    W₂Tms A σ ∘Tms W₂Tms A τ ≡ W₂Tms A (σ ∘Tms τ)
  WTmLem4 {A = A} σ τ = ap (_⊕ V 𝑧𝑣) (WTmLem3 σ τ)

  [][] {Γ} {Δ} {Σ} {A} t σ τ =
    TmIndLem'
      (λ {Σ} {A} t → (Γ Δ : Ctx) (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
        t [ σ ] [ τ ] ≡ t [ σ ∘Tms τ ])
      (λ t → isPropΠ4 (λ Γ Δ σ τ → trunc (t [ σ ] [ τ ]) (t [ σ ∘Tms τ ])))
      (λ v Γ Δ σ τ → deriveMap _[ τ ] σ v ⁻¹)
      (λ {Σ} {A} t p Γ Δ σ τ →
        Lam (t [ W₂Tms A σ ] [ W₂Tms A τ ])
          ≡⟨ ap Lam (p (Γ ⊹ A) (Δ ⊹ A) (W₂Tms A σ) (W₂Tms A τ)) ⟩
        Lam (t [ W₂Tms A σ ∘Tms W₂Tms A τ ])
          ≡⟨ (λ i → Lam (t [ WTmLem4 σ τ i ])) ⟩
        Lam (t [ W₂Tms A (σ ∘Tms τ) ])
          ∎)
      (λ t s p q Γ Δ σ τ i → App (p Γ Δ σ τ i) (q Γ Δ σ τ i))
      t Γ Δ σ τ

  {-[][] {Γ} {Δ} {Σ} {A} t σ τ =
    TmIndLem req
      (λ r t → t [ rσ r ] [ rτ r ])
      (λ r t → t [ rσ r ∘Tms rτ r ])
      (λ r v →
        deriveMap _[ rτ r ] (rσ r) v ⁻¹)
      (λ {Σ} {A} r t →
        Lam (t [ W₂Tms A (rσ r) ] [ W₂Tms A (rτ r) ])
          ≡⟨ ap Lam ([][] t (W₂Tms A (rσ r)) (W₂Tms A (rτ r))) ⟩
        Lam (t [ W₂Tms A (rσ r) ∘Tms W₂Tms A (rτ r) ])
          ≡⟨ (λ i → Lam (t [ WTmLem4 (rσ r) (rτ r) i ])) ⟩
        Lam (t [ W₂Tms A (rσ r ∘Tms rτ r) ])
          ∎)
      (λ r t s i →
        App ([][] t (rσ r) (rτ r) i) ([][] s (rσ r) (rτ r) i))
      (𝑅𝑒𝑞 Γ Δ σ τ) t where
    record req (Σ : Ctx) (A : Ty) : Type where
      constructor 𝑅𝑒𝑞
      field
        rΓ rΔ : Ctx
        rσ : Tms rΔ Σ
        rτ : Tms rΓ rΔ
    open req-}

  Wvarify : {Γ Δ : Ctx} {A : Ty} (σ : Ren Γ Δ) →
    W₁Tms A (varify σ) ≡ varify (W₁𝑅𝑒𝑛 A σ)
  Wvarify ! = refl
  Wvarify {Γ} {Δ} {A} (σ ⊕ v) =
    W₁Tms A (varify σ) ⊕ V (derive π v)
      ≡⟨ (λ i → Wvarify σ i ⊕ V (deriveMap 𝑠𝑣 (id𝑅𝑒𝑛 Γ) v i)) ⟩
    varify (W₁𝑅𝑒𝑛 A σ) ⊕ V (𝑠𝑣 (derive (id𝑅𝑒𝑛 Γ) v))
      ≡⟨ (λ i → varify (W₁𝑅𝑒𝑛 A σ) ⊕ V (𝑠𝑣 (𝒾𝒹⟦⟧ v i))) ⟩
    varify (W₁𝑅𝑒𝑛 A (σ ⊕ v))
      ∎

  ∘TmsIdL : {Γ Δ : Ctx} (σ : Tms Γ Δ) → idTms Δ ∘Tms σ ≡ σ
  ∘TmsIdL ! = refl
  ∘TmsIdL {Γ} {Δ = Δ ⊹ A} (σ ⊕ t) =
    (varify π ∘Tms (σ ⊕ t)) ⊕ t
      ≡⟨ (λ i → (Wvarify (id𝑅𝑒𝑛 Δ) (~ i) ∘Tms (σ ⊕ t)) ⊕ t) ⟩
    (W₁Tms A (idTms Δ) ∘Tms (σ ⊕ t)) ⊕ t
      ≡⟨ ap (_⊕ t) (WTm∘ (idTms Δ) σ t) ⟩
    (idTms Δ ∘Tms σ) ⊕ t
      ≡⟨ ap (_⊕ t) (∘TmsIdL σ) ⟩
    σ ⊕ t
      ∎

  [id] : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → t [ idTms Γ ] ≡ t
  [id] {Γ} {A} t =
    TmIndLem'
      (λ {Γ} t → t [ idTms Γ ] ≡ t)
      (λ {Γ} t → trunc (t [ idTms Γ ]) t)
      (λ {Γ} v →
        derive (map𝐸𝑙𝑠 V (id𝑅𝑒𝑛 Γ)) v
          ≡⟨ deriveMap V (id𝑅𝑒𝑛 Γ) v ⟩
        V (derive (id𝑅𝑒𝑛 Γ) v)
          ≡⟨ ap V (𝒾𝒹⟦⟧ v) ⟩
        V v
          ∎)
      (λ {Γ} {A} t p →
        Lam (t [ W₂Tms A (idTms Γ) ])
          ≡⟨ (λ i → Lam (t [ Wvarify (id𝑅𝑒𝑛 Γ) i ⊕ V 𝑧𝑣 ])) ⟩
        Lam (t [ idTms (Γ ⊹ A) ])
          ≡⟨ ap Lam p ⟩
        Lam t
          ∎)
      (λ t s p q i → App (p i) (q i))
      t

  {-[id] : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → t [ idTms Γ ] ≡ t
  [id] {Γ} {A} t =
    TmIndLem (λ Γ A → ⊤)
      (λ {Γ} r t → t [ idTms Γ ])
      (λ r t → t)
      (λ {Γ} r v →
        derive (map𝐸𝑙𝑠 V (id𝑅𝑒𝑛 Γ)) v
          ≡⟨ deriveMap V (id𝑅𝑒𝑛 Γ) v ⟩
        V (derive (id𝑅𝑒𝑛 Γ) v)
          ≡⟨ ap V (𝒾𝒹⟦⟧ v) ⟩
        V v
          ∎)
      (λ {Γ} {A} r t →
        Lam (t [ W₂Tms A (idTms Γ) ])
          ≡⟨ (λ i → Lam (t [ Wvarify (id𝑅𝑒𝑛 Γ) i ⊕ V 𝑧𝑣 ])) ⟩
        Lam (t [ idTms (Γ ⊹ A) ])
          ≡⟨ ap Lam ([id] t) ⟩
        Lam t
          ∎)
      (λ r t s i →
        App ([id] t i) ([id] s i))
      tt t-}

  ∘TmsIdR : {Γ Δ : Ctx} (σ : Tms Γ Δ) → σ ∘Tms (idTms Γ) ≡ σ
  ∘TmsIdR ! = refl
  ∘TmsIdR (σ ⊕ t) i = ∘TmsIdR σ i ⊕ [id] t i

  switchLem {Γ} {Δ} {A} σ t =
    W₂Tms A σ ∘Tms (idTms Γ ⊕ t [ σ ])
      ≡⟨ ap (_⊕ t [ σ ]) (WTm∘ σ (idTms Γ) (t [ σ ])) ⟩
    (σ ∘Tms idTms Γ) ⊕ t [ σ ]
      ≡⟨ (λ i → ∘TmsIdL (∘TmsIdR σ i) (~ i) ⊕ t [ σ ]) ⟩
    (idTms Δ ⊕ t) ∘Tms σ
      ∎

  private
    module C = Contextual

  σιν : Contextual lzero lzero
  C.ty σιν = Ty
  C.tm σιν = Tm
  C._⟦_⟧ σιν = _[_]
  C.𝒾𝒹 σιν = idTms
  C.𝒾𝒹L σιν = ∘TmsIdL
  C.𝒾𝒹⟦⟧ σιν = [id]
  C.⟦⟧⟦⟧ σιν = [][]
  C.isSetTm σιν = trunc

  []RenLem : {Γ Δ : Ctx} {A : Ty} (t : Tm Δ A) (σ : Ren Γ Δ) →
    t [ σ ]Ren ≡ t [ varify σ ]
  []RenLem {Γ} {Δ} {A} t σ =
    TmIndLem'
      (λ {Δ} t → (Γ : Ctx) (σ : Ren Γ Δ) → t [ σ ]Ren ≡ t [ varify σ ])
      (λ t → isPropΠ2 (λ Γ σ → trunc (t [ σ ]Ren) (t [ varify σ ])))
      (λ v Γ σ → deriveMap V σ v ⁻¹)
      (λ {Δ} {A} t p Γ σ →
        Lam (t [ W₂𝑅𝑒𝑛 A σ ]Ren)
          ≡⟨ ap Lam (p (Γ ⊹ A) (W₂𝑅𝑒𝑛 A σ)) ⟩
        Lam (t [ varify (W₂𝑅𝑒𝑛 A σ) ])
          ≡⟨ (λ i → Lam (t [ Wvarify σ (~ i) ⊕ V 𝑧𝑣 ])) ⟩
        Lam (t [ W₂Tms A (varify σ) ])
          ∎)
      (λ t s p q Γ σ i → App (p Γ σ i) (q Γ σ i))
      t Γ σ

  ∘ᵣTmsLem : {Γ Δ Σ : Ctx}(σ : Tms Δ Σ) (τ : Ren Γ Δ) →
    σ ∘ᵣTms τ ≡ σ ∘Tms varify τ
  ∘ᵣTmsLem ! τ = refl
  ∘ᵣTmsLem (σ ⊕ t) τ i = ∘ᵣTmsLem σ τ i ⊕ []RenLem t τ i

  {-[]RenLem : {Γ Δ : Ctx} {A : Ty} (t : Tm Δ A) (σ : Ren Γ Δ) →
    t [ σ ]Ren ≡ t [ varify σ ]
  []RenLem {Γ} {Δ} {A} t σ =
    TmIndLem req
      (λ r t → t [ rσ r ]Ren)
      (λ r t → t [ varify (rσ r) ])
      (λ r v → deriveMap V (rσ r) v ⁻¹)
      (λ r t →
        {!Lam (t [ W₂𝑅𝑒𝑛 A₁ (rσ r) ]Ren)
          ≡⟨ ap Lam (!})
      {!!}
      (𝑅𝑒𝑞 Γ σ) t where
    record req (Δ : Ctx) (A : Ty) : Type where
      constructor 𝑅𝑒𝑞
      field
        rΓ : Ctx
        rσ : Ren rΓ Δ
    open req-}

  open CCC

  instance
    σινCCC : CCC σιν
    _⇛_ σινCCC = _⇒_
    Λ σινCCC = Lam
    𝑎𝑝𝑝 σινCCC = App
    Λnat σινCCC t σ i =
      Lam (t [ ∘ᵣTmsLem σ π i ⊕ V 𝑧𝑣 ])
    𝑎𝑝𝑝β σινCCC = β
    𝑎𝑝𝑝η σινCCC t =
      t
        ≡⟨ η t ⟩
      Lam (App (t [ π ]Ren) (V 𝑧𝑣))
        ≡⟨ (λ i → Lam (App ([]RenLem t π i) (V 𝑧𝑣))) ⟩
      Lam (App (t [ varify π ]) (V 𝑧𝑣))
        ∎
