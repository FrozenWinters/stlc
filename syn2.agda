{-# OPTIONS --cubical #-}

module syn2 where

open import contextual

infixr 20 _⇒_
data Ty : Type where
  Base : Char → Ty
  _⇒_ : Ty → Ty → Ty

Ctx = 𝐶𝑡𝑥 Ty
Var = 𝑉𝑎𝑟 Ty
Ren = 𝑅𝑒𝑛 Ty

data Tm : Ctx → Ty → Type
Tms = 𝑇𝑚𝑠 Tm

infixl 30 _[_]
_[_] : {Γ Δ : Ctx} {A : Ty} → Tm Δ A → Tms Γ Δ → Tm Γ A

infixl 20 _∘Tms_
_∘Tms_ : {Γ Δ Σ : Ctx} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
σ ∘Tms τ = map𝑇𝑚𝑠 _[ τ ] σ

idTms : (Γ : Ctx) → Tms Γ Γ
W₁Tm : {Γ : Ctx} (A : Ty) {B : Ty} → Tm Γ B → Tm (Γ ⊹ A) B
W₁Tms : {Γ Δ : Ctx} (A : Ty) → Tms Γ Δ → Tms (Γ ⊹ A) Δ
W₁Tms A σ = map𝑇𝑚𝑠 (W₁Tm A) σ
W₂Tms : {Γ Δ : Ctx} (A : Ty) → Tms Γ Δ → Tms (Γ ⊹ A) (Δ ⊹ A)

{-# NO_POSITIVITY_CHECK #-}
data Tm where
  V : {Γ : Ctx} {A : Ty} → Var Γ A → Tm Γ A
  Lam : {Γ : Ctx} {A B : Ty} → Tm (Γ ⊹ A) B → Tm Γ (A ⇒ B)
  App : {Γ : Ctx} {A B : Ty} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

  β : {Γ : Ctx} {A B : Ty} (t : Tm (Γ ⊹ A) B) (s : Tm Γ A) →
    App (Lam t) s ≡ t [ idTms Γ ⊕ s ]
  η : {Γ : Ctx} {A B : Ty} (t : Tm Γ (A ⇒ B)) →
    t ≡ Lam (App (W₁Tm A t) (V 𝑧𝑣))

  trunc : {Γ : Ctx} {A : Ty} → isSet (Tm Γ A)

W₂Tms A σ = W₁Tms A σ ⊕ V 𝑧𝑣

varify : {Γ Δ : Ctx} → Ren Γ Δ → Tms Γ Δ
varify σ = map𝑇𝑚𝑠 V σ

idTms Γ = varify (id𝑅𝑒𝑛 Γ)

𝑧 : {Γ : Ctx} {A : Ty} → Tm (Γ ⊹ A) A
𝑧 {Γ} {A} = 𝑧𝑇𝑚𝑠 (idTms (Γ ⊹ A))

π : {Γ : Ctx} {A : Ty} → Tms (Γ ⊹ A) Γ
π {Γ} {A} = π𝑇𝑚𝑠 (idTms (Γ ⊹ A))

[][] : {Γ Δ Σ : Ctx} {A : Ty} (t : Tm Σ A) (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
  t [ σ ] [ τ ] ≡ t [ σ ∘Tms τ ]
  
Wlem1 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) (t : Tm Γ A) →
  W₁Tms A σ ∘Tms (τ ⊕ t) ≡ σ ∘Tms τ
  
∘TmsIdL : {Γ Δ : Ctx} (σ : Tms Γ Δ) → idTms Δ ∘Tms σ ≡ σ

∘TmsIdR : {Γ Δ : Ctx} (σ : Tms Γ Δ) → σ ∘Tms (idTms Γ) ≡ σ

V v [ σ ] = derive σ v
Lam {A = A} t [ σ ] = Lam (t [ W₂Tms A σ ])
App t s [ σ ] = App (t [ σ ]) (s [ σ ])

β {Γ} {A} {B} t s i [ σ ] =
  (App (Lam (t [ W₂Tms A σ ])) (s [ σ ])
    ≡⟨ β (t [ W₂Tms A σ ]) (s [ σ ]) ⟩
  t [ W₂Tms A σ ] [ idTms _ ⊕ s [ σ ] ]
    ≡⟨ [][] t (W₂Tms A σ) (idTms _ ⊕ s [ σ ]) ⟩
  t [ W₁Tms A σ ∘Tms (idTms _ ⊕ s [ σ ]) ⊕ s [ σ ] ]
    ≡⟨ (λ i → t [ Wlem1 σ (idTms _) (s [ σ ]) i  ⊕ s [ σ ] ]) ⟩
  t [ σ ∘Tms idTms _ ⊕ s [ σ ] ]
    ≡⟨ (λ i → t [ ∘TmsIdR σ i ⊕ s [ σ ] ]) ⟩
  t [ σ ⊕ s [ σ ] ]
    ≡⟨ (λ i → t [ ∘TmsIdL σ (~ i) ⊕ s [ σ ] ]) ⟩
  t [ (idTms Γ ⊕ s) ∘Tms σ ]
    ≡⟨ [][] t (idTms Γ ⊕ s) σ ⁻¹ ⟩
  t [ idTms Γ ⊕ s ] [ σ ]
    ∎) i
η t i [ σ ] =
  ap _[ σ ] (η t) i
trunc t s p q i j [ σ ] =
  isSet→SquareP (λ i j → trunc)
    (λ k → p k [ σ ])
    (λ k → q k [ σ ])
    (λ k → t [ σ ])
    (λ k → s [ σ ]) i j

-- We now need to construct shifts (i.e. weakening) and for this we need lots of lemmas

data CtxPos : Ctx → Type where
  𝑍 : {Γ : Ctx} → CtxPos Γ
  𝑆 : {Γ : Ctx} {A : Ty} → CtxPos Γ → CtxPos (Γ ⊹ A)

insertCtx : (Γ : Ctx) → Ty → CtxPos Γ → Ctx
insertCtx Γ A 𝑍 = Γ ⊹ A
insertCtx (Γ ⊹ B) A (𝑆 n) = insertCtx Γ A n ⊹ B

varToInsertion : (Γ : Ctx) (A : Ty) (𝑖 : CtxPos Γ) → Var (insertCtx Γ A 𝑖) A
varToInsertion Γ A 𝑍 = 𝑧𝑣
varToInsertion (Γ ⊹ B) A (𝑆 𝑖) = 𝑠𝑣 (varToInsertion Γ A 𝑖)

prefix : {Γ : Ctx} → CtxPos Γ → Ctx
prefix {Γ} 𝑍 = Γ
prefix (𝑆 𝑖) = prefix 𝑖

_+_ : {Γ : Ctx} (𝒾 : CtxPos Γ) → CtxPos (prefix 𝒾) → CtxPos Γ
𝑍 + 𝑗 = 𝑗
𝑆 𝑖 + 𝑗 = 𝑆 (𝑖 + 𝑗)

shiftPos : {Γ : Ctx} {A : Ty} (𝑖 𝑗 : CtxPos Γ) → CtxPos (insertCtx Γ A 𝑖)
shiftPos 𝑖 𝑍 = 𝑍
shiftPos 𝑍 (𝑆 𝑗) = 𝑆 (shiftPos 𝑍 𝑗)
shiftPos (𝑆 𝑖) (𝑆 𝑗) = 𝑆 (shiftPos 𝑖 𝑗)

incPos : {Γ : Ctx} {A : Ty} (𝑖 𝑗 : CtxPos Γ) → CtxPos (insertCtx Γ A 𝑖)
incPos 𝑍 𝑗 = 𝑆 𝑗
incPos (𝑆 𝑖) 𝑍 = 𝑆 𝑍
incPos (𝑆 𝑖) (𝑆 𝑗) = 𝑆 (incPos 𝑖 𝑗)

insertCtx² : {Γ : Ctx} {A B : Ty} (𝑖 : CtxPos Γ) (𝑗 : CtxPos (prefix 𝑖)) →
  insertCtx (insertCtx Γ A 𝑖) B (incPos 𝑖 (𝑖 + 𝑗))
    ≡ insertCtx (insertCtx Γ B (𝑖 + 𝑗)) A (shiftPos (𝑖 + 𝑗) 𝑖)
insertCtx² 𝑍 𝑗 = refl
insertCtx² {Γ ⊹ A} {B} {C} (𝑆 𝑖) 𝑗 i = insertCtx² {Γ} {B} {C} 𝑖 𝑗 i ⊹ A

insertTms : {Γ Δ : Ctx} (𝑖 : CtxPos Δ) → Tms Γ Δ → {A : Ty} → Tm Γ A → Tms Γ (insertCtx Δ A 𝑖)
insertTms 𝑍 σ t = σ ⊕ t
insertTms (𝑆 𝑖) (σ ⊕ s) t = insertTms 𝑖 σ t ⊕ s

{-# TERMINATING #-}
shift : {Γ : Ctx} (𝑖 : CtxPos Γ) {A B : Ty} → Tm Γ B → Tm (insertCtx Γ A 𝑖) B

W₁Tm A t = shift 𝑍 t

shiftTms : {Γ Δ : Ctx} (𝑖 : CtxPos Γ) {A : Ty} → Tms Γ Δ → Tms (insertCtx Γ A 𝑖) Δ
shiftTms 𝑖 = map𝑇𝑚𝑠 (shift 𝑖)

shift² : {Γ : Ctx} {A B C : Ty} (t : Tm Γ C) (𝑖 : CtxPos Γ) (𝑗 : CtxPos (prefix 𝑖)) →
  PathP (λ i → Tm (insertCtx² {Γ} {A} {B} 𝑖 𝑗 i) C)
    (shift (incPos 𝑖 (𝑖 + 𝑗)) {B} (shift 𝑖 {A} t))
    (shift (shiftPos (𝑖 + 𝑗) 𝑖) (shift (𝑖 + 𝑗) t))

shiftLem : {Γ Δ : Ctx} (𝑖 : CtxPos Δ) {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) (s : Tm Γ A) →
  shift 𝑖 t [ insertTms 𝑖 σ s ] ≡ t [ σ ]

shift[] : {Γ Δ : Ctx} (𝑖 : CtxPos Γ) {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) →
  shift 𝑖 {A} (t [ σ ]) ≡ (t [ shiftTms 𝑖 σ ])

idInsertLem : (Γ : Ctx) (A : Ty) (𝑖 : CtxPos Γ) →
  idTms (insertCtx Γ A 𝑖) ≡ insertTms 𝑖 (shiftTms 𝑖 (idTms Γ)) (V (varToInsertion Γ A 𝑖))

shiftVar : {Γ : Ctx} (𝑖 : CtxPos Γ) {B A : Ty} → Var Γ A → Var (insertCtx Γ B 𝑖) A
shiftVar 𝑍 v = 𝑠𝑣 v
shiftVar (𝑆 𝑖) 𝑧𝑣 = 𝑧𝑣
shiftVar (𝑆 𝑖) (𝑠𝑣 v) = 𝑠𝑣 (shiftVar 𝑖 v)

shiftRen : {Γ Δ : Ctx} (𝑖 : CtxPos Γ) {A : Ty} → Ren Γ Δ → Ren (insertCtx Γ A 𝑖) Δ
shiftRen 𝑖 = map𝑇𝑚𝑠 (shiftVar 𝑖)

shift 𝑖 (V v) = V (shiftVar 𝑖 v)
shift 𝑖 (Lam t) = Lam (shift (𝑆 𝑖) t)
shift 𝑖 (App t s) = App (shift 𝑖 t) (shift 𝑖 s)

shift {Γ} 𝑖 {A} {B} (β {Γ} {C} t s i) =
  (App (Lam (shift (𝑆 𝑖) {A} t)) (shift 𝑖 s)
    ≡⟨ β (shift (𝑆 𝑖) t) (shift 𝑖 s) ⟩
  shift (𝑆 𝑖) t [ idTms (insertCtx Γ A 𝑖) ⊕ shift 𝑖 s ]
    ≡⟨ (λ i → shift (𝑆 𝑖) t [ idInsertLem Γ A 𝑖 i ⊕ shift 𝑖 s ]) ⟩
  shift (𝑆 𝑖) t [ insertTms (𝑆 𝑖) (shiftTms 𝑖 (idTms Γ ⊕ s)) (V (varToInsertion Γ A 𝑖)) ]
    ≡⟨ shiftLem (𝑆 𝑖) t (shiftTms 𝑖 (idTms Γ ⊕ s)) (V (varToInsertion Γ A 𝑖)) ⟩
  t [ shiftTms 𝑖 (idTms Γ ⊕ s) ]
    ≡⟨ shift[] 𝑖 t (idTms Γ ⊕ s) ⁻¹ ⟩
  shift 𝑖 (t [ idTms Γ ⊕ s ])
    ∎) i
shift {Γ} 𝑖 {A} {B₁ ⇒ B₂} (η t i) =
  (shift 𝑖 t
    ≡⟨ η (shift 𝑖 t) ⟩
  Lam (App (W₁Tm B₁ (shift 𝑖 t)) (V 𝑧𝑣))
    ≡⟨ (λ i → Lam (App (shift² t 𝑍 𝑖 (~ i)) (V 𝑧𝑣))) ⟩
  Lam (App (shift (𝑆 𝑖) (shift 𝑍 t)) (V 𝑧𝑣))
    ∎) i
shift 𝑖 (trunc t s p q i j) =
  isSet→SquareP (λ i j → trunc)
    (λ k → shift 𝑖 (p k))
    (λ k → shift 𝑖 (q k))
    (λ k → shift 𝑖 t)
    (λ k → shift 𝑖 s) i j

shiftVar² : {Γ : Ctx} {A B C : Ty} (v : Var Γ C) (𝑖 : CtxPos Γ) (𝑗 : CtxPos (prefix 𝑖)) →
  PathP (λ i → Var (insertCtx² {Γ} {A} {B} 𝑖 𝑗 i) C)
    (shiftVar (incPos 𝑖 (𝑖 + 𝑗)) {B} (shiftVar 𝑖 {A} v))
    (shiftVar (shiftPos (𝑖 + 𝑗) 𝑖) (shiftVar (𝑖 + 𝑗) v))
shiftVar² v 𝑍 𝑗 = refl
shiftVar² 𝑧𝑣 (𝑆 𝑖) 𝑗 i = 𝑧𝑣
shiftVar² (𝑠𝑣 v) (𝑆 𝑖) 𝑗 i = 𝑠𝑣 (shiftVar² v 𝑖 𝑗 i)

private
  record TmIndStr (P₁ P₂ : {Γ : Ctx} {A : Ty} → Tm Γ A → Tm Γ A) : Type where
    field
      caseV : {Γ : Ctx} {A : Ty} (v : Var Γ A) →
        P₁ (V v) ≡ P₂ (V v)
      caseLam : {Γ : Ctx} {A B : Ty} (t : Tm (Γ ⊹ A) B) →
        P₁ t ≡ P₂ t → P₁ (Lam t) ≡ P₂ (Lam t)
      caseApp : {Γ : Ctx} {A B : Ty} (t : Tm Γ (A ⇒ B)) (s : Tm Γ A) →
        P₁ t ≡ P₂ t → P₁ s ≡ P₂ s → P₁ (App t s) ≡ P₂ (App t s)

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
  
  TmIndLem {P₁} {P₂} pf (β {Γ} t s i) j =
    isSet→SquareP (λ i j → trunc)
      (TmIndLem pf (App (Lam t) s))
      (TmIndLem pf (t [ idTms Γ ⊕ s ]))
      (λ k → P₁ (β t s k))
      (λ k → P₂ (β t s k)) i j
  TmIndLem {P₁} {P₂} pf (η {Γ} {A} t i) j =
    isSet→SquareP (λ i j → trunc)
      (TmIndLem pf t)
      (TmIndLem pf (Lam (App (W₁Tm A t) (V 𝑧𝑣))))
      (λ k → P₁ (η t k))
      (λ k → P₂ (η t k)) i j
  TmIndLem {P₁} {P₂} pf (trunc t s a b i j) =
    isSet→SquareP
      (λ i j →
        isSet→isGroupoid trunc
          (P₁ (trunc t s a b i j))
          (P₂ (trunc t s a b i j)))
      (λ k → TmIndLem pf (a k))
      (λ k → TmIndLem pf (b k))
      (λ k → TmIndLem pf t)
      (λ k → TmIndLem pf s) i j

  {-TmIndLem pf (V v) = caseV pf v
  TmIndLem pf (Lam t) = caseLam pf t (TmIndLem pf t)
  TmIndLem pf (App t s) = caseApp pf t s (TmIndLem pf t) (TmIndLem pf s)
  TmIndLem pf (t [ σ ]) = case[] pf t σ (TmIndLem pf t) (TmsIndLem pf σ)-}

shift² (V v) 𝑖 𝑗 i = V (shiftVar² v 𝑖 𝑗 i)
shift² (Lam t) 𝑖 𝑗 i = Lam (shift² t (𝑆 𝑖) 𝑗 i)
shift² (App t s) 𝑖 𝑗 i = App (shift² t 𝑖 𝑗 i) (shift² s 𝑖 𝑗 i)

shift² (β t s i) 𝑖 𝑗 j = {!!}
shift² (η t i) 𝑖 𝑗 = {!!}
shift² (trunc t s p q i j) 𝑖 𝑗 = {!!}

shift²Tms : {Γ Δ : Ctx} {A B : Ty} (σ : Tms Γ Δ) (𝑖 : CtxPos Γ) (𝑗 : CtxPos (prefix 𝑖)) →
  PathP (λ i → Tms (insertCtx² {Γ} {A} {B} 𝑖 𝑗 i) Δ)
    (shiftTms (incPos 𝑖 (𝑖 + 𝑗)) {B} (shiftTms 𝑖 {A} σ))
    (shiftTms (shiftPos (𝑖 + 𝑗) 𝑖) (shiftTms (𝑖 + 𝑗) σ))
shift²Tms ! 𝑖 𝑗 i = !
shift²Tms (σ ⊕ t) 𝑖 𝑗 i = shift²Tms σ 𝑖 𝑗 i ⊕ shift² t 𝑖 𝑗 i

deriveLem : {Γ Δ : Ctx} (𝑖 : CtxPos Δ) {A B : Ty} (σ : Tms Γ Δ) (s : Tm Γ A) (v : Var Δ B) →
  derive (insertTms 𝑖 σ s) (shiftVar 𝑖 v) ≡ derive σ v
deriveLem 𝑍 σ s v = refl
deriveLem (𝑆 𝑖) (σ ⊕ t) s 𝑧𝑣 = refl
deriveLem (𝑆 𝑖) (σ ⊕ t) s (𝑠𝑣 v) = deriveLem 𝑖 σ s v

deriveLem2 : {Γ Δ : Ctx} (𝑖 : CtxPos Γ) {A B : Ty} (σ : Tms Γ Δ) (v : Var Δ B) →
  shift 𝑖 {A} (derive σ v) ≡ derive (shiftTms 𝑖 σ) v
deriveLem2 𝑖 (σ ⊕ t) 𝑧𝑣 = refl
deriveLem2 𝑖 (σ ⊕ t) (𝑠𝑣 v) = deriveLem2 𝑖 σ v

W₁InsertLem : {Γ Δ : Ctx} (𝑖 : CtxPos Δ) {A B : Ty} (σ : Tms Γ Δ) (s : Tm Γ B) →
  W₁Tms A (insertTms 𝑖 σ s) ≡ insertTms 𝑖 (W₁Tms A σ) (W₁Tm A s)
W₁InsertLem 𝑍 σ s = refl
W₁InsertLem (𝑆 𝑖) {A} (σ ⊕ t) s i = W₁InsertLem 𝑖 σ s i ⊕ W₁Tm A t

shiftInsertLem : {Γ Δ : Ctx} (𝑖 : CtxPos Γ) (𝑗 : CtxPos Δ) {A B : Ty} (σ : Tms Γ Δ) (s : Tm Γ B) →
  shiftTms 𝑖 {A} (insertTms 𝑗 σ s) ≡ insertTms 𝑗 (shiftTms 𝑖 σ) (shift 𝑖 s)
shiftInsertLem 𝑖 𝑍 σ s = refl
shiftInsertLem 𝑖 (𝑆 𝑗) (σ ⊕ t) s i = shiftInsertLem 𝑖 𝑗 σ s i ⊕ shift 𝑖 t

{-shiftLemPf :  {Γ Δ : Ctx} (𝑖 : CtxPos Δ) {A B : Ty} (σ : Tms Γ Δ) (s : Tm Γ A) →
  TmIndStr (λ t → shift 𝑖 t [ insertTms 𝑖 σ s ]) (λ t → t [ σ ])-}

shiftLem 𝑖 (V v) σ s =
  deriveLem 𝑖 σ s v
shiftLem 𝑖 (Lam {Γ} {A} t) σ s =
  Lam (shift (𝑆 𝑖) t [ W₂Tms A (insertTms 𝑖 σ s) ])
    ≡⟨ (λ i → Lam (shift (𝑆 𝑖) t [ W₁InsertLem 𝑖 σ s i ⊕ 𝑧 ])) ⟩
  Lam (shift (𝑆 𝑖) t [ insertTms (𝑆 𝑖) (W₂Tms A σ) (W₁Tm A s) ])
    ≡⟨ ap Lam (shiftLem (𝑆 𝑖) t (W₂Tms A σ) (W₁Tm A s) ) ⟩
  Lam (t [ W₂Tms A σ ])
    ∎
    
shiftLem 𝑖 (App t₁ t₂) σ s i =
  App (shiftLem 𝑖 t₁ σ s i) (shiftLem 𝑖 t₂ σ s i)
shiftLem {Γ} {Δ} 𝑖 (β t₁ t₂ i) σ s j =
  isSet→SquareP (λ i j → trunc)
    (shiftLem 𝑖 (App (Lam t₁) t₂) σ s)
    (shiftLem 𝑖 (t₁ [ idTms Δ ⊕ t₂ ]) σ s)
    (λ k → shift 𝑖 (β t₁ t₂ k) [ insertTms 𝑖 σ s ])
    (λ k → β t₁ t₂ k [ σ ]) i j
shiftLem 𝑖 (η {Γ} {A} t i) σ s =
  {!isSet→SquareP (λ i j → trunc)
    (shiftLem 𝑖 t σ s)
    (shiftLem 𝑖 (Lam (App (W₁Tm A t) (V 𝑧𝑣))) σ s)
    (λ k → shift 𝑖 (η t k) [ insertTms 𝑖 σ s ])
    (λ k → η t k [ σ ]) i!}
shiftLem 𝑖 (trunc t₁ t₂ p q i j) σ s =
  {!!}

shift[] 𝑖 (V v) σ =
  deriveLem2 𝑖 σ v
shift[] 𝑖 (Lam {Γ} {A} t) σ =
  Lam (shift (𝑆 𝑖) (t [ W₂Tms A σ ]))
    ≡⟨ ap Lam (shift[] (𝑆 𝑖) t (W₂Tms A σ)) ⟩
  Lam (t [ shiftTms (𝑆 𝑖) (shiftTms 𝑍 σ) ⊕ 𝑧 ])
    ≡⟨ (λ i → Lam (t [ map𝑇𝑚𝑠comp {tm₂ = Tm} (shift (𝑆 𝑖)) (shift 𝑍) σ i ⊕ 𝑧 ])) ⟩
  Lam (t [ map𝑇𝑚𝑠 (shift (𝑆 𝑖) ∘ shift 𝑍) σ ⊕ 𝑧 ])
    ≡⟨ (λ i → Lam (t [ map𝑇𝑚𝑠 (λ u → shift² u 𝑍 𝑖 i) σ ⊕ 𝑧 ])) ⟩
  Lam (t [ map𝑇𝑚𝑠 (λ u → shift 𝑍 (shift 𝑖 u)) σ ⊕ 𝑧 ])
    ≡⟨ (λ i → Lam (t [ map𝑇𝑚𝑠comp {tm₂ = Tm} (shift 𝑍) (shift 𝑖) σ (~ i) ⊕ 𝑧 ])) ⟩
  Lam (t [ W₂Tms A (shiftTms 𝑖 σ) ])
    ∎
shift[] 𝑖 (App t s) σ i =
  App (shift[] 𝑖 t σ i) (shift[] 𝑖 s σ i)

shift[] 𝑖 (β t s i) σ = {!!}
shift[] 𝑖 (η t i) σ = {!!}
shift[] 𝑖 (trunc t s p q i j) σ = {!!}

Vlem0 : {Γ Δ : Ctx} {A : Ty} (v : Var Δ A) (σ : Ren Γ Δ) →
  V (v [ σ ]𝑅) ≡ (V v) [ varify σ ]
Vlem0 𝑧𝑣 (σ ⊕ w) = refl
Vlem0 (𝑠𝑣 v) (σ ⊕ w) = Vlem0 v σ

Vlem1 : {Γ Δ Σ : Ctx} (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  varify (σ ∘𝑅𝑒𝑛 τ) ≡ varify σ ∘Tms varify τ
Vlem1 ! τ = refl
Vlem1 (σ ⊕ t) τ i = Vlem1 σ τ i ⊕ Vlem0 t τ i 

Vlem2 : {Γ Δ : Ctx} {A : Ty} (σ : Ren Γ Δ) →
  varify (W₁𝑅𝑒𝑛 A σ) ≡ W₁Tms A (varify σ)
Vlem2 ! = refl
Vlem2 (σ ⊕ v) i = Vlem2 σ i ⊕ V (𝑠𝑣 v)

Vlem3 : {Γ : Ctx} {A : Ty} → W₂Tms A (idTms Γ) ≡ idTms (Γ ⊹ A)
Vlem3 {Γ} i = Vlem2 (id𝑅𝑒𝑛 Γ) (~ i) ⊕ V 𝑧𝑣

idInsertLem Γ A 𝑍 i = Vlem2 (id𝑅𝑒𝑛 Γ) i ⊕ V 𝑧𝑣
idInsertLem (Γ ⊹ B) A (𝑆 𝑖) =
  idTms (insertCtx Γ A 𝑖 ⊹ B)
    ≡⟨ (λ i → Vlem2 (id𝑅𝑒𝑛 (insertCtx Γ A 𝑖)) i ⊕ V 𝑧𝑣) ⟩
  W₁Tms B (idTms (insertCtx Γ A 𝑖)) ⊕ V 𝑧𝑣
    ≡⟨ (λ i → W₁Tms B (idInsertLem Γ A 𝑖 i) ⊕ V 𝑧𝑣) ⟩
  W₁Tms B (insertTms 𝑖 (shiftTms 𝑖 (idTms Γ)) (V (varToInsertion Γ A 𝑖))) ⊕ V 𝑧𝑣
    ≡⟨ (λ i → W₁InsertLem 𝑖 (shiftTms 𝑖 (idTms Γ)) (V (varToInsertion Γ A 𝑖)) i ⊕ V 𝑧𝑣) ⟩
  insertTms 𝑖 (W₁Tms B (shiftTms 𝑖 (idTms Γ))) (V (𝑠𝑣 (varToInsertion Γ A 𝑖))) ⊕ V 𝑧𝑣
    ≡⟨ (λ i → insertTms 𝑖 (shift²Tms (idTms Γ) 𝑍 𝑖 (~ i)) (V (𝑠𝑣 (varToInsertion Γ A 𝑖))) ⊕ V 𝑧𝑣) ⟩
  insertTms 𝑖 (shiftTms (𝑆 𝑖) (W₁Tms B (idTms Γ))) (V (𝑠𝑣 (varToInsertion Γ A 𝑖))) ⊕ V 𝑧𝑣
    ≡⟨ (λ i → insertTms 𝑖 (shiftTms (𝑆 𝑖) (Vlem2 (id𝑅𝑒𝑛 Γ) (~ i)))
      (V (𝑠𝑣 (varToInsertion Γ A 𝑖))) ⊕ V 𝑧𝑣) ⟩
  insertTms (𝑆 𝑖) (shiftTms (𝑆 𝑖) (idTms (Γ ⊹ B))) (V (varToInsertion (Γ ⊹ B) A (𝑆 𝑖)))
    ∎
    
Wlem0 : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ B) (σ : Tms Γ Δ) (s : Tm Γ A) →
  W₁Tm A t [ σ ⊕ s ] ≡ t [ σ ]
Wlem0 t σ s = shiftLem 𝑍 t σ s

Wlem1 ! τ t = refl
Wlem1 (σ ⊕ s) τ t i = Wlem1 σ τ t i ⊕ Wlem0 s τ t i

Wlem2 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
  σ ∘Tms W₁Tms A τ ≡ W₁Tms A (σ ∘Tms τ)
Wlem2 ! τ = refl
Wlem2 {A = A} (σ ⊕ t) τ i = Wlem2 σ τ i ⊕ shift[] 𝑍 t τ (~ i) 

Wlem3 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
  W₁Tms A σ ∘Tms W₂Tms A τ ≡ W₁Tms A (σ ∘Tms τ)
Wlem3 {A = A} σ τ =
  W₁Tms A σ ∘Tms (W₁Tms A τ ⊕ 𝑧)
    ≡⟨ Wlem1 σ (W₁Tms A τ) 𝑧 ⟩
  σ ∘Tms W₁Tms A τ
    ≡⟨ Wlem2 σ τ ⟩
  W₁Tms A (σ ∘Tms τ)
    ∎

Wlem4 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
  (W₂Tms A σ ∘Tms W₂Tms A τ) ≡ W₂Tms A (σ ∘Tms τ)
Wlem4 σ τ i = Wlem3 σ τ i ⊕ 𝑧

[][]Var : {Γ Δ Σ : Ctx} {A : Ty} (v : Var Σ A) (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
  V v [ σ ] [ τ ] ≡ V v [ σ ∘Tms τ ]
[][]Var 𝑧𝑣 (σ ⊕ t) τ = refl
[][]Var (𝑠𝑣 v) (σ ⊕ t) τ = [][]Var v σ τ

[][] (V v) σ τ = [][]Var v σ τ
[][] (Lam {Γ} {A} t) σ τ =
  Lam (t [ W₂Tms A σ ] [ W₂Tms A τ ])
    ≡⟨ ap Lam ([][] t (W₂Tms A σ) (W₂Tms A τ)) ⟩
  Lam (t [ W₂Tms A σ ∘Tms W₂Tms A τ ])
    ≡⟨ (λ i → Lam (t [ Wlem4 σ τ i ])) ⟩
  Lam (t [ W₂Tms A (σ ∘Tms τ) ])
    ∎
[][] (App t s) σ τ i = App ([][] t σ τ i) ([][] s σ τ i)

[][] (β {Γ} t s i) σ τ =
  isSet→SquareP (λ i j → trunc)
    ([][] (App (Lam t) s) σ τ)
    ([][] (t [ idTms Γ ⊕ s ]) σ τ)
    (λ k → β t s k [ σ ] [ τ ])
    (λ k → β t s k [ σ ∘Tms τ ]) i
[][] (η {Γ} {A} {B} t i) σ τ =
  {!isSet→SquareP (λ i j → trunc)
    ([][] t σ τ)
    ([][] (Lam (App (W₁Tm A t) (V 𝑧𝑣))) σ τ)
    (λ k → η t k [ σ ] [ τ ])
    (λ k → η t k [ σ ∘Tms τ ]) i!}
[][] (trunc t s p q i j) σ τ =
  isSet→SquareP
    (λ i j →
      isSet→isGroupoid trunc
        (trunc t s p q i j [ σ ] [ τ ])
        (trunc t s p q i j [ σ ∘Tms τ ]))
    (λ k → [][] (p k) σ τ)
    (λ k → [][] (q k) σ τ)
    (λ k → [][] t σ τ)
    (λ k → [][] s σ τ) i j 

deriveW₁Ren : {Γ Δ : Ctx} {A B : Ty} (σ : Ren Γ Δ) (v : Var Δ B) →
  derive (varify (W₁𝑅𝑒𝑛 A σ)) v ≡ W₁Tm A (derive (varify σ) v)
deriveW₁Ren (σ ⊕ w) 𝑧𝑣 = refl
deriveW₁Ren (σ ⊕ w) (𝑠𝑣 v) = deriveW₁Ren σ v

deriveId : {Γ : Ctx} {A : Ty} (v : Var Γ A) →
  derive (idTms Γ) v ≡ V v
deriveId {Γ ⊹ B} 𝑧𝑣 = refl
deriveId {Γ ⊹ B} (𝑠𝑣 v) =
  derive (varify (W₁𝑅𝑒𝑛 B (id𝑅𝑒𝑛 Γ))) v
    ≡⟨ deriveW₁Ren (id𝑅𝑒𝑛 Γ) v ⟩
  W₁Tm B (derive (varify (id𝑅𝑒𝑛 Γ)) v)
    ≡⟨ ap (W₁Tm B) (deriveId v) ⟩
  V (𝑠𝑣 v)
    ∎

[id] : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → t [ idTms Γ ] ≡ t

∘TmsIdR ! = refl
∘TmsIdR (σ ⊕ t) i = ∘TmsIdR σ i ⊕ [id] t i

[id] (V v) = deriveId v
[id] (Lam {Γ} {A} t) =
  Lam (t [ W₂Tms A (idTms Γ) ])
    ≡⟨ (λ i → Lam (t [ Vlem3 i ])) ⟩
  Lam (t [ idTms (Γ ⊹ A) ])
    ≡⟨ ap Lam ([id] t) ⟩
  Lam t
    ∎
[id] (App t s) i =
  App ([id] t i) ([id] s i)

[id] (β t s i) = {!!}
[id] (η t i) = {!!}
[id] (trunc t s p q i j) = {!!}

Wlem1Varify : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Tms Γ Δ) (t : Tm Γ A) →
  varify (W₁𝑅𝑒𝑛 A σ) ∘Tms (τ ⊕ t) ≡ (varify σ) ∘Tms τ
Wlem1Varify ! τ t = refl
Wlem1Varify {A = A} (σ ⊕ v) τ t i = Wlem1Varify σ τ t i ⊕ V v [ τ ]

∘TmsIdL ! = refl
∘TmsIdL {Γ} {Δ ⊹ B} (σ ⊕ t) =
  varify (W₁𝑅𝑒𝑛 B (id𝑅𝑒𝑛 Δ)) ∘Tms (σ ⊕ t) ⊕ t
    ≡⟨ (λ i → Wlem1Varify (id𝑅𝑒𝑛 Δ) σ t i ⊕ t) ⟩
  varify (id𝑅𝑒𝑛 Δ) ∘Tms σ ⊕ t
    ≡⟨ ap (_⊕ t) (∘TmsIdL σ) ⟩
  σ ⊕ t
    ∎

Wlem5 : {Γ Δ : Ctx} {A : Ty} (σ : Tms Γ Δ) →
  σ ∘Tms π ≡ W₁Tms A σ
Wlem5 {Γ} {Δ} {A} σ =
  σ ∘Tms π
    ≡⟨ ap (σ ∘Tms_) (Vlem2 (id𝑅𝑒𝑛 Γ)) ⟩
  σ ∘Tms W₁Tms A (idTms Γ)
    ≡⟨ Wlem2 σ (idTms Γ) ⟩
  W₁Tms A (σ ∘Tms idTms Γ)
    ≡⟨ ap (W₁Tms A) (∘TmsIdR σ) ⟩
  W₁Tms A σ
    ∎
