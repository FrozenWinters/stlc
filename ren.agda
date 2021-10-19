{-# OPTIONS --cubical --allow-unsolved-metas #-}

module ren where

open import cartesian
open import syn2

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Data.Char renaming (_≟_ to _Id≟_)
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything renaming (cong to ap)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (zero to Z; suc to S)
open import Cubical.Data.Empty as ⊥ public
open import Cubical.Data.Unit as ⊤ renaming (Unit to ⊤)

infix 30 _[_]R
_[_]R : {Γ Δ : Ctx} {A : Ty} → Var Δ A → Ren Γ Δ → Var Γ A
Zv [ σ ⊕R v ]R = v
Sv v [ σ ⊕R w ]R = v [ σ ]R

infixl 30 _∘Ren_
_∘Ren_ : {Γ Δ Σ : Ctx} → Ren Δ Σ → Ren Γ Δ → Ren Γ Σ
!R ∘Ren τ = !R
(σ ⊕R v) ∘Ren τ = σ ∘Ren τ ⊕R v [ τ ]R

[][]Ren : {Γ Δ Σ : Ctx} {A : Ty} (v : Var Σ A) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  v [ σ ]R [ τ ]R ≡ v [ σ ∘Ren τ ]R
[][]Ren Zv (σ ⊕R v) τ = refl
[][]Ren (Sv v) (σ ⊕R w) τ = [][]Ren v σ τ

∘RenAssoc : {Γ Δ Σ Ω : Ctx} (σ : Ren Σ Ω) (τ : Ren Δ Σ) (μ : Ren Γ Δ) →
  σ ∘Ren τ ∘Ren μ ≡ σ ∘Ren (τ ∘Ren μ)
∘RenAssoc !R τ μ = refl
∘RenAssoc (σ ⊕R v) τ μ i = ∘RenAssoc σ τ μ i ⊕R [][]Ren v τ μ i

Vlem3 : {Γ Δ : Ctx} {A : Ty} (v : Var Δ A) (σ : Ren Γ Δ) →
  V (v [ σ ]R) ≡ (V v) [ varify σ ]
Vlem3 Zv (σ ⊕R w) = Zv[] (varify σ) (V w) ⁻¹
Vlem3 (Sv v) (σ ⊕R w) =
  V (v [ σ ]R)
    ≡⟨ Vlem3 v σ ⟩
  V v [ varify σ ]
    ≡⟨ Sv[] v (varify σ) (V w) ⁻¹ ⟩
  V (Sv v) [ varify σ ⊕ V w ]
    ∎

Vlem4 : {Γ Δ Σ : Ctx} (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  varify (σ ∘Ren τ) ≡ varify σ ∘Tms varify τ
Vlem4 !R τ = refl
Vlem4 (σ ⊕R t) τ i = Vlem4 σ τ i ⊕ Vlem3 t τ i 

Wlem1Ren : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Ren Γ Δ) (v : Var Γ A) →
  W₁Ren A σ ∘Ren (τ ⊕R v) ≡ σ ∘Ren τ
Wlem1Ren !R τ v = refl
Wlem1Ren (σ ⊕R w) τ v = ap (_⊕R w [ τ ]R) (Wlem1Ren σ τ v)

∘RenIdL : {Γ Δ : Ctx} (σ : Ren Γ Δ) → idRen Δ ∘Ren σ ≡ σ
∘RenIdL !R = refl
∘RenIdL {Γ} {Δ ⊹ A} (σ ⊕R v) =
  W₁Ren A (idRen Δ) ∘Ren (σ ⊕R v) ⊕R v
    ≡⟨ ap (_⊕R v) (Wlem1Ren (idRen Δ) σ v) ⟩
  idRen Δ ∘Ren σ ⊕R v
    ≡⟨ ap (_⊕R v) (∘RenIdL σ) ⟩
  σ ⊕R v
    ∎

Wlem2Ren : {Γ Δ : Ctx} {A B : Ty} (v : Var Δ A) (σ : Ren Γ Δ) →
  v [ W₁Ren B σ ]R ≡ Sv (v [ σ ]R)
Wlem2Ren Zv (σ ⊕R v) = refl
Wlem2Ren (Sv v) (σ ⊕R w) = Wlem2Ren v σ

Wlem3Ren : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  σ ∘Ren W₁Ren A τ ≡ W₁Ren A (σ ∘Ren τ)
Wlem3Ren !R τ = refl
Wlem3Ren (σ ⊕R v) τ i = Wlem3Ren σ τ i ⊕R Wlem2Ren v τ i

Wlem4Ren : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  W₂Ren A σ ∘Ren W₂Ren A τ ≡ W₂Ren A (σ ∘Ren τ)
Wlem4Ren !R τ = refl
Wlem4Ren {A = A} (σ ⊕R v) τ =
  W₁Ren A σ ∘Ren (W₁Ren A τ ⊕R Zv) ⊕R v [ W₁Ren A τ ]R ⊕R Zv
    ≡⟨ (λ i → Wlem1Ren σ (W₁Ren A τ) Zv i ⊕R Wlem2Ren v τ i ⊕R Zv) ⟩
  σ ∘Ren W₁Ren A τ ⊕R Sv (v [ τ ]R) ⊕R Zv
    ≡⟨ (λ i → Wlem3Ren σ τ i ⊕R Sv (v [ τ ]R) ⊕R Zv) ⟩
  W₂Ren A (σ ∘Ren τ ⊕R v [ τ ]R)
    ∎

Wlem5Ren : {Γ Δ Σ : Ctx} {A : Ty} (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  W₁Ren A σ ∘Ren W₂Ren A τ ≡ W₁Ren A (σ ∘Ren τ)
Wlem5Ren !R τ = refl
Wlem5Ren (σ ⊕R v) τ i = Wlem5Ren σ τ i ⊕R Wlem2Ren v τ i



[id]Ren : {Γ : Ctx} {A : Ty} (v : Var Γ A) →
  v [ idRen Γ ]R ≡ v
[id]Ren Zv = refl
[id]Ren {Γ ⊹ B} {A} (Sv v) =
  v [ W₁Ren B (idRen Γ) ]R
    ≡⟨ Wlem2Ren v (idRen Γ) ⟩
  Sv (v [ idRen Γ ]R)
    ≡⟨ ap Sv ([id]Ren v) ⟩
  Sv v
    ∎

∘RenIdR : {Γ Δ : Ctx} (σ : Ren Γ Δ) → σ ∘Ren idRen Γ ≡ σ
∘RenIdR !R = refl
∘RenIdR (σ ⊕R v) i = ∘RenIdR σ i ⊕R [id]Ren v i

isSetRen : {Γ Δ : Ctx} → isSet (Ren Γ Δ)
isSetRen = {!!}

{-
infix 30 _[_]Tm _[_]Tms
_[_]Tm : {Γ Δ : Ctx} {A : Ty} → Tm Δ A → Ren Γ Δ → Tm Γ A

{-# TERMINATING #-}
_[_]Tms : {Γ Δ Σ : Ctx} → Tms Δ Σ → Ren Γ Δ → Tms Γ Σ
! [ σ ]Tms = !
(τ ⊕ t) [ σ ]Tms = τ [ σ ]Tms ⊕ (t [ σ ]Tm)

Wlem0 : {Γ Δ : Ctx} {A B : Ty} (t : Tm Δ B) (σ : Ren Γ Δ) →
  W₁ A (t [ σ ]Tm) ≡ t [ W₁Ren A σ ]Tm
Wlem1 : {Γ Δ  Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Ren Γ Δ) →
  W₁Tms A (σ [ τ ]Tms) ≡ σ [ W₁Ren A τ ]Tms
Wlem2 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Ren Γ Δ) (v : Var Γ A) →
  W₁Tms A σ [ τ ⊕R v ]Tms ≡ σ [ τ ]Tms
Wlem3 : {Γ Δ Σ : Ctx} {A : Ty} (σ : Tms Δ Σ) (τ : Ren Γ Δ) →
  W₁Tms A σ [ W₂Ren A τ ]Tms ≡ σ [ W₁Ren A τ ]Tms

V v [ σ ]Tm = V (v [ σ ]R)
Lam {A = A} t [ σ ]Tm = Lam (t [ W₂Ren A σ ]Tm)
App t s [ σ ]Tm = App (t [ σ ]Tm) (s [ σ ]Tm)
(t [ τ ]) [ σ ]Tm = t [ τ [ σ ]Tms ]
W₁ A t [ σ ⊕R v ]Tm = t [ σ ]Tm
β {A = A} t s i [ σ ]Tm = {!β (t [ W₂Ren A σ ]Tm) (s [ σ ]Tm)!}
η t i [ σ ]Tm = {!η (t [ σ ]Tm)!}
Zv[] τ t i [ σ ]Tm = Zv[] (τ [ σ ]Tms) (t [ σ ]Tm) i
Sv[] v τ t i [ σ ]Tm = Sv[] v (τ [ σ ]Tms) (t [ σ ]Tm) i
Lam[] {Γ} {Δ} {A} {B} t τ i [ σ ]Tm =
  (Lam t [ τ [ σ ]Tms ]
    ≡⟨ Lam[] t (τ [ σ ]Tms) ⟩
  Lam (t [ W₁Tms A (τ [ σ ]Tms) ⊕ V Zv ])
    ≡⟨ (λ i → Lam (t [ Wlem1 τ σ i ⊕ V Zv ])) ⟩
  Lam (t [ τ [ W₁Ren A σ ]Tms ⊕ V Zv ])
    ≡⟨ (λ i → Lam (t [ Wlem3 τ σ (~ i) ⊕ V Zv ])) ⟩
  Lam (t [ W₁Tms A τ [ W₂Ren A σ ]Tms ⊕ V Zv ])
    ∎) i
App[] t s σ₁ i [ σ ]Tm = {!!}
W₁V v i [ σ ⊕R w ]Tm = V (v [ σ ]R)
W₁Lam t i [ σ ⊕R v ]Tm = {!!}
W₁App t s i [ σ ⊕R v ]Tm = App (t [ σ ]Tm) (s [ σ ]Tm)
W₁[] t τ i [ σ ]Tm = {!!}
isSetTm t s x y i i₁ [ σ ]Tm = {!!}

Wlem0 (V x) σ = {!!}
Wlem0 {A = A} (Lam {Γ} {B} {C} t) σ =
  {!W₁Lam (t [ W₂Ren B σ ]Tm)!}
Wlem0 {A = A} (App t s) σ =
  W₁ A (App (t [ σ ]Tm) (s [ σ ]Tm))
    ≡⟨ W₁App (t [ σ ]Tm) (s [ σ ]Tm) ⟩
  App (W₁ A (t [ σ ]Tm)) (W₁ A (s [ σ ]Tm))
    ≡⟨ (λ i → App (Wlem0 t σ i) (Wlem0 s σ i)) ⟩
  App (t [ W₁Ren A σ ]Tm) (s [ W₁Ren A σ ]Tm)
    ∎
Wlem0 {A = A} (t [ τ ]) σ =
  W₁ A (t [ τ [ σ ]Tms ])
    ≡⟨ W₁[] t (τ [ σ ]Tms) ⟩
  t [ W₁Tms A (τ [ σ ]Tms) ]
    ≡⟨ ap (t [_]) (Wlem1 τ σ) ⟩
  t [ τ [ W₁Ren A σ ]Tms ]
    ∎
Wlem0 (W₁ A t) (σ ⊕R v) = Wlem0 t σ
Wlem0 (β t t₁ i) σ = {!!}
Wlem0 (η t i) σ = {!!}
Wlem0 (Zv[] σ₁ t i) σ = {!!}
Wlem0 (Sv[] v σ₁ t i) σ = {!!}
Wlem0 (Lam[] t σ₁ i) σ = {!!}
Wlem0 (App[] t t₁ σ₁ i) σ = {!!}
Wlem0 (W₁V v i) σ = {!!}
Wlem0 (W₁Lam t i) σ = {!!}
Wlem0 (W₁App t t₁ i) σ = {!!}
Wlem0 (W₁[] t τ i) σ = {!!}
Wlem0 (isSetTm t t₁ x y i i₁) σ = {!!}

Wlem1 ! τ = refl
Wlem1 (σ ⊕ t) τ i = Wlem1 σ τ i ⊕ Wlem0 t τ i

Wlem2 ! τ v = refl
Wlem2 (σ ⊕ t) τ v = ap (_⊕ t [ τ ]Tm ) (Wlem2 σ τ v)

Wlem3 ! τ = refl
Wlem3 {A = A} (σ ⊕ t) τ = ap (_⊕ t [ W₁Ren A τ ]Tm) (Wlem3 σ τ)
-}

module _ where
  open Precategory renaming (id to 𝒾𝒹)
  open Functor

  REN : Precategory lzero lzero
  REN .ob = Ctx
  REN .Hom[_,_] = Ren
  REN .𝒾𝒹 Γ = idRen Γ
  REN ._⋆_ σ τ = τ ∘Ren σ
  REN .⋆IdL = ∘RenIdR
  REN .⋆IdR = ∘RenIdL
  REN .⋆Assoc σ τ μ = ∘RenAssoc μ τ σ ⁻¹

  instance
    isCatREN : isCategory REN
    isCatREN .isSetHom = isSetRen

  TM : (A : Ty) → ob (PSh REN)
  TM A .F-ob Δ = Tm Δ A , isSetTm
  TM A .F-hom σ t = t [ varify σ ]
  TM A .F-id i σ = [id] σ i
  TM A .F-seq σ τ i t =
    (t [ varify (σ ∘Ren τ) ]
      ≡⟨ ap (t [_]) (Vlem4 σ τ) ⟩
    t [ varify σ ∘Tms varify τ ]
      ≡⟨ [][] t (varify σ) (varify τ) ⁻¹ ⟩
    t [ varify σ ] [ varify τ ]
      ∎) i

  TMS : (Γ : Ctx) → ob (PSh REN)
  TMS Γ .F-ob Δ = Tms Δ Γ , isSetTms
  TMS Γ .F-hom σ τ = τ ∘Tms varify σ 
  TMS Γ .F-id i σ = ∘IdR σ i
  TMS Γ .F-seq σ τ i μ =
    (μ ∘Tms varify (σ ∘Ren τ)
      ≡⟨ ap (μ ∘Tms_) (Vlem4 σ τ) ⟩
    μ ∘Tms (varify σ ∘Tms varify τ)
      ≡⟨ ∘Assoc μ (varify σ) (varify τ) ⁻¹ ⟩
    μ ∘Tms varify σ ∘Tms varify τ
      ∎) i

data Nf : (Γ : Ctx) (A : Ty) → Set

data Ne : (Γ : Ctx) (A : Ty) → Set where
  VN : {Γ : Ctx} {A : Ty} → Var Γ A → Ne Γ A
  APP : {Γ : Ctx} {A B : Ty} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

data Nf where
  NEU : {Γ : Ctx} {c : Char} → Ne Γ (Base c) → Nf Γ (Base c)
  LAM : {Γ : Ctx} {A B : Ty} → Nf (Γ ⊹ A) B → Nf Γ (A ⇒ B)

insertCtx : (Γ : Ctx) (A : Ty) (n : ℕ) → Ctx
insertCtx Γ A Z = Γ ⊹ A
insertCtx ∅ A (S n) = ∅ ⊹ A
insertCtx (Γ ⊹ B) A (S n) = insertCtx Γ A n ⊹ B

SVar : {Γ : Ctx} {A B : Ty} (n : ℕ) → Var Γ A → Var (insertCtx Γ B n) A
SNe : {Γ : Ctx} {A B : Ty} (n : ℕ) → Ne Γ A → Ne (insertCtx Γ B n) A
SNf : {Γ : Ctx} {A B : Ty} (n : ℕ) → Nf Γ A → Nf (insertCtx Γ B n) A

SVar Z v = Sv v
SVar (S n) Zv = Zv
SVar (S n) (Sv v) = Sv (SVar n v)

SNe n (VN v) = VN (SVar n v)
SNe n (APP M N) = APP (SNe n M) (SNf n N)

SNf n (NEU M) = NEU (SNe n M)
SNf n (LAM N) = LAM (SNf (S n) N)

infix 30 _[_]NE _[_]NF
_[_]NE : {Γ Δ : Ctx} {A : Ty} → Ne Δ A → Ren Γ Δ → Ne Γ A
_[_]NF : {Γ Δ : Ctx} {A : Ty} → Nf Δ A → Ren Γ Δ → Nf Γ A

APP M N [ σ ]NE = APP (M [ σ ]NE) (N [ σ ]NF)
VN v [ σ ]NE = VN (v [ σ ]R)

NEU M [ σ ]NF = NEU (M [ σ ]NE)
LAM {A = A} N [ σ ]NF = LAM (N [ W₂Ren A σ ]NF)

[id]NE : {Γ : Ctx} {A : Ty} → (M : Ne Γ A) →
  M [ idRen Γ ]NE ≡ M
[id]NF : {Γ : Ctx} {A : Ty} → (N : Nf Γ A) →
  N [ idRen Γ ]NF ≡ N

[id]NE (VN Zv) = refl
[id]NE (VN (Sv v)) =
  VN (v [ W₁Ren _ (idRen _) ]R)
    ≡⟨ ap VN (Wlem2Ren v (idRen _)) ⟩
  VN (Sv (v [ idRen _ ]R))
    ≡⟨ ap VN (ap Sv ([id]Ren v)) ⟩
  VN (Sv v)
    ∎
[id]NE (APP M N) i = APP ([id]NE M i) ([id]NF N i)

[id]NF (NEU M) = ap NEU ([id]NE M)
[id]NF (LAM N) = ap LAM ([id]NF N)

[][]NE : {Γ Δ Σ : Ctx} {A : Ty} (M : Ne Σ A) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  M [ σ ]NE [ τ ]NE ≡ M [ σ ∘Ren τ ]NE
[][]NF : {Γ Δ Σ : Ctx} {A : Ty} (N : Nf Σ A) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  N [ σ ]NF [ τ ]NF ≡ N [ σ ∘Ren τ ]NF

[][]NE (VN v) σ τ = ap VN ([][]Ren v σ τ)
[][]NE (APP M N) σ τ i = APP ([][]NE M σ τ i) ([][]NF N σ τ i)

[][]NF (NEU M) σ τ = ap NEU ([][]NE M σ τ)
[][]NF (LAM N) σ τ =
  LAM (N [ W₂Ren _ σ ]NF [ W₂Ren _ τ ]NF)
    ≡⟨ ap LAM ([][]NF N (W₂Ren _ σ) (W₂Ren _ τ) ) ⟩
  LAM (N [ W₂Ren _ σ ∘Ren W₂Ren _ τ ]NF)
    ≡⟨ (λ i → LAM (N [ Wlem4Ren σ τ i ]NF)) ⟩
  LAM (N [ W₂Ren _ (σ ∘Ren τ) ]NF)
    ∎

isSetNeutral : {Γ : Ctx} {A : Ty} → isSet (Ne Γ A)
isSetNeutral = {!!}

isSetNormal : {Γ : Ctx} {A : Ty} → isSet (Nf Γ A)
isSetNormal = {!!}


-- Now extending everything to lists of neutrals/normals

data Nes : (Γ Δ : Ctx) → Set where
  !NE : {Γ : Ctx} → Nes Γ ∅
  _⊕NE_ : {Γ Δ : Ctx} {A : Ty} (σ : Nes Γ Δ) (t : Ne Γ A) → Nes Γ (Δ ⊹ A)

data Nfs : (Γ Δ : Ctx) → Set where
  !NF : {Γ : Ctx} → Nfs Γ ∅
  _⊕NF_ : {Γ Δ : Ctx} {A : Ty} (σ : Nfs Γ Δ) (t : Nf Γ A) → Nfs Γ (Δ ⊹ A)

infix 30 _[_]NEs
_[_]NEs : {Γ Δ Σ : Ctx} → Nes Δ Σ → Ren Γ Δ → Nes Γ Σ
!NE [ σ ]NEs = !NE
(MS ⊕NE M) [ σ ]NEs = MS [ σ ]NEs ⊕NE M [ σ ]NE

infix 30 _[_]NFs
_[_]NFs : {Γ Δ Σ : Ctx} → Nfs Δ Σ → Ren Γ Δ → Nfs Γ Σ
!NF [ σ ]NFs = !NF
(NS ⊕NF N) [ σ ]NFs = NS [ σ ]NFs ⊕NF N [ σ ]NF

[id]NEs : {Γ Δ : Ctx} (MS : Nes Γ Δ) →
  MS [ idRen Γ ]NEs ≡ MS
[id]NEs !NE = refl
[id]NEs (MS ⊕NE M) i = [id]NEs MS i ⊕NE [id]NE M i

[id]NFs : {Γ Δ : Ctx} (NS : Nfs Γ Δ) →
  NS [ idRen Γ ]NFs ≡ NS
[id]NFs !NF = refl
[id]NFs (NS ⊕NF N) i = [id]NFs NS i ⊕NF [id]NF N i

[][]NEs : {Γ Δ Σ Ω : Ctx} (MS : Nes Σ Ω) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  MS [ σ ]NEs [ τ ]NEs ≡ MS [ σ ∘Ren τ ]NEs
[][]NEs !NE σ τ = refl
[][]NEs (MS ⊕NE M) σ τ i = [][]NEs MS σ τ i ⊕NE [][]NE M σ τ i

[][]NFs : {Γ Δ Σ Ω : Ctx} (NS : Nfs Σ Ω) (σ : Ren Δ Σ) (τ : Ren Γ Δ) →
  NS [ σ ]NFs [ τ ]NFs ≡ NS [ σ ∘Ren τ ]NFs
[][]NFs !NF σ τ = refl
[][]NFs (NS ⊕NF N) σ τ i = [][]NFs NS σ τ i ⊕NF [][]NF N σ τ i

isSetNeutrals : {Γ Δ : Ctx} → isSet (Nes Γ Δ)
isSetNeutrals = {!!}

isSetNormals : {Γ Δ : Ctx} → isSet (Nfs Γ Δ)
isSetNormals = {!!}

module _ where
  open Precategory
  open Functor

  NE : Ty → ob (PSh REN)
  NE A .F-ob Δ = Ne Δ A , isSetNeutral
  NE A .F-hom σ M = M [ σ ]NE
  NE A .F-id i M = [id]NE M i
  NE A .F-seq σ τ i M = [][]NE M σ τ (~ i) 

  NF : Ty → ob (PSh REN)
  NF A .F-ob Δ = Nf Δ A , isSetNormal
  NF A .F-hom σ N = N [ σ ]NF
  NF A .F-id i N = [id]NF N i
  NF A .F-seq σ τ i N = [][]NF N σ τ (~ i)

  NES : (Γ : Ctx) → ob (PSh REN)
  NES Γ .F-ob Δ = Nes Δ Γ , isSetNeutrals
  NES Γ .F-hom σ MS = MS [ σ ]NEs
  NES Γ .F-id i MS = [id]NEs MS i
  NES Γ .F-seq σ τ i MS = [][]NEs MS σ τ (~ i)

  NFS : (Γ : Ctx) → ob (PSh REN)
  NFS Γ .F-ob Δ = Nfs Δ Γ , isSetNormals
  NFS Γ .F-hom σ NS = NS [ σ ]NFs
  NFS Γ .F-id i NS = [id]NFs NS i
  NFS Γ .F-seq σ τ i NS = [][]NFs NS σ τ (~ i)

varifyNe : {Γ Δ : Ctx} → Ren Γ Δ → Nes Γ Δ
varifyNe !R = !NE
varifyNe (σ ⊕R v) = varifyNe σ ⊕NE VN v

idNeu : (Γ : Ctx) → Nes Γ Γ
idNeu Γ = varifyNe (idRen Γ)

embedNeutral : {Γ : Ctx} {A : Ty} → Ne Γ A → Nf Γ A
embedNeutral {A = Base c} M = NEU M
embedNeutral {A = A ⇒ B} M = LAM (embedNeutral (APP (SNe Z M) (embedNeutral (VN Zv))))

includeNeutral : {Γ : Ctx} {A : Ty} → Ne Γ A → Tm Γ A
includeNormal : {Γ : Ctx} {A : Ty} → Nf Γ A → Tm Γ A

includeNeutral (VN v) = V v
includeNeutral (APP M N) = App (includeNeutral M) (includeNormal N)

includeNormal (NEU M) = includeNeutral M
includeNormal (LAM N) = Lam (includeNormal N)

includeNeutrals : {Γ Δ : Ctx} → Nes Γ Δ → Tms Γ Δ
includeNeutrals !NE = !
includeNeutrals (MS ⊕NE M) = includeNeutrals MS ⊕ includeNeutral M

includeNormals : {Γ Δ : Ctx} → Nfs Γ Δ → Tms Γ Δ
includeNormals !NF = !
includeNormals (NS ⊕NF N) = includeNormals NS ⊕ includeNormal N

{-
module _ where
  open Precategory
  open Functor

  ιNE : Functor 
-}
