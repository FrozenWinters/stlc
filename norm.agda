{-# OPTIONS --cubical --allow-unsolved-metas #-}

module norm where

open import syn
open import eliminator
open import contextual
open import ccc
open import presheaves
open import twgl
open import twglccc

open import Cubical.Data.Nat renaming (zero to Z; suc to S) hiding (elim)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Categories.Instances.Sets

open Syn
open Presheaves σιν (λ c → Base c)
open TwGlCC σιν (λ c → Base c)
open TwGlCCC σιν (λ c → Base c)
open Glueing
open GlTm
open Contextual TwGl

private
  module C = Contextual σιν
  module R = Contextual C.ρεν
  module I = Contextual ρεν

NEULem : {Γ Δ : Ctx} {X : Char} (M : Ne Δ (Base X)) (σ : Ren Γ Δ) →
  NEU (M [ σ ]NE) ≡ NEU M [ σ ]NF
NEULem (VN v) σ = refl
NEULem (APP M N) σ = refl

module _ where
  open NatTrans
  open Functor

  base : (X : Char) → Glueing
  Gl-A (base X) = Base X
  Gl-⦇A⦈ (base X) = NF (Base X)
  N-ob (Gl-u (base X)) Γ M = NEU M
  N-hom (Gl-u (base X)) σ i M = NEULem M σ i
  Gl-q (base X) = idTrans (NF (Base X))
  Gl-comp (base X) = makeNatTransPath (λ i Σ M → ιNe M)

open Eliminator TwGl ⦃ isCCCTwGl ⦄ base

interpTyLem : (A : Ty) → Gl-A (interpTy A) ≡ A
interpTyLem (Base X) = refl
interpTyLem (A ⇒ B) i = interpTyLem A i Syn.⇒ interpTyLem B i

interpCtxLem : (Γ : Ctx) → Gls-Γ (interpCtx Γ) ≡ Γ
interpCtxLem ∅ = refl
interpCtxLem (Γ ⊹ A) i = interpCtxLem Γ i ⊹ interpTyLem A i

private
  interpVarHelper : {Γ : Ctx} {A : Ty} (v : Var Γ A) →
    PathP (λ i → Var (interpCtxLem Γ i) (interpTyLem A i)) (tr𝑉𝑎𝑟 Gl-A (tr𝑉𝑎𝑟 interpTy v)) v
  interpVarHelper 𝑧𝑣 i = 𝑧𝑣
  interpVarHelper (𝑠𝑣 v) i = 𝑠𝑣 (interpVarHelper v i)

  interpVarLem₁ : {Γ : Ctx} {A : Ty} (v : Var Γ A) →
    PathP (λ i → Tm (interpCtxLem Γ i) (interpTyLem A i))
      (GlTm-α (makeTwGlVar (tr𝑉𝑎𝑟 interpTy v))) (V v)
  interpVarLem₁ {Γ} {A} v i =
    (derive {tm = Tm} (map𝑇𝑚𝑠 V (id𝑅𝑒𝑛 (interpCtxLem Γ i))) (interpVarHelper v i)
      ≡⟨ deriveMap {tm₂ = Tm} V (id𝑅𝑒𝑛 (interpCtxLem Γ i)) (interpVarHelper v i) ⟩
    V (derive (id𝑅𝑒𝑛 (interpCtxLem Γ i)) (interpVarHelper v i))
      ≡⟨ ap V (makeRenVar σιν (interpVarHelper v i)) ⟩
    V (interpVarHelper v i)
      ∎) i

  interpVarLem₂ : {Γ : Ctx} {A : Ty} (v : Var Γ A) →
    (GlTm-α (makeTwGlVar (tr𝑉𝑎𝑟 interpTy v))) ≡ GlTm-α (interpTm (V v))
  interpVarLem₂ {Γ} {A} v =
    GlTm-α (makeTwGlVar (tr𝑉𝑎𝑟 interpTy v))
      ≡⟨ ap (GlTm-α ∘ makeTwGlVar) (makeRenVar ρεν (tr𝑉𝑎𝑟 interpTy v) ⁻¹) ⟩
    GlTm-α (makeTwGlVar (I.makeVar (tr𝑉𝑎𝑟 interpTy v)))
      ≡⟨ ap GlTm-α (deriveMap makeTwGlVar (id𝑅𝑒𝑛 (map𝐶𝑡𝑥 interpTy Γ)) (tr𝑉𝑎𝑟 interpTy v) ⁻¹)  ⟩
    GlTm-α (derive {tm = GlTm} (map𝑇𝑚𝑠 makeTwGlVar (id𝑅𝑒𝑛 (map𝐶𝑡𝑥 interpTy Γ))) (tr𝑉𝑎𝑟 interpTy v))
      ∎

  interpVarLem : {Γ : Ctx} {A : Ty} (v : Var Γ A) →
    PathP (λ i → Tm (interpCtxLem Γ i) (interpTyLem A i)) (GlTm-α (interpTm (V v))) (V v)
  interpVarLem {Γ} {A} v =
    subst
      (λ t → PathP (λ i → Tm (interpCtxLem Γ i) (interpTyLem A i)) t (V v))
      (interpVarLem₂ v) (interpVarLem₁ v)   

interpTmLem : {Γ : Ctx} {A : Ty} (t : Tm Γ A) →
  PathP (λ i → Tm (interpCtxLem Γ i) (interpTyLem A i)) (GlTm-α (interpTm t)) t

{-# TERMINATING #-}
interpTmsLem : {Γ Δ : Ctx} (σ : Tms Γ Δ) →
  PathP (λ i → Tms (interpCtxLem Γ i) (interpCtxLem Δ i)) (GlTms-αs (interpTms σ)) σ
interpTmsLem ! i = !
interpTmsLem (σ ⊕ t) i = interpTmsLem σ i ⊕ interpTmLem t i

interpTmLem {Γ} {A} (V v) =
  interpVarLem v
interpTmLem (Lam t) i =
  Lam (interpTmLem t i)
interpTmLem (App t s) i =
  App (interpTmLem t i) (interpTmLem s i)
interpTmLem (t [ σ ]) i =
  interpTmLem t i [ interpTmsLem σ i ]
  
interpTmLem {Γ} (β t s i) =
  isSet→SquareP (λ i j → trunc)
    (interpTmLem (App (Lam t) s))
    (interpTmLem (t [ idTms Γ ⊕ s ]))
    (λ k → TwGlCC.GlTm.GlTm-α (interpTm (β t s k)))
    (β t s) i
interpTmLem (η t i) =
  isSet→SquareP (λ i j → trunc)
    (interpTmLem t)
    (interpTmLem (Lam (App (t [ varify R.π ]) (V 𝑧𝑣))))
    (λ k → GlTm-α (interpTm (η t k)))
    (η t) i
interpTmLem (𝑧𝑣[] σ t i) =
  isSet→SquareP (λ i j → trunc)
    (interpTmLem (V 𝑧𝑣 [ σ ⊕ t ]))
    (interpTmLem t)
    (λ k → GlTm-α (interpTm (𝑧𝑣[] σ t k)))
    (𝑧𝑣[] σ t) i
interpTmLem (𝑠𝑣[] v σ t i) =
  isSet→SquareP (λ i j → trunc)
    (interpTmLem (V (𝑠𝑣 v) [ σ ⊕ t ]))
    (interpTmLem (V v [ σ ]))
    (λ k → GlTm-α (interpTm (𝑠𝑣[] v σ t k)))
    (𝑠𝑣[] v σ t) i
interpTmLem {Γ} {A ⇒ B} (Lam[] t σ i) =
  isSet→SquareP (λ i j → trunc)
    (interpTmLem (Lam t [ σ ]))
    (interpTmLem (Lam (t [ W₂Tms A σ ])))
    (λ k → GlTm-α (interpTm (Lam[] t σ k)))
    (Lam[] t σ) i
interpTmLem (App[] t s σ i) =
  isSet→SquareP (λ i j → trunc)
    (interpTmLem (App t s [ σ ]))
    (interpTmLem (App (t [ σ ]) (s [ σ ])))
    (λ k → GlTm-α (interpTm (App[] t s σ k)))
    (App[] t s σ) i
interpTmLem ([][] t σ τ i) =
  isSet→SquareP (λ i j → trunc)
    (interpTmLem (t [ σ ] [ τ ]))
    (interpTmLem (t [ σ ∘Tms τ ]))
    (λ k → GlTm-α (interpTm ([][] t σ τ k)))
    ( [][] t σ τ) i
interpTmLem {Γ} {A} (trunc t s p q i j) =
  isSet→SquareP
    (λ i j →
      isOfHLevelPathP {A = λ k → Tm (interpCtxLem Γ k) (interpTyLem A k)} 2 trunc
        (GlTm-α (interpTm (trunc t s p q i j)))
        (trunc t s p q i j))
    (λ k → interpTmLem (p k))
    (λ k → interpTmLem (q k))
    (λ k → interpTmLem t)
    (λ k → interpTmLem s) i j

transportComp : ∀ {ℓ₁ ℓ₂} {A₁ A₂ : Type ℓ₁} {B₁ B₂ : Type ℓ₂}
  {p : A₁ ≡ A₂} {q : B₁ ≡ B₂} (f : ∀ i → p i → q i) (x : A₁) →
   transport q (f i0 x) ≡ f i1 (transport p x)
transportComp {p = p} {q} f x = {!!}

sem : {Γ : Ctx} {A : Ty} → Tm Γ A → GlTm (interpCtx Γ) (interpTy A)
sem = interpTm

normalise : {Γ : Ctx} {A : Ty} → Tm Γ A → Nf Γ A
normalise {Γ} {A} t =
  transport (λ i → Nf (interpCtxLem Γ i) (interpTyLem A i)) (GlTm-norm (sem t))

correctness : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → ιNf (normalise t) ≡ t
correctness {Γ} {A} t =
  ιNf (normalise t)
    ≡⟨ transportComp (λ i → ιNf {interpCtxLem Γ i} {interpTyLem A i}) (GlTm-norm (sem t)) ⁻¹ ⟩
  transport (λ i → Tm (interpCtxLem Γ i) (interpTyLem A i)) (ιNf (GlTm-norm (sem t)))
    ≡⟨ (λ i → transport (λ j → Tm (interpCtxLem Γ j) (interpTyLem A j))
      (GlTm-correctness (sem t) i)) ⟩
  transport (λ i → Tm (interpCtxLem Γ i) (interpTyLem A i)) (GlTm-α (sem t))
    ≡⟨ transport (PathP≡Path _ _ _) (interpTmLem t) ⟩
  t
    ∎
