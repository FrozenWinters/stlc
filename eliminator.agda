{-# OPTIONS --cubical #-}

module eliminator where

open import contextual
open import ccc
open import syn

open import Agda.Builtin.Char
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

-- We construct a canonical contextual functor from σιν to any CCC 𝒞

module Eliminator {ℓ₁ ℓ₂} (𝒞 : Contextual ℓ₁ ℓ₂) ⦃ CCC𝒞 : CCC 𝒞 ⦄
                  (base : (c : Char) → Contextual.ty 𝒞) where
  open Contextual 𝒞
  private
    module S = Contextual σιν
  open CCC CCC𝒞
  open Syn

  interpTy : Ty → ty
  interpTy (Base X) = base X
  interpTy (A ⇒ B) = (interpTy A) ⇛ (interpTy B)

  interpCtx : Ctx → ctx
  interpCtx Γ = map𝐶𝑡𝑥 interpTy Γ

  trVar = tr𝑉𝑎𝑟 interpTy

  interpVar : {Γ : Ctx} {A : Ty} (v : Var Γ A) → tm (interpCtx Γ) (interpTy A)
  interpVar v = makeVar (tr𝑉𝑎𝑟 interpTy v)

  interpRen : {Γ Δ : Ctx} (σ : Ren Γ Δ) → tms (interpCtx Γ) (interpCtx Δ)
  interpRen = map𝑇𝑚𝑠₁ interpVar

  interpIdRen : {Γ : Ctx} → interpRen (id𝑅𝑒𝑛 Γ) ≡ 𝒾𝒹 (interpCtx Γ)
  interpIdRen {Γ} =
    map𝑇𝑚𝑠₁ (λ v → makeVar (tr𝑉𝑎𝑟 interpTy v)) (id𝑅𝑒𝑛 Γ)
      ≡⟨ map𝑇𝑚𝑠comp₂ makeVar (tr𝑉𝑎𝑟 interpTy) (id𝑅𝑒𝑛 Γ) ⁻¹ ⟩
    makeRen (tr𝑅𝑒𝑛 interpTy (id𝑅𝑒𝑛 Γ))
      ≡⟨ (λ i → makeRen (trId interpTy Γ i)) ⟩
    makeRen (id𝑅𝑒𝑛 (map𝐶𝑡𝑥 interpTy Γ))
      ≡⟨ 𝒾𝒹η₂ ⟩
    𝒾𝒹 (map𝐶𝑡𝑥 interpTy Γ)
      ∎

  interpW₁Ren : {Γ Δ : Ctx} {A : Ty} (σ : Ren Γ Δ) →
    interpRen (W₁𝑅𝑒𝑛 A σ) ≡ interpRen σ ⊚ π
  interpW₁Ren ! = refl
  interpW₁Ren {Γ} {Δ} {A} (σ ⊕ v) i = interpW₁Ren {A = A} σ i ⊕ make𝑠𝑣 (tr𝑉𝑎𝑟 interpTy v) i

  πlem : {Γ : Ctx} {A : Ty} → interpRen (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) ≡ π
  πlem {Γ} {A} =
    interpRen (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ))
      ≡⟨ interpW₁Ren (id𝑅𝑒𝑛 Γ) ⟩
    interpRen (id𝑅𝑒𝑛 Γ) ⊚ π
      ≡⟨ ap (_⊚ π) interpIdRen ⟩
    𝒾𝒹 (interpCtx Γ) ⊚ π
      ≡⟨ 𝒾𝒹L π ⟩
    π
      ∎

  interpTm  : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → tm (interpCtx Γ) (interpTy A)

  {-# TERMINATING #-}
  interpTms : {Γ Δ : Ctx} (σ : Tms Γ Δ) → tms  (interpCtx Γ)  (interpCtx Δ)
  interpTms = map𝑇𝑚𝑠₁ interpTm

  interpVarify : {Γ Δ : Ctx} (σ : Ren Γ Δ) →
    interpTms (varify σ) ≡ interpRen σ

  interpId : {Γ : Ctx} → interpTms (idTms Γ) ≡ 𝒾𝒹 (interpCtx Γ)
  interpId {Γ} =
   interpTms (varify (id𝑅𝑒𝑛 Γ))
     ≡⟨ interpVarify (id𝑅𝑒𝑛 Γ) ⟩
   interpRen (id𝑅𝑒𝑛 Γ)
     ≡⟨ interpIdRen ⟩
   𝒾𝒹 (interpCtx Γ)
     ∎

  πlemTms : {Γ : Ctx} {A : Ty} → interpTms (S.π {Γ} {A}) ≡ π
  πlemTms {Γ} {A} =
    interpTms (S.π {Γ} {A})
      ≡⟨ interpVarify (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ)) ⟩
    interpRen (W₁𝑅𝑒𝑛 A (id𝑅𝑒𝑛 Γ))
      ≡⟨ πlem ⟩
    π
      ∎

  interp∘Tms : {Γ Δ Σ : Ctx} (σ : Tms Δ Σ) (τ : Tms Γ Δ) →
    interpTms (σ ∘Tms τ) ≡ interpTms σ ⊚ interpTms τ

  interpW₁Tm : {Γ : Ctx} (A : Ty) {B : Ty} (t : Tm Γ B) →
    interpTm (W₁Tm A t) ≡ interpTm t ⟦ π ⟧

  interpW₁Tms : {Γ Δ : Ctx} (A : Ty) (σ : Tms Γ Δ) →
    interpTms (W₁Tms A σ) ≡ interpTms σ ⊚ π
  interpW₁Tms A ! = !η (! ⊚ π)
  interpW₁Tms A (σ ⊕ t) =
    interpTms (W₁Tms A σ) ⊕ interpTm (W₁Tm A t)
      ≡⟨ (λ i → interpW₁Tms A σ i ⊕ interpW₁Tm A t i) ⟩
    (interpTms σ ⊚ π) ⊕ (interpTm t ⟦ π ⟧)
      ≡⟨ ⊕⊚ (interpTms σ) (interpTm t) π ⁻¹ ⟩
    interpTms σ ⊕ interpTm t ⊚ π
      ∎

  interpTm (V v) =
    interpVar v
  interpTm (Lam t) =
    Λ (interpTm t)
  interpTm (App t s) =
    𝑎𝑝𝑝 (interpTm t) (interpTm s)
  interpTm (t [ σ ]) =
    interpTm t ⟦ interpTms σ ⟧

  interpTm (β {Γ} t s i) =
    (𝑎𝑝𝑝 (Λ (interpTm t)) (interpTm s)
      ≡⟨ 𝑎𝑝𝑝β (interpTm t) (interpTm s) ⟩
    interpTm t ⟦ 𝒾𝒹 (interpCtx Γ) ⊕ interpTm s ⟧
      ≡⟨ (λ j → interpTm t ⟦ interpId (~ j) ⊕ interpTm s ⟧) ⟩
    interpTm t ⟦ interpTms (idTms Γ) ⊕ interpTm s ⟧
      ∎) i
  interpTm (η {Γ} {A} t i) =
    (interpTm t
      ≡⟨ 𝑎𝑝𝑝η (interpTm t) ⟩
    Λ (𝑎𝑝𝑝 (interpTm t ⟦ π ⟧) 𝑧)
      ≡⟨ (λ i → Λ (𝑎𝑝𝑝 (interpTm t ⟦ πlemTms {Γ} {A} (~ i) ⟧) 𝑧)) ⟩
    Λ (𝑎𝑝𝑝 (interpTm (t [ S.π ])) 𝑧)
      ∎) i
  interpTm (𝑧𝑣[] σ t i) =
    𝑧β (interpTms (σ ⊕ t)) i
  interpTm (𝑠𝑣[] v σ t i) =
    W₁⟦⟧ (tr𝑉𝑎𝑟 interpTy v) (interpTms σ) (interpTm t) i
  interpTm (Lam[] {A = A} t σ i) =
    (Λ (interpTm t) ⟦ interpTms σ ⟧
      ≡⟨ Λnat (interpTm t) (interpTms σ) ⟩
    Λ (interpTm t ⟦ interpTms σ ⊚ π ⊕ 𝑧 ⟧)
      ≡⟨ (λ j → Λ (interpTm t ⟦ interpW₁Tms A σ (~ j) ⊕ 𝑧 ⟧)) ⟩
    Λ (interpTm t ⟦ interpTms (W₁Tms A σ) ⊕ 𝑧 ⟧)
      ∎) i
  interpTm (App[] t s σ i) =
    𝑎𝑝𝑝⟦⟧ (interpTm t) (interpTm s) (interpTms σ) i
  interpTm ([][] t σ τ i) =
    (interpTm t ⟦ interpTms σ ⟧ ⟦ interpTms τ ⟧
      ≡⟨ ⟦⟧⟦⟧ (interpTm t) (interpTms σ) (interpTms τ) ⟩
    interpTm t ⟦ interpTms σ ⊚ interpTms τ ⟧
      ≡⟨ ap (interpTm t ⟦_⟧) (interp∘Tms σ τ ⁻¹) ⟩
    interpTm t ⟦ interpTms (σ ∘Tms τ) ⟧
      ∎) i
  interpTm (trunc t s p q i j) =
    isSet→SquareP (λ i j → isSetTm)
      (λ k → interpTm (p k))
      (λ k → interpTm (q k))
      (λ k → interpTm t)
      (λ k → interpTm s) i j

  interpVarify ! = refl
  interpVarify (σ ⊕ v) = ap (_⊕ interpVar v) (interpVarify σ)

  interpW₁Tm {Γ} A t = ap (interpTm t ⟦_⟧) πlemTms

  interp∘Tms ! τ = !η (! ⊚ interpTms τ)
  interp∘Tms (σ ⊕ t) τ = ap (_⊕ interpTm (t [ τ ])) (interp∘Tms σ τ)

  open ContextualFunctor

  elim : ContextualFunctor σιν 𝒞
  CF-ty elim = interpTy
  CF-tm elim = interpTm
  CF-id elim = interpId
  CF-sub elim t σ = refl

  open CCCPreserving

  CCCPres : CCCPreserving elim
  pres-⇛ CCCPres A B = refl
  pres-𝐴𝑝𝑝 CCCPres {Γ} {A} {B} t i =
    𝑎𝑝𝑝 (transportRefl (interpTm t) (~ i) ⟦ πlemTms {Γ} {A} i ⟧) 𝑧

  BasePreserving : ContextualFunctor σιν 𝒞 → Type ℓ₁
  BasePreserving F = (c : Char) → CF-ty F (Base c) ≡ base c

  BasePres : BasePreserving elim
  BasePres c = refl

  module UP {F : ContextualFunctor σιν 𝒞} (p₁ : CCCPreserving F) (p₂ : BasePreserving F) where
    UP-ty' : (A : Ty) → CF-ty F A ≡ CF-ty elim A
    UP-ty' (Base c) = p₂ c
    UP-ty' (A ⇒ B) = pres-⇛ p₁ A B ∙ (λ i → UP-ty' A i ⇛ UP-ty' B i)

    UP-ty : CF-ty F ≡ CF-ty elim
    UP-ty = funExt UP-ty'

    UP-ctx : CF-ctx F ≡ CF-ctx elim
    UP-ctx i = map𝐶𝑡𝑥 (UP-ty i)    

    {-# TERMINATING #-}
    UP-tm' : {Γ : Ctx} {A : Ty} (t : Tm Γ A) →
      PathP (λ i → tm (UP-ctx i Γ) (UP-ty i A)) (CF-tm F t) (CF-tm elim t)
    UP-sub' : {Γ Δ : Ctx} (σ : Tms Γ Δ) →
      PathP (λ i → tms (UP-ctx i Γ) (UP-ctx i Δ)) (CF-tms F σ) (CF-tms elim σ)

    UP-sub' ! i = !
    UP-sub' (σ ⊕ t) i = UP-sub' σ i ⊕ UP-tm' t i

    transp𝑎𝑝𝑝 : {P : Ty → ty} (a : CF-ty F ≡ P) →
      {Γ : Ctx} {A B : Ty} (t : Tm Γ (A ⇒ B)) (s : Tm Γ A) →
      transport (λ i → tm (map𝐶𝑡𝑥 (a i) Γ) (a i B)) (CF-tm F (App t s))
        ≡ 𝑎𝑝𝑝
          ((transport (λ i → tm (map𝐶𝑡𝑥 (a i) Γ)
            ((pres-⇛ p₁ A B ∙ (λ j → a j A ⇛ a j B)) i)) (CF-tm F t)))
          (transport (λ i → tm (map𝐶𝑡𝑥 (a i) Γ) (a i A)) (CF-tm F s))
    transp𝑎𝑝𝑝 a {Γ} {A} {B} t s =
      J
        (λ P b →
          transport (λ i → tm (map𝐶𝑡𝑥 (b i) Γ) (b i B)) (CF-tm F (App t s))
          ≡ 𝑎𝑝𝑝
            ((transport (λ i → tm (map𝐶𝑡𝑥 (b i) Γ)
              ((pres-⇛ p₁ A B ∙ (λ j → b j A ⇛ b j B)) i)) (CF-tm F t)))
            (transport (λ i → tm (map𝐶𝑡𝑥 (b i) Γ) (b i A)) (CF-tm F s)))
        (transport (λ i → tm (map𝐶𝑡𝑥 (refl i) Γ) (refl {x = CF-ty F} i B)) (CF-tm F (App t s))
          ≡⟨ transportRefl (CF-tm F (App t s)) ⟩
        CF-tm F (App t s)
          ≡⟨ pres-𝑎𝑝𝑝 p₁ t s ⟩
        𝑎𝑝𝑝 (transport (λ i → tm (CF-ctx F Γ) (pres-⇛ p₁ A B i)) (CF-tm F t)) (CF-tm F s)
          ≡⟨ (λ j → 𝑎𝑝𝑝
            (transport (λ i → tm (CF-ctx F Γ) (rUnit (pres-⇛ p₁ A B) j i)) (CF-tm F t))
            (transportRefl (CF-tm F s) (~ j))) ⟩
        𝑎𝑝𝑝 (transport (λ i → tm (CF-ctx F Γ) ((pres-⇛ p₁ A B ∙ refl) i)) (CF-tm F t))
          (transport refl (CF-tm F s))
          ∎)
        a

    UP-tm' {Γ} {A} (V v) =
      (CF-tm F (V v)
        ≡⟨ (λ i → CF-tm F (V (makeRenVar σιν v (~ i)))) ⟩
      CF-tm F (V (derive (id𝑅𝑒𝑛 Γ) v))
        ≡⟨ ap (CF-tm F) (deriveMap V (id𝑅𝑒𝑛 Γ) v ⁻¹) ⟩
      CF-tm F (S.makeVar v)
        ≡⟨ CF-Var F v ⟩
      makeVar (tr𝑉𝑎𝑟 (CF-ty F) v)
        ∎) ◁ (λ i → makeVar (tr𝑉𝑎𝑟 (UP-ty i) v))
    UP-tm' (Lam {Γ} {A} {B} t) =
      toPathP
        (transport (λ j → tm (UP-ctx j Γ) (UP-ty j (A ⇒ B))) (CF-tm F (Lam t))
          ≡⟨ (λ i → transport (λ j → tm (lUnit (UP-ctx) i j Γ)
            (UP-ty j (A ⇒ B))) (CF-tm F (Lam t))) ⟩
        transport (λ j → tm ((refl ∙ (λ i → UP-ctx i Γ)) j) (UP-ty' (A ⇒ B) j)) (CF-tm F (Lam t))
          ≡⟨ transport-tm {tm = tm} refl (pres-⇛ p₁ A B) (λ j → UP-ctx j Γ)
            (λ j → UP-ty' A j ⇛ UP-ty' B j) (CF-tm F (Lam t)) ⁻¹ ⟩
        transport (λ j → tm (UP-ctx j Γ) (UP-ty' A j ⇛ UP-ty' B j))
          (transport (λ i → tm (map𝐶𝑡𝑥 (CF-ty F) Γ) (pres-⇛ p₁ A B i)) (CF-tm F (Lam t)))
          ≡⟨ (λ i → transport (λ j → tm (UP-ctx j Γ) (UP-ty' A j ⇛ UP-ty' B j))
            (transport (λ i → tm (map𝐶𝑡𝑥 (CF-ty F) Γ) (pres-⇛ p₁ A B i))
              (transportRefl (CF-tm F (Lam t)) (~ i)))) ⟩
        transport (λ j → tm (UP-ctx j Γ) (UP-ty' A j ⇛ UP-ty' B j))
          (transport (λ i → tm (map𝐶𝑡𝑥 (CF-ty F) Γ) (pres-⇛ p₁ A B i))
            (transport refl (CF-tm F (Lam t))))
          ≡⟨ fromPathP (compPathP (pres-Λ p₁ t) (λ i → Λ (UP-tm' t i))) ⟩
        Λ (interpTm t)
          ∎)
    UP-tm' (App {Γ} {A} {B} t s) =
      toPathP
        (transport (λ i → tm (UP-ctx i Γ) (UP-ty i B)) (CF-tm F (App t s))
          ≡⟨ transp𝑎𝑝𝑝 UP-ty t s ⟩
        𝑎𝑝𝑝 (transport (λ i → tm (map𝐶𝑡𝑥 (UP-ty i) Γ) (UP-ty' (A ⇒ B) i)) (CF-tm F t))
          (transport (λ i → tm (map𝐶𝑡𝑥 (UP-ty i) Γ) (UP-ty i A)) (CF-tm F s))
          ≡⟨ (λ i → 𝑎𝑝𝑝 (fromPathP (UP-tm' t) i) (fromPathP (UP-tm' s) i)) ⟩
        𝑎𝑝𝑝 (interpTm t) (interpTm s)
          ∎)
    UP-tm' (t [ σ ]) =
      (CF-sub F t σ ◁ (λ i → UP-tm' t i ⟦ UP-sub' σ i ⟧)) ▷ CF-sub elim t σ ⁻¹
    UP-tm' {Γ} (β t s i) =
      isSet→SquareP (λ i j → isSetTm)
        (UP-tm' (App (Lam t) s))
        (UP-tm' (t [ idTms Γ ⊕ s ]))
        (λ k → CF-tm F (β t s k))
        (λ k → CF-tm elim (β t s k)) i
    UP-tm' (η t i) =
      isSet→SquareP (λ i j → isSetTm)
        (UP-tm' t)
        (UP-tm' (Lam (App (t [ varify (Contextual.π 𝑟𝑒𝑛) ]) (V 𝑧𝑣))))
        (λ k → CF-tm F (η t k))
        (λ k → CF-tm elim (η t k)) i
    UP-tm' (𝑧𝑣[] σ t i) =
      isSet→SquareP (λ i j → isSetTm)
        (UP-tm' (V 𝑧𝑣 [ σ ⊕ t ]))
        (UP-tm' t)
        (λ k → CF-tm F (𝑧𝑣[] σ t k))
        (λ k → CF-tm elim (𝑧𝑣[] σ t k)) i
    UP-tm' (𝑠𝑣[] v σ t i) =
      isSet→SquareP (λ i j → isSetTm)
        (UP-tm' (V (𝑠𝑣 v) [ σ ⊕ t ]))
        (UP-tm' (V v [ σ ]))
        (λ k → CF-tm F (𝑠𝑣[] v σ t k))
        (λ k → CF-tm elim (𝑠𝑣[] v σ t k)) i
    UP-tm' (Lam[] t σ i) =
      isSet→SquareP (λ i j → isSetTm)
        (UP-tm' (Lam t [ σ ]))
        (UP-tm' (Lam (t [ W₂Tms _ σ ])))
        (λ k → CF-tm F (Lam[] t σ k))
        (λ k → CF-tm elim (Lam[] t σ k)) i
    UP-tm' (App[] t s σ i) =
      isSet→SquareP (λ i j → isSetTm)
        (UP-tm' (App t s [ σ ]))
        (UP-tm' (App (t [ σ ]) (s [ σ ])))
        (λ k → CF-tm F (App[] t s σ k))
        (λ k → CF-tm elim (App[] t s σ k)) i
    UP-tm' ([][] t σ τ i) =
      isSet→SquareP (λ i j → isSetTm)
        (UP-tm' (t [ σ ] [ τ ]))
        (UP-tm' (t [ σ ∘Tms τ ]))
        (λ k → CF-tm F ([][] t σ τ k))
        (λ k → CF-tm elim ([][] t σ τ k)) i
    UP-tm' {Γ} {A} (trunc t s p q i j) =
      isSet→SquareP
        (λ i j →
          isOfHLevelPathP {A = λ k → tm (UP-ctx k Γ) (UP-ty k A)} 2 isSetTm
            (CF-tm F (trunc t s p q i j))
            (CF-tm elim (trunc t s p q i j)))
        (λ k → UP-tm' (p k))
        (λ k → UP-tm' (q k))
        (λ k → UP-tm' t)
        (λ k → UP-tm' s) i j

    UP-tm : PathP (λ i → {Γ : Ctx} {A : Ty} → Tm Γ A → tm (UP-ctx i Γ) (UP-ty i A))
                  (CF-tm F) (CF-tm elim)
    UP-tm i t = UP-tm' t i

    UP : F ≡ elim
    CF-ty (UP i) = UP-ty i
    CF-tm (UP i) = UP-tm i
    CF-id (UP i) {Γ = Γ} =
      isSet→SquareP (λ i j → isSetTms)
        (CF-id F)
        interpId
        (λ k → map𝑇𝑚𝑠₁ (UP-tm k) (idTms Γ))
        (λ k → 𝒾𝒹 (map𝐶𝑡𝑥 (UP-ty k) Γ)) i
    CF-sub (UP i) t σ =
      isSet→SquareP (λ i j → isSetTm)
        (CF-sub F t σ)
        (λ k → interpTm t ⟦ interpTms σ ⟧)
        (λ k → UP-tm k (t [ σ ]))
        (λ k → UP-tm k t ⟦ map𝑇𝑚𝑠₁ (UP-tm k) σ ⟧) i

open Syn

σινInitial : InitialCCC σιν (λ c → Base c)
σινInitial 𝒟 base = initIn elim CCCPres BasePres (λ F p₁ p₂ → UP.UP p₁ p₂)
  where
    open Eliminator 𝒟 base
