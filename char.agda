{-# OPTIONS --cubical #-}

module char where

open import syn

open import Agda.Builtin.Char public
open import Agda.Builtin.Char.Properties

open import Cubical.Foundations.Everything renaming (cong to ap)

open import Cubical.Data.Equality
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Nat renaming (zero to Z; suc to S)

open import Cubical.Relation.Nullary public

CharToNat : Char → ℕ
CharToNat = primCharToNat

CharToNatInjective : {c d : Char} → CharToNat c ≡c CharToNat d → c ≡ d
CharToNatInjective  {c} {d} p = ptoc (primCharToNatInjective c d (ctop p))

discreteChar : Discrete Char
discreteChar c d with discreteℕ (CharToNat c) (CharToNat d)
... | yes p = yes (CharToNatInjective p)
... | no ¬p = no (λ p → ¬p (ap CharToNat p))

open Syn

extractChar : Ty → Char
extractChar (Base c) = c
extractChar (A ⇒ B) = 'a'

caseTy : ∀ {ℓ} {A : Type ℓ} → (aBase aArr : A) → Ty → A
caseTy aBase aArr (Base c) = aBase
caseTy aBase aArr (A ⇒ B) = aArr

π₁Ty : Ty → Ty
π₁Ty (Base c) = Base c
π₁Ty (A ⇒ B) = A

π₂Ty : Ty → Ty
π₂Ty (Base c) = Base c
π₂Ty (A ⇒ B) = B

discreteTy : Discrete Ty
discreteTy (Base c) (Base d) with discreteChar c d
... | yes p = yes (ap Base p)
... | no ¬p = no (λ p → ¬p (ap extractChar p))
discreteTy (Base c) (B₁ ⇒ B₂) = no (λ p → subst (caseTy ℕ ⊥) p 0)
discreteTy (A₁ ⇒ A₂) (Base x) = no (λ p → subst (caseTy ⊥ ℕ) p 0)
discreteTy (A₁ ⇒ A₂) (B₁ ⇒ B₂) with discreteTy A₁ B₁
... | no ¬p = no (λ l → ¬p (ap π₁Ty l))
... | yes p with discreteTy A₂ B₂
... | yes q = yes (λ i → p i ⇒ q i)
... | no ¬q = no (λ l → ¬q (ap π₂Ty l))





