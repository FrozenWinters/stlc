{-# OPTIONS --cubical #-}

module tests where

open import ren
open import syn
open import normal
open import norm
open import twgl

open import Cubical.Data.Nat renaming (zero to Z; suc to S)

ChurchType : Ty → Ty
ChurchType A = (A ⇒ A) ⇒ A ⇒ A

ChurchBody : {Γ : Ctx} {A : Ty} → ℕ → Tm (Γ ⊹ (A ⇒ A) ⊹ A) A
ChurchBody Z = (V 𝑧𝑣)
ChurchBody (S n) = App (V (𝑠𝑣 𝑧𝑣)) (ChurchBody n)

𝐶𝑁𝑢𝑚 : {Γ : Ctx} {A : Ty} → ℕ → Tm Γ (ChurchType A)
𝐶𝑁𝑢𝑚 n = Lam (Lam (ChurchBody n))

PlusType : Ty → Ty
PlusType A = ChurchType A ⇒ ChurchType A ⇒ ChurchType A

Plus : {Γ : Ctx} {A : Ty} → Tm Γ (PlusType A)
Plus = Lam (Lam (Lam (Lam (App (App (V (𝑠𝑣 (𝑠𝑣 (𝑠𝑣 𝑧𝑣)))) (V (𝑠𝑣 𝑧𝑣)))
                               (App (App (V (𝑠𝑣 (𝑠𝑣 𝑧𝑣))) (V (𝑠𝑣 𝑧𝑣))) (V 𝑧𝑣))))))

𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 : (A : Ty) → ℕ → ℕ → Tm ∅ (ChurchType A)
𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 A n m = App (App Plus (𝐶𝑁𝑢𝑚 n)) (𝐶𝑁𝑢𝑚 m)

sum = semantics (𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 (Base 'A') 1000 1000)

test1 = ιNf (GlTm-norm sum)

test2 = GlTm-correctness sum

Id : (A : Ty) → Tm ∅ (A ⇒ A)
Id A = Lam (V 𝑧𝑣)

idA⇒A = semantics (Id (Base 'A' ⇒ Base 'A'))

test3 = ιNf (GlTm-norm idA⇒A)
test4 = GlTm-correctness idA⇒A

Agda𝐶𝑁𝑢𝑚 : ℕ → ((ℕ → ℕ) → ℕ → ℕ)
Agda𝐶𝑁𝑢𝑚 Z = λ s z → z
Agda𝐶𝑁𝑢𝑚 (S n) = λ s z → s (Agda𝐶𝑁𝑢𝑚 n s z)

AgdaPlus : ((ℕ → ℕ) → ℕ → ℕ) → ((ℕ → ℕ) → ℕ → ℕ) → ((ℕ → ℕ) → ℕ → ℕ)
AgdaPlus n m s z = n s (m s z)

Agda𝐸𝑥𝑝𝑟 : ℕ → ℕ → ((ℕ → ℕ) → ℕ → ℕ)
Agda𝐸𝑥𝑝𝑟 n m = AgdaPlus (Agda𝐶𝑁𝑢𝑚 n) (Agda𝐶𝑁𝑢𝑚 m)
