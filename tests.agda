{-# OPTIONS --cubical #-}

module tests where

open import lists
open import syn
open import norm
open import normal
open import Cubical.Data.Sigma
--open import presheaves

open import Cubical.Data.Nat renaming (zero to Z; suc to S)

open Syn
--open Presheaves σιν (λ c → Base c)
open Normal σιν (λ c → Base c)

ChurchType : Ty → Ty
ChurchType A = (A ⇒ A) ⇒ A ⇒ A

ChurchBody : {Γ : Ctx} {A : Ty} → ℕ → Tm (Γ ⊹ (A ⇒ A) ⊹ A) A
ChurchBody Z = (V 𝑧𝑣)
ChurchBody (S n) = App (V (𝑠𝑣 𝑧𝑣)) (ChurchBody n)

𝐶𝑁𝑢𝑚 : {Γ : Ctx} {A : Ty} → ℕ → Tm Γ (ChurchType A)
𝐶𝑁𝑢𝑚 n = Lam (Lam (ChurchBody n))

-- Some metatheory

𝐴 = Base 'A'

ChurchLem : (t : Tm (∅ ⊹ (𝐴 ⇒ 𝐴) ⊹ 𝐴) 𝐴) → Σ ℕ (λ n → ChurchBody n ≡ t)
ChurchLem t with normalise t
... | NEU (VN v) = {!!}
... | NEU (APP M N) = {!!}

ChurchThm : (t : Tm ∅ (ChurchType 𝐴)) → Σ ℕ (λ n → 𝐶𝑁𝑢𝑚 n ≡ t)
ChurchThm t with normalise t
... | LAM (LAM N) with ChurchLem (ιNf N)
... | n , p = n ,
  {!Lam (Lam (ChurchBody n))
    ≡⟨ ap (Lam ∘ Lam) p ⟩
  ιNf (normalise t)
    ∎!}


--Some computational exmaples

PlusType : Ty → Ty
PlusType A = ChurchType A ⇒ ChurchType A ⇒ ChurchType A

Plus : {Γ : Ctx} {A : Ty} → Tm Γ (PlusType A)
Plus = Lam (Lam (Lam (Lam (App (App (V (𝑠𝑣 (𝑠𝑣 (𝑠𝑣 𝑧𝑣)))) (V (𝑠𝑣 𝑧𝑣)))
                               (App (App (V (𝑠𝑣 (𝑠𝑣 𝑧𝑣))) (V (𝑠𝑣 𝑧𝑣))) (V 𝑧𝑣))))))

𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 : (A : Ty) → ℕ → ℕ → Tm ∅ (ChurchType A)
𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 A n m = App (App Plus (𝐶𝑁𝑢𝑚 n)) (𝐶𝑁𝑢𝑚 m)

sum = 𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 (Base 'A') 2 2

test1 = ιNf (normalise sum)

test2 = correctness sum

Id : (A : Ty) → Tm ∅ (A ⇒ A)
Id A = Lam (V 𝑧𝑣)

idA⇒A = Id (Base 'A' ⇒ Base 'A')

test3 = ιNf (normalise idA⇒A)
test4 = correctness idA⇒A

Agda𝐶𝑁𝑢𝑚 : ℕ → ((ℕ → ℕ) → ℕ → ℕ)
Agda𝐶𝑁𝑢𝑚 Z = λ s z → z
Agda𝐶𝑁𝑢𝑚 (S n) = λ s z → s (Agda𝐶𝑁𝑢𝑚 n s z)

AgdaPlus : ((ℕ → ℕ) → ℕ → ℕ) → ((ℕ → ℕ) → ℕ → ℕ) → ((ℕ → ℕ) → ℕ → ℕ)
AgdaPlus n m s z = n s (m s z)

Agda𝐸𝑥𝑝𝑟 : ℕ → ℕ → ((ℕ → ℕ) → ℕ → ℕ)
Agda𝐸𝑥𝑝𝑟 n m = AgdaPlus (Agda𝐶𝑁𝑢𝑚 n) (Agda𝐶𝑁𝑢𝑚 m)
