{-# OPTIONS --cubical #-}

module tests where

open import lists
open import norm
open import normal
open import syn
open import eliminator

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (zero to Z; suc to S)

open Syn
open Normal σιν Base
open Norm σινInitial

ChurchType : Ty → Ty
ChurchType A = (A ⇒ A) ⇒ A ⇒ A

ChurchBody : {Γ : Ctx} {A : Ty} → ℕ → Tm (Γ ⊹ (A ⇒ A) ⊹ A) A
ChurchBody Z = (V 𝑧𝑣)
ChurchBody (S n) = App (V (𝑠𝑣 𝑧𝑣)) (ChurchBody n)

𝐶𝑁𝑢𝑚 : {Γ : Ctx} {A : Ty} → ℕ → Tm Γ (ChurchType A)
𝐶𝑁𝑢𝑚 n = Lam (Lam (ChurchBody n))

-- Some metatheory

𝐴 = Base 'A'

{-ChurchLem : (t : Tm (∅ ⊹ (𝐴 ⇒ 𝐴) ⊹ 𝐴) 𝐴) → Σ ℕ (λ n → ChurchBody n ≡ t)
ChurchLem t with normalise t
... | NEU (VN v) = 0 , {!!}
... | NEU (APP M N) = {!M!}-}

{-ChurchThm : (t : Tm ∅ (ChurchType 𝐴)) → Σ ℕ (λ n → 𝐶𝑁𝑢𝑚 n ≡ t)
ChurchThm t with normalise t
... | LAM (LAM N) with ChurchLem (ιNf N)
... | n , p = n ,
  {!Lam (Lam (ChurchBody n))
    ≡⟨ ap (Lam ∘ Lam) p ⟩
  ιNf (normalise t)
    ∎!}-}


--Some computational exmaples

PlusType : Ty → Ty
PlusType A = ChurchType A ⇒ ChurchType A ⇒ ChurchType A

Plus : {Γ : Ctx} {A : Ty} → Tm Γ (PlusType A)
Plus = Lam (Lam (Lam (Lam (App (App (V (𝑠𝑣 (𝑠𝑣 (𝑠𝑣 𝑧𝑣)))) (V (𝑠𝑣 𝑧𝑣)))
                               (App (App (V (𝑠𝑣 (𝑠𝑣 𝑧𝑣))) (V (𝑠𝑣 𝑧𝑣))) (V 𝑧𝑣))))))

𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 : (A : Ty) → ℕ → ℕ → Tm ∅ (ChurchType A)
𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 A n m = App (App Plus (𝐶𝑁𝑢𝑚 n)) (𝐶𝑁𝑢𝑚 m)

sum = 𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 (Base 'A') 2 2

test1 = ιNf (norm sum)

test2 = correctness sum

Id : (A : Ty) → Tm ∅ (A ⇒ A)
Id A = Lam (V 𝑧𝑣)

idA⇒A = Id (Base 'A' ⇒ Base 'A')

test3 = ιNf (norm idA⇒A)
test4 = correctness idA⇒A

-- Violation of Nat cannonicity

nf-len : {Γ : Ctx} {A : Ty} → Nf Γ A → ℕ
ne-len : {Γ : Ctx} {A : Ty} → Ne Γ A → ℕ

nf-len (NEU M) = S (ne-len M)
nf-len (LAM N) = S (nf-len N)

ne-len (VN v) = S Z
ne-len (APP M N) = ne-len M + nf-len N

test5 : ℕ
test5 = nf-len (norm sum)


-- Benchmarks

Agda𝐶𝑁𝑢𝑚 : ℕ → ((ℕ → ℕ) → ℕ → ℕ)
Agda𝐶𝑁𝑢𝑚 Z = λ s z → z
Agda𝐶𝑁𝑢𝑚 (S n) = λ s z → s (Agda𝐶𝑁𝑢𝑚 n s z)

AgdaPlus : ((ℕ → ℕ) → ℕ → ℕ) → ((ℕ → ℕ) → ℕ → ℕ) → ((ℕ → ℕ) → ℕ → ℕ)
AgdaPlus n m s z = n s (m s z)

Agda𝐸𝑥𝑝𝑟 : ℕ → ℕ → ((ℕ → ℕ) → ℕ → ℕ)
Agda𝐸𝑥𝑝𝑟 n m = AgdaPlus (Agda𝐶𝑁𝑢𝑚 n) (Agda𝐶𝑁𝑢𝑚 m)
