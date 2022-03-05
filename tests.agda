{-# OPTIONS --cubical #-}

module tests where

open import lists
open import norm
open import normal
open import syn
open import eliminator

open import Cubical.Data.Nat renaming (zero to Z; suc to S)

data STLCBase : Type where
  𝐴 : STLCBase
  𝐵 : STLCBase

open Syn STLCBase
open Initial STLCBase
open Norm σινInitial
open Normal σιν Base

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

sum = 𝑃𝑙𝑢𝑠𝐸𝑥𝑝𝑟 (Base 𝐴) 2 2

test1 = ιNf (norm sum)

test2 = correctness sum

Id : (A : Ty) → Tm ∅ (A ⇒ A)
Id A = Lam (V 𝑧𝑣)

idA⇒A = Id (Base 𝐴 ⇒ Base 𝐴)

test3 = ιNf (norm idA⇒A)
test4 = correctness idA⇒A

idA = Id (Base 𝐴)

test5 = ιNf (norm idA)
