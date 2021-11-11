{-# OPTIONS --cubical #-}

module tests where

open import ren2
open import syn3
open import normal
open import norm

ChurchType : Ty → Ty
ChurchType A = (A ⇒ A) ⇒ A ⇒ A

ChurchTwo : {Γ : Ctx} {A : Ty} → Tm Γ (ChurchType A)
ChurchTwo = Lam (Lam (App (V (Sv Zv)) (App (V (Sv Zv)) (V Zv))))

PlusType : Ty → Ty
PlusType A = ChurchType A ⇒ ChurchType A ⇒ ChurchType A

Plus : {Γ : Ctx} {A : Ty} → Tm Γ (PlusType A)
Plus = Lam (Lam (Lam (Lam (App (App (V (Sv (Sv (Sv Zv)))) (V (Sv Zv)))
                               (App (App (V (Sv (Sv Zv))) (V (Sv Zv))) (V Zv))))))

TwoPlusTwo : {A : Ty} → Tm ∅ (ChurchType A)
TwoPlusTwo = App (App Plus ChurchTwo) ChurchTwo

test1 = norm (TwoPlusTwo {Base 'A'})
