{-# OPTIONS --cubical #-}

module tests where

open import lists
open import norm
open import normal
open import syn
open import eliminator

open import Cubical.Data.Nat renaming (zero to Z; suc to S)

data STLCBase : Type where
  π΄ : STLCBase
  π΅ : STLCBase

open Syn STLCBase
open Initial STLCBase
open Norm ΟΞΉΞ½Initial
open Normal ΟΞΉΞ½ Base

ChurchType : Ty β Ty
ChurchType A = (A β A) β A β A

ChurchBody : {Ξ : Ctx} {A : Ty} β β β Tm (Ξ βΉ (A β A) βΉ A) A
ChurchBody Z = (V π§π£)
ChurchBody (S n) = App (V (π π£ π§π£)) (ChurchBody n)

πΆππ’π : {Ξ : Ctx} {A : Ty} β β β Tm Ξ (ChurchType A)
πΆππ’π n = Lam (Lam (ChurchBody n))

PlusType : Ty β Ty
PlusType A = ChurchType A β ChurchType A β ChurchType A

Plus : {Ξ : Ctx} {A : Ty} β Tm Ξ (PlusType A)
Plus = Lam (Lam (Lam (Lam (App (App (V (π π£ (π π£ (π π£ π§π£)))) (V (π π£ π§π£)))
                               (App (App (V (π π£ (π π£ π§π£))) (V (π π£ π§π£))) (V π§π£))))))

πππ’π πΈπ₯ππ : (A : Ty) β β β β β Tm β (ChurchType A)
πππ’π πΈπ₯ππ A n m = App (App Plus (πΆππ’π n)) (πΆππ’π m)

sum = πππ’π πΈπ₯ππ (Base π΄) 2 2

test1 = ΞΉNf (norm sum)

test2 = correctness sum

Id : (A : Ty) β Tm β (A β A)
Id A = Lam (V π§π£)

idAβA = Id (Base π΄ β Base π΄)

test3 = ΞΉNf (norm idAβA)
test4 = correctness idAβA

idA = Id (Base π΄)

test5 = ΞΉNf (norm idA)
