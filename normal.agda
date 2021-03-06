{-# OPTIONS --cubical --allow-unsolved-metas #-}

module normal where

open import lists
open import contextual
open import ccc
open import psh

open import Cubical.Data.Nat renaming (zero to Z; suc to S) hiding (elim)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private
  variable
    β : Level

-- We define normal and neutral terms

module Normal (π : Contextual β β) β¦ πCCC : CCC π β¦
              {X : Type β} (base : X β Contextual.ty π) where
  open Contextual π
  open CCC πCCC
  open Presheaf REN

  private
    module R = Contextual ΟΞ΅Ξ½

  data Ne : (Ξ : ctx) (A : ty) β Type β
  data Nf : (Ξ : ctx) (A : ty) β Type β

  data Ne where
    VN : {Ξ : ctx} {A : ty} β IntVar Ξ A β Ne Ξ A
    APP : {Ξ : ctx} {A B : ty} β Ne Ξ (A β B) β Nf Ξ A β Ne Ξ B

  data Nf where
    NEU : {Ξ : ctx} {x : X} β Ne Ξ (base x) β Nf Ξ (base x)
    LAM : {Ξ : ctx} {A B : ty} β Nf (Ξ βΉ A) B β Nf Ξ (A β B)

  infix 30 _[_]NE _[_]NF
  _[_]NE : {Ξ Ξ : ctx} {A : ty} β Ne Ξ A β IntRen Ξ Ξ β Ne Ξ A
  _[_]NF : {Ξ Ξ : ctx} {A : ty} β Nf Ξ A β IntRen Ξ Ξ β Nf Ξ A

  APP M N [ Ο ]NE = APP (M [ Ο ]NE) (N [ Ο ]NF)
  VN v [ Ο ]NE = VN (v R.β¦ Ο β§)

  NEU M [ Ο ]NF = NEU (M [ Ο ]NE)
  LAM {A = A} N [ Ο ]NF = LAM (N [ Wβπππ A Ο ]NF)

  [id]NE : {Ξ : ctx} {A : ty} β (M : Ne Ξ A) β
    M [ R.πΎπΉ Ξ ]NE β‘ M
  [id]NF : {Ξ : ctx} {A : ty} β (N : Nf Ξ A) β
    N [ R.πΎπΉ Ξ ]NF β‘ N

  [id]NE (VN π§π£) = refl
  [id]NE (VN (π π£ v)) =
    VN (v R.β¦ Wβπππ _ (R.πΎπΉ _) β§)
      β‘β¨ ap VN (Wlem2πππ v (R.πΎπΉ _)) β©
    VN (π π£ (v R.β¦ R.πΎπΉ _ β§))
      β‘β¨ ap VN (ap π π£ (R.πΎπΉβ¦β§ v)) β©
    VN (π π£ v)
      β
  [id]NE (APP M N) i = APP ([id]NE M i) ([id]NF N i)

  [id]NF (NEU M) = ap NEU ([id]NE M)
  [id]NF (LAM N) = ap LAM ([id]NF N)

  [][]NE : {Ξ Ξ Ξ£ : ctx} {A : ty} (M : Ne Ξ£ A) (Ο : IntRen Ξ Ξ£) (Ο : IntRen Ξ Ξ) β
    M [ Ο ]NE [ Ο ]NE β‘ M [ Ο R.β Ο ]NE
  [][]NF : {Ξ Ξ Ξ£ : ctx} {A : ty} (N : Nf Ξ£ A) (Ο : IntRen Ξ Ξ£) (Ο : IntRen Ξ Ξ) β
    N [ Ο ]NF [ Ο ]NF β‘ N [ Ο R.β Ο ]NF

  [][]NE (VN v) Ο Ο = ap VN (R.β¦β§β¦β§ v Ο Ο)
  [][]NE (APP M N) Ο Ο i = APP ([][]NE M Ο Ο i) ([][]NF N Ο Ο i)

  [][]NF (NEU M) Ο Ο = ap NEU ([][]NE M Ο Ο)
  [][]NF (LAM N) Ο Ο =
    LAM (N [ Wβπππ _ Ο ]NF [ Wβπππ _ Ο ]NF)
      β‘β¨ ap LAM ([][]NF N (Wβπππ _ Ο) (Wβπππ _ Ο) ) β©
    LAM (N [ Wβπππ _ Ο R.β Wβπππ _ Ο ]NF)
      β‘β¨ (Ξ» i β LAM (N [ Wlem4πππ Ο Ο i ]NF)) β©
    LAM (N [ Wβπππ _ (Ο R.β Ο) ]NF)
      β

  isSetNeutral : {Ξ : ctx} {A : ty} β isSet (Ne Ξ A)
  isSetNeutral = {!!}

  isSetNormal : {Ξ : ctx} {A : ty} β isSet (Nf Ξ A)
  isSetNormal = {!!}

  ΞΉNe : {Ξ : ctx} {A : ty} β Ne Ξ A β tm Ξ A
  ΞΉNf : {Ξ : ctx} {A : ty} β Nf Ξ A β tm Ξ A

  ΞΉNe (VN v) = makeVar v
  ΞΉNe (APP M N) = πππ (ΞΉNe M) (ΞΉNf N)

  ΞΉNf (NEU M) = ΞΉNe M
  ΞΉNf (LAM N) = Ξ (ΞΉNf N)

  ΞΉNeLem : {Ξ Ξ : ctx} {A : ty} (M : Ne Ξ A) (Ο : IntRen Ξ Ξ) β
    ΞΉNe (M [ Ο ]NE) β‘ ΞΉNe M β¦ makeRen Ο β§
  ΞΉNfLem : {Ξ Ξ : ctx} {A : ty} (N : Nf Ξ A) (Ο : IntRen Ξ Ξ) β
    ΞΉNf (N [ Ο ]NF) β‘ ΞΉNf N β¦ makeRen Ο β§

  ΞΉNeLem (VN v) Ο = make[]π v Ο
  ΞΉNeLem (APP M N) Ο =
    πππ (ΞΉNe (M [ Ο ]NE)) (ΞΉNf (N [ Ο ]NF))
      β‘β¨ (Ξ» i β πππ (ΞΉNeLem M Ο i) (ΞΉNfLem N Ο i)) β©
    πππ (ΞΉNe M β¦ makeRen Ο β§) (ΞΉNf N β¦ makeRen Ο β§)
      β‘β¨ πππβ¦β§ (ΞΉNe M) (ΞΉNf N) (makeRen Ο) β»ΒΉ β©
    πππ (ΞΉNe M) (ΞΉNf N) β¦ makeRen Ο β§
      β

  ΞΉNfLem (NEU M) Ο = ΞΉNeLem M Ο
  ΞΉNfLem (LAM {Ξ} {A} N) Ο =
    Ξ (ΞΉNf (N [ Wβπππ A Ο ]NF))
      β‘β¨ ap Ξ (ΞΉNfLem N (Wβπππ A Ο)) β©
    Ξ (ΞΉNf N β¦ makeRen (Wβπππ A Ο) β§)
      β‘β¨ (Ξ» i β Ξ (ΞΉNf N β¦ makeW Ο i β π§ β§)) β©
    Ξ (ΞΉNf N β¦ Wβtms A (makeRen Ο) β§)
      β‘β¨ Ξnat (ΞΉNf N) (makeRen Ο) β»ΒΉ β©
    Ξ (ΞΉNf N) β¦ makeRen Ο β§
      β

  Nes = πππ  Ne
  Nfs = πππ  Nf

  _[_]NFS : {Ξ Ξ Ξ£ : ctx} β Nfs Ξ Ξ£ β IntRen Ξ Ξ β Nfs Ξ Ξ£
  NS [ Ο ]NFS = mapπΈππ  _[ Ο ]NF NS

  ΞΉNes : {Ξ Ξ : ctx} β Nes Ξ Ξ β tms Ξ Ξ
  ΞΉNes = mapπΈππ  ΞΉNe

  ΞΉNfs : {Ξ Ξ : ctx} β Nfs Ξ Ξ β tms Ξ Ξ
  ΞΉNfs = mapπΈππ  ΞΉNf

  ΞΉNfsLem : {Ξ Ξ Ξ£ : ctx} (NS : Nfs Ξ Ξ£) (Ο : IntRen Ξ Ξ) β
    ΞΉNfs (NS [ Ο ]NFS) β‘ ΞΉNfs NS β (makeRen Ο)
  ΞΉNfsLem ! Ο = refl
  ΞΉNfsLem (NS β N) Ο i = ΞΉNfsLem NS Ο i β ΞΉNfLem N Ο i

  idNes : (Ξ : ctx) β Nes Ξ Ξ
  idNes Ξ = mapπΈππ  VN (idπππ Ξ)

  ΞΉIdNes : (Ξ : ctx) β ΞΉNes (idNes Ξ) β‘ πΎπΉ Ξ
  ΞΉIdNes Ξ =
    mapπΈππ  ΞΉNe (mapπΈππ  VN (idπππ Ξ))
      β‘β¨ mapπΈππ comp ΞΉNe VN (idπππ Ξ) β©
    makeRen (idπππ Ξ)
      β‘β¨ πΎπΉΞ·β β©
    πΎπΉ Ξ
      β

  open PSh
  open PShMorCart

  TM : (A : ty) β PSh
  sec (TM A) Ξ = tm Ξ A
  isSetSec (TM A) = isSetTm
  hom (TM A) Ο t = t β¦ makeRen Ο β§
  id-hom (TM A) t = ap (t β¦_β§) πΎπΉΞ·β β πΎπΉβ¦β§ t
  β-hom (TM A) Ο Ο t = ap (t β¦_β§) (makeβπππ Ο Ο) β β¦β§β¦β§ t (makeRen Ο) (makeRen Ο) β»ΒΉ

  NE : ty β PSh
  sec (NE A) Ξ = Ne Ξ A
  isSetSec (NE A) = isSetNeutral
  hom (NE A) Ο M = M [ Ο ]NE
  id-hom (NE A) = [id]NE
  β-hom (NE A) Ο Ο M = [][]NE M Ο Ο β»ΒΉ

  NF : ty β PSh
  sec (NF A) Ξ = Nf Ξ A
  isSetSec (NF A) = isSetNormal
  hom (NF A) Ο N = N [ Ο ]NF
  id-hom (NF A) = [id]NF
  β-hom (NF A) Ο Ο N = [][]NF N Ο Ο β»ΒΉ

  ΞΉNE : (A : ty) β PShMorCart (NE A) (TM A)
  ob (ΞΉNE A) = ΞΉNe
  nat (ΞΉNE A) Ο M = ΞΉNeLem M Ο

  ΞΉNF : (A : ty) β PShMorCart (NF A) (TM A)
  ob (ΞΉNF A) = ΞΉNf
  nat (ΞΉNF A) Ο N = ΞΉNfLem N Ο
