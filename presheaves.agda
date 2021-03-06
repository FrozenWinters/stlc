{-# OPTIONS --cubical #-}

module presheaves where

open import lists
open import contextual
open import ccc
open import normal
open import psh

private
  variable
    โ : Level

module Presheaves (๐ : Contextual โ โ) โฆ ๐CCC : CCC ๐ โฆ
                  {X : Type โ} (base : X โ Contextual.ty ๐) where
  open Normal ๐ base
  open Contextual ๐
  open Presheaf REN
  --open PShWeave REN
  open PSh
  open PShMor
  open PShMorCart

  ๐๐โ = ๐ซ๐ฎ๐ฝ

  private
    module P = Contextual ๐ซ๐ฎ๐ฝ

  TM : (A : ty) โ PSh
  sec (TM A) ฮ = tm ฮ A
  isSetSec (TM A) = isSetTm
  hom (TM A) ฯ t = t โฆ makeRen ฯ โง
  id-hom (TM A) t = ap (t โฆ_โง) ๐พ๐นฮทโ โ ๐พ๐นโฆโง t
  โ-hom (TM A) ฯ ฯ t = ap (t โฆ_โง) (makeโ๐๐๐ ฯ ฯ) โ โฆโงโฆโง t (makeRen ฯ) (makeRen ฯ) โปยน

  {-TMS = plurify TM

  TMใ : {ฮ : ctx} {A : ty} โ tm ฮ A โ PShMor (TMS ฮ) (TM A)
  ob (TMใ t) ๐s = t โฆ โ ๐s โง
  nat (TMใ {ฮ} t) ฯ ๐s =
    t โฆ โ (homs (TMS ฮ) ฯ ๐s) โง
      โกโจ ap (t โฆ_โง) (โhom ฯ ๐s) โฉ
    t โฆ โ ๐s โ makeRen ฯ โง
      โกโจ โฆโงโฆโง t (โ ๐s) (makeRen ฯ) โปยน โฉ
    t โฆ โ ๐s โง โฆ makeRen ฯ โง
      โ

  TMSใ : {ฮ ฮ : ctx} โ tms ฮ ฮ โ PShMors (TMS ฮ) (TMS ฮ)
  TMSใ = map๐ธ๐๐ โ TMใ

  โTMSใ : {ฮ ฮ ฮฃ : ctx} (ฯ : tms ฮ ฮ) (๐s : secs (TMS ฮ) ฮฃ) โ
    โ (obs (TMSใ ฯ) ๐s) โก ฯ โ โ ๐s
  โTMSใ ! ๐s = refl
  โTMSใ (ฯ โ t) ๐s i  = โTMSใ ฯ ๐s i โ t โฆ โ ๐s โง

  TMใโฆโง : {ฮ ฮ : ctx} {A : ty} (t : tm ฮ A) (ฯ : tms ฮ ฮ) โ
    TMใ (t โฆ ฯ โง) โก TMใ t P.โฆ TMSใ ฯ โง
  TMใโฆโง t ฯ =
    โกPShMor
      (ฮป ๐s โ
        t โฆ ฯ โง โฆ โ ๐s โง
          โกโจ โฆโงโฆโง t ฯ (โ ๐s) โฉ
        t โฆ ฯ โ โ ๐s โง
          โกโจ ap (t โฆ_โง) (โTMSใ ฯ ๐s โปยน) โฉ
        t โฆ โ (obs (TMSใ ฯ) ๐s) โง
          โ)-}

  NE : ty โ PSh
  sec (NE A) ฮ = Ne ฮ A
  isSetSec (NE A) = isSetNeutral
  hom (NE A) ฯ M = M [ ฯ ]NE
  id-hom (NE A) = [id]NE
  โ-hom (NE A) ฯ ฯ M = [][]NE M ฯ ฯ โปยน

  NF : ty โ PSh
  sec (NF A) ฮ = Nf ฮ A
  isSetSec (NF A) = isSetNormal
  hom (NF A) ฯ N = N [ ฯ ]NF
  id-hom (NF A) = [id]NF
  โ-hom (NF A) ฯ ฯ N = [][]NF N ฯ ฯ โปยน

  ฮนNE : (A : ty) โ PShMorCart (NE A) (TM A)
  ob (ฮนNE A) = ฮนNe
  nat (ฮนNE A) ฯ M = ฮนNeLem M ฯ

  ฮนNF : (A : ty) โ PShMorCart (NF A) (TM A)
  ob (ฮนNF A) = ฮนNf
  nat (ฮนNF A) ฯ N = ฮนNfLem N ฯ

  
