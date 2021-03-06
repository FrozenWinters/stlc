{-# OPTIONS --cubical  #-}

module twglccc where

open import lists
open import contextual
open import ccc
open import normal
open import psh
open import twgl

module TwGlCCC {โ} (๐ : Contextual โ โ) โฆ ๐CCC : CCC ๐ โฆ
                   {X : Type โ} (base : X โ Contextual.ty ๐) where
  open Contextual ๐
  open Presheaf REN
  open PresheafCCC REN
  open TwGlCC ๐ base
  open CCC ๐CCC
  open Normal ๐ base

  private
    module R = Contextual ฯฮตฮฝ
    module T = Contextual TwGl
    module P = Contextual ๐ซ๐ฎ๐ฝ

  open GlTy
  open GlTm
  open PSh
  open PShMor
  open PShMorCart

  A-AโB : (A B : GlTy) โ ty
  A-AโB A B = Gl-A A โ Gl-A B

  โฆAโฆ-AโB : (A B : GlTy) โ PSh
  โฆAโฆ-AโB A B = Gl-โฆAโฆ A โPSh Gl-โฆAโฆ B
  
  q-AโB : (A B : GlTy) โ PShMorCart (โฆAโฆ-AโB A B) (NF (A-AโB A B))
  ob (q-AโB A B) ๐ป = LAM (โชGl-qโซ B (ob ๐ป (R.ฯ , โชGl-uโซ A (VN ๐ง๐ฃ))))
  nat (q-AโB A B) {ฮ} {ฮ} ฯ ๐ป =
    LAM (โชGl-qโซ B (ob ๐ป (ฯ R.โ R.ฯ , โชGl-uโซ A (VN ๐ง๐ฃ))))
      โกโจ (ฮป i โ LAM (โชGl-qโซ B (ob ๐ป (lem i , nat (Gl-u A) (Wโ๐๐๐ ๐ด ฯ) (VN ๐ง๐ฃ) i)))) โฉ
    LAM (โชGl-qโซ B (ob ๐ป (R.ฯ R.โ Wโ๐๐๐ ๐ด ฯ , hom (Gl-โฆAโฆ A) (Wโ๐๐๐ ๐ด ฯ) (โชGl-uโซ A (VN ๐ง๐ฃ)))))
      โกโจ (ฮป i โ LAM (โชGl-qโซ B (nat ๐ป (Wโ๐๐๐ ๐ด ฯ) (R.ฯ , โชGl-uโซ A (VN ๐ง๐ฃ)) i))) โฉ
    LAM (โชGl-qโซ B (hom (Gl-โฆAโฆ B) (Wโ๐๐๐ ๐ด ฯ) (ob ๐ป (R.ฯ , โชGl-uโซ A (VN ๐ง๐ฃ)))))
      โกโจ ap LAM (nat (Gl-q B) (Wโ๐๐๐ ๐ด ฯ) (ob ๐ป (R.ฯ , โชGl-uโซ A (VN ๐ง๐ฃ)))) โฉ
    LAM (โชGl-qโซ B (ob ๐ป (R.ฯ , โชGl-uโซ A (VN ๐ง๐ฃ)))) [ ฯ ]NF
      โ where
    ๐ด = Gl-A A
    lem : ฯ R.โ R.ฯ โก R.ฯ R.โ (Wโ๐๐๐ (Gl-A A) ฯ)
    lem =
      ฯ R.โ R.ฯ
        โกโจ Wlem3๐๐๐ ฯ (R.๐พ๐น ฮ) โฉ
      Wโ๐๐๐ (Gl-A A) (ฯ โ๐๐๐ R.๐พ๐น ฮ)
        โกโจ (ฮป i โ Wโ๐๐๐ (Gl-A A) (R.๐พ๐นL (R.๐พ๐นR ฯ i) (~ i))) โฉ
      Wโ๐๐๐ (Gl-A A) (R.๐พ๐น ฮ โ๐๐๐ ฯ)
        โกโจ Wlem5๐๐๐ (R.๐พ๐น ฮ) ฯ โปยน โฉ
      R.ฯ R.โ Wโ๐๐๐ (Gl-A A) ฯ
        โ

  u-AโB : (A B : GlTy) โ PShMorCart (NE (A-AโB A B)) (โฆAโฆ-AโB A B)
  ob (ob (u-AโB A B) M) (ฯ , ๐) = โชGl-uโซ B (APP (M [ ฯ ]NE) (โชGl-qโซ A ๐))
  nat (ob (u-AโB A B) M) ฯ (ฯ , ๐)=
    โชGl-uโซ B (APP (M [ ฯ R.โ ฯ ]NE) (โชGl-qโซ A (hom (Gl-โฆAโฆ A) ฯ ๐)))
      โกโจ (ฮป i โ โชGl-uโซ B (APP ([][]NE M ฯ ฯ (~ i)) (nat (Gl-q A) ฯ ๐ i))) โฉ
    โชGl-uโซ B (APP (M [ ฯ ]NE) (โชGl-qโซ A ๐) [ ฯ ]NE)
      โกโจ nat (Gl-u B) ฯ (APP (M [ ฯ ]NE) (โชGl-qโซ A ๐)) โฉ
    hom (Gl-โฆAโฆ B) ฯ (โชGl-uโซ B (APP (M [ ฯ ]NE) (โชGl-qโซ A ๐)))
      โ
  nat (u-AโB A B) ฯ M =
    โกPShMorCart (ฮป {(ฯ , ๐) i โ โชGl-uโซ B (APP ([][]NE M ฯ ฯ i) (โชGl-qโซ A ๐))})

  comp-AโB : (A B : GlTy) {ฮ : ctx} (M : Ne ฮ (A-AโB A B)) โ
    (ฮนNf โ ob (q-AโB A B) โ ob (u-AโB A B)) M โก ฮนNe M
  comp-AโB A B M =
    ฮ ((ฮนNf โ โชGl-qโซ B โ โชGl-uโซ B) (APP (M [ R.ฯ ]NE) ((โชGl-qโซ A โ โชGl-uโซ A) (VN ๐ง๐ฃ))))
      โกโจ ap ฮ (Gl-comp B (APP (M [ R.ฯ ]NE) ((โชGl-qโซ A โ โชGl-uโซ A) (VN ๐ง๐ฃ)))) โฉ
    ฮ (๐๐๐ (ฮนNe (M [ R.ฯ ]NE)) ((ฮนNf โ โชGl-qโซ A โ โชGl-uโซ A) (VN ๐ง๐ฃ)))
      โกโจ (ฮป i โ ฮ (๐๐๐ (ฮนNeLem M R.ฯ i) (Gl-comp A (VN ๐ง๐ฃ) i))) โฉ
    ฮ (๐๐๐ (ฮนNe M โฆ makeRen R.ฯ โง) ๐ง)
      โกโจ (ฮป i โ ฮ (๐๐๐ (ฮนNe M โฆ ฯฮท i โง) ๐ง)) โฉ
    ฮ (๐๐๐ (ฮนNe M โฆ ฯ โง) ๐ง)
      โกโจ ๐๐๐ฮท (ฮนNe M) โปยน โฉ
    ฮนNe M
      โ

  record Subset {โโ โโ : Level} : Type (lsuc (โโ โ โโ))  where
    field
      Sub-A : Type โโ
      Sub-q : isSet Sub-A
      Sub-B : Sub-A โ Type โโ
      Sub-p : (๐ : Sub-A) โ (isProp (Sub-B ๐))
      
    type = ฮฃ Sub-A Sub-B

    isSetType : isSet type
    isSetType = isSetฮฃ Sub-q (ฮป ๐ โ isPropโisSet (Sub-p ๐))
    
    subtypeLem : {๐ ๐ : type} โ fst ๐ โก fst ๐ โ ๐ โก ๐
    subtypeLem {๐} {๐} a i = a i , isOfHLevelโisOfHLevelDep 1 (ฮป z โ Sub-p z) (snd ๐) (snd ๐) a i

  open Subset

  โฆAโBโฆ-sec : (A B : GlTy) (ฮ : ctx) โ Subset
  Sub-A (โฆAโBโฆ-sec A B ฮ) = sec (โฆAโฆ-AโB A B) ฮ
  Sub-q (โฆAโBโฆ-sec A B ฮ) = isSetSec (โฆAโฆ-AโB A B)
  Sub-B (โฆAโBโฆ-sec A B ฮ) ๐ป = (ฮ : ctx) (ฯ : IntRen ฮ ฮ) (๐ : sec (Gl-โฆAโฆ A) ฮ) โ
    (ฮนNf โ โชGl-qโซ B โ ob ๐ป) (ฯ , ๐)
    โก ๐๐๐ (ฮนNf (ob (q-AโB A B) ๐ป [ ฯ ]NF)) (ฮนNf (โชGl-qโซ A ๐))
  Sub-p (โฆAโBโฆ-sec A B ฮ) ฮฑ = isPropฮ?3 (ฮป ฮ ฯ y โ isSetTm _ _)

  _โTwGl_ : GlTy โ GlTy โ GlTy
  Gl-A (A โTwGl B) = A-AโB A B
  
  sec (Gl-โฆAโฆ (A โTwGl B)) ฮ = type (โฆAโBโฆ-sec A B ฮ)
  isSetSec (Gl-โฆAโฆ (A โTwGl B)) {ฮ} = isSetType (โฆAโBโฆ-sec A B ฮ)
  hom (Gl-โฆAโฆ (A โTwGl B)) ฯ (๐ป , p) =
    hom (โฆAโฆ-AโB A B) ฯ ๐ป ,
    (ฮป ฮ ฯ ๐ โ
      (ฮนNf โ โชGl-qโซ B โ ob ๐ป) (ฯ R.โ ฯ , ๐)
        โกโจ p ฮ (ฯ R.โ ฯ) ๐ โฉ
      ๐๐๐ (ฮนNf (ob (q-AโB A B) ๐ป [ ฯ R.โ ฯ ]NF)) (ฮนNf (โชGl-qโซ A ๐))
        โกโจ (ฮป i โ ๐๐๐ (ฮนNf ([][]NF (ob (q-AโB A B) ๐ป) ฯ ฯ (~ i))) (ฮนNf (โชGl-qโซ A ๐))) โฉ
      ๐๐๐ (ฮนNf (ob (q-AโB A B) ๐ป [ ฯ ]NF [ ฯ ]NF)) (ฮนNf (โชGl-qโซ A ๐))
        โกโจ (ฮป i โ ๐๐๐ (ฮนNf (nat (q-AโB A B) ฯ ๐ป (~ i) [ ฯ ]NF)) (ฮนNf (โชGl-qโซ A ๐))) โฉ
      ๐๐๐ (ฮนNf (ob (q-AโB A B) (hom (โฆAโฆ-AโB A B) ฯ ๐ป) [ ฯ ]NF)) (ฮนNf (โชGl-qโซ A ๐))
        โ)
  id-hom (Gl-โฆAโฆ (A โTwGl B)) {ฮ} (๐ป , p) =
    subtypeLem (โฆAโBโฆ-sec A B ฮ) (id-hom (โฆAโฆ-AโB A B) ๐ป)
  โ-hom (Gl-โฆAโฆ (A โTwGl B)) {ฮ} ฯ ฯ (๐ป , p) =
    subtypeLem (โฆAโBโฆ-sec A B ฮ) (โ-hom (โฆAโฆ-AโB A B) ฯ ฯ ๐ป)

  ob (Gl-q (A โTwGl B)) (๐ป , p) = ob (q-AโB A B) ๐ป
  nat (Gl-q (A โTwGl B)) ฯ (๐ป , p) = nat (q-AโB A B) ฯ ๐ป
  
  ob (Gl-u (A โTwGl B)) M =
    ob (u-AโB A B) M ,
    (ฮป ฮ ฯ ๐ โ
      (ฮนNf โ โชGl-qโซ B โ โชGl-uโซ B) (APP (M [ ฯ ]NE) (โชGl-qโซ A ๐))
        โกโจ Gl-comp B (APP (M [ ฯ ]NE) (โชGl-qโซ A ๐)) โฉ
      ๐๐๐ (ฮนNe (M [ ฯ ]NE)) (ฮนNf (โชGl-qโซ A ๐))
        โกโจ (ฮป i โ  ๐๐๐ (ฮนNeLem M ฯ i) (ฮนNf (โชGl-qโซ A ๐))) โฉ
      ๐๐๐ (ฮนNe M โฆ makeRen ฯ โง) (ฮนNf (โชGl-qโซ A ๐))
        โกโจ (ฮป i โ  ๐๐๐ (comp-AโB A B M (~ i) โฆ makeRen ฯ โง) (ฮนNf (โชGl-qโซ A ๐))) โฉ
      ๐๐๐ ((ฮนNf โ ob (q-AโB A B) โ ob (u-AโB A B)) M โฆ makeRen ฯ โง) (ฮนNf (โชGl-qโซ A ๐))
        โกโจ (ฮป i โ ๐๐๐ (ฮนNfLem ((ob (q-AโB A B) โ ob (u-AโB A B)) M) ฯ (~ i)) (ฮนNf (โชGl-qโซ A ๐))) โฉ
      ๐๐๐ (ฮนNf (ob (q-AโB A B) (ob (u-AโB A B) M) [ ฯ ]NF)) (ฮนNf (โชGl-qโซ A ๐))
        โ)
  nat (Gl-u (A โTwGl B)) {ฮ} ฯ M =
    subtypeLem (โฆAโBโฆ-sec A B ฮ) (nat (u-AโB A B) ฯ M)
  
  Gl-comp (A โTwGl B) M = comp-AโB A B M

  ฮTwGl-nat : {ฮ : GlCtx} {A B : GlTy} (t : GlTm (ฮ โน A) B) {ฮ : ctx} (๐s : secs (Gls-โฆฮโฆ ฮ) ฮ) โ
    (ฮนNf โ ob (q-AโB A B) โ ob (ฮPSh (GlTm-โฆฮฑโฆ t))) ๐s
    โก ฮ (GlTm-ฮฑ t) โฆ (ฮนNfs โ โชGls-qโซ ฮ) ๐s โง
  ฮTwGl-nat {ฮ} {A} {B} t ๐s =
    ฮ ((ฮนNf โ โชGl-qโซ B โ โชGlTm-โฆฮฑโฆโซ t) (homs (Gls-โฆฮโฆ ฮ) R.ฯ ๐s โ โชGl-uโซ A (VN ๐ง๐ฃ)))
      โกโจ ap ฮ (GlTm-nat t (homs (Gls-โฆฮโฆ ฮ) R.ฯ ๐s โ โชGl-uโซ A (VN ๐ง๐ฃ))) โฉ
    ฮ (GlTm-ฮฑ t โฆ ฮนNfs (โชGls-qโซ ฮ (homs (Gls-โฆฮโฆ ฮ) R.ฯ ๐s))
      โ ((ฮนNf โ โชGl-qโซ A โ โชGl-uโซ A) (VN ๐ง๐ฃ)) โง)
      โกโจ (ฮป i โ ฮ (GlTm-ฮฑ t โฆ ฮนNfs (Gls-q-nat ฮ R.ฯ ๐s i) โ Gl-comp A (VN ๐ง๐ฃ) i โง)) โฉ
    ฮ (GlTm-ฮฑ t โฆ ฮนNfs (โชGls-qโซ ฮ ๐s [ R.ฯ ]NFS) โ ๐ง โง)
      โกโจ (ฮป i โ ฮ (GlTm-ฮฑ t โฆ ฮนNfsLem (โชGls-qโซ ฮ ๐s) R.ฯ i โ ๐ง โง)) โฉ
    ฮ (GlTm-ฮฑ t โฆ ฮนNfs (โชGls-qโซ ฮ ๐s) โ makeRen R.ฯ โ ๐ง โง)
      โกโจ (ฮป i โ ฮ (GlTm-ฮฑ t โฆ ฮนNfs (โชGls-qโซ ฮ ๐s) โ ฯฮท i โ ๐ง โง)) โฉ
    ฮ (GlTm-ฮฑ t โฆ Wโtms (Gl-A A) ((ฮนNfs โ โชGls-qโซ ฮ) ๐s) โง)
      โกโจ ฮnat (GlTm-ฮฑ t) ((ฮนNfs โ โชGls-qโซ ฮ) ๐s) โปยน โฉ
    ฮ (GlTm-ฮฑ t) โฆ (ฮนNfs โ โชGls-qโซ ฮ) ๐s โง
      โ

  ฮTwGl : {ฮ : GlCtx} {A B : GlTy} โ GlTm (ฮ โน A) B โ GlTm ฮ (A โTwGl B)
  ob (GlTm-โฆฮฑโฆ (ฮTwGl {ฮ} {A} {B} t)) ๐s =
    ob (ฮPSh (GlTm-โฆฮฑโฆ t)) ๐s ,
    (ฮป ฮ ฯ ๐ โ
      (ฮนNf โ โชGl-qโซ B โ โชGlTm-โฆฮฑโฆโซ t) (homs (Gls-โฆฮโฆ ฮ) ฯ ๐s โ ๐)
        โกโจ GlTm-nat t (homs (Gls-โฆฮโฆ ฮ) ฯ ๐s โ ๐) โฉ
      GlTm-ฮฑ t โฆ ฮนNfs (โชGls-qโซ ฮ (homs (Gls-โฆฮโฆ ฮ) ฯ ๐s)) โ ฮนNf (โชGl-qโซ A ๐) โง
        โกโจ (ฮป i โ GlTm-ฮฑ t โฆ ฮนNfs (Gls-q-nat ฮ ฯ ๐s i) โ ฮนNf (โชGl-qโซ A ๐) โง) โฉ
      GlTm-ฮฑ t โฆ ฮนNfs (โชGls-qโซ ฮ ๐s [ ฯ ]NFS) โ ฮนNf (โชGl-qโซ A ๐) โง
        โกโจ (ฮป i โ GlTm-ฮฑ t โฆ ฮนNfsLem (โชGls-qโซ ฮ ๐s) ฯ i โ ฮนNf (โชGl-qโซ A ๐) โง) โฉ
      GlTm-ฮฑ t โฆ ฮนNfs (โชGls-qโซ ฮ ๐s) โ makeRen ฯ โ ฮนNf (โชGl-qโซ A ๐) โง
        โกโจ lem (GlTm-ฮฑ t) (ฮนNfs (โชGls-qโซ ฮ ๐s) โ makeRen ฯ) (ฮนNf (โชGl-qโซ A ๐)) โปยน โฉ
      GlTm-ฮฑ t โฆ Wโtms (Gl-A A) (ฮนNfs (โชGls-qโซ ฮ ๐s) โ makeRen ฯ) โง โฆ ๐พ๐น ฮ โ ฮนNf (โชGl-qโซ A ๐) โง
        โกโจ ๐๐๐ฮฒ (GlTm-ฮฑ t โฆ Wโtms (Gl-A A) (ฮนNfs (โชGls-qโซ ฮ ๐s) โ makeRen ฯ) โง)
          (ฮนNf (โชGl-qโซ A ๐)) โปยน โฉ
      ๐๐๐ (ฮ (GlTm-ฮฑ t โฆ Wโtms (Gl-A A) (ฮนNfs (โชGls-qโซ ฮ ๐s) โ makeRen ฯ) โง)) (ฮนNf (โชGl-qโซ A ๐))
        โกโจ (ฮป i โ ๐๐๐ (ฮnat (GlTm-ฮฑ t) (ฮนNfs (โชGls-qโซ ฮ ๐s) โ makeRen ฯ) (~ i))
          (ฮนNf (โชGl-qโซ A ๐))) โฉ
      ๐๐๐ (ฮ (GlTm-ฮฑ t) โฆ ฮนNfs (โชGls-qโซ ฮ ๐s) โ makeRen ฯ โง) (ฮนNf (โชGl-qโซ A ๐))
        โกโจ (ฮป i โ ๐๐๐ (โฆโงโฆโง (ฮ (GlTm-ฮฑ t)) (ฮนNfs (โชGls-qโซ ฮ ๐s)) (makeRen ฯ) (~ i))
          (ฮนNf (โชGl-qโซ A ๐))) โฉ
      ๐๐๐ (ฮ (GlTm-ฮฑ t) โฆ ฮนNfs (โชGls-qโซ ฮ ๐s) โง โฆ makeRen ฯ โง) (ฮนNf (โชGl-qโซ A ๐))
        โกโจ (ฮป i โ ๐๐๐ (ฮTwGl-nat t ๐s (~ i) โฆ makeRen ฯ โง) (ฮนNf (โชGl-qโซ A ๐))) โฉ
      ๐๐๐ ((ฮนNf โ ob (q-AโB A B) โ ob (ฮPSh (GlTm-โฆฮฑโฆ t))) ๐s โฆ makeRen ฯ โง) (ฮนNf (โชGl-qโซ A ๐))
        โกโจ (ฮป i โ ๐๐๐ (ฮนNfLem (ob (q-AโB A B) (ob (ฮPSh (GlTm-โฆฮฑโฆ t)) ๐s)) ฯ (~ i))
          (ฮนNf (โชGl-qโซ A ๐))) โฉ
      ๐๐๐ (ฮนNf ((ob (q-AโB A B) โ ob (ฮPSh (GlTm-โฆฮฑโฆ t))) ๐s [ ฯ ]NF)) (ฮนNf (โชGl-qโซ A ๐))
        โ) where
    lem : {ฮ ฮ : ctx} {A B : ty} (t : tm (ฮ โน A) B) (ฯ : tms ฮ ฮ) (s : tm ฮ A) โ
      t โฆ Wโtms A ฯ โง โฆ ๐พ๐น ฮ โ s โง โก t โฆ ฯ โ s โง
    lem {ฮ} {ฮ} {A} t ฯ s =
      t โฆ Wโtms A ฯ โง โฆ ๐พ๐น ฮ โ s โง
        โกโจ โฆโงโฆโง t (Wโtms A ฯ) (๐พ๐น ฮ โ s) โฉ
      t โฆ Wโtms A ฯ โ (๐พ๐น ฮ โ s) โ ๐ง โฆ ๐พ๐น ฮ โ s โง โง
        โกโจ (ฮป i โ t โฆ Wtmsโ ฯ (๐พ๐น ฮ) s i โ ๐งโฆโง (๐พ๐น ฮ โ s) i โง) โฉ
      t โฆ ฯ โ ๐พ๐น ฮ โ s โง
        โกโจ (ฮป i โ t โฆ ๐พ๐นR ฯ i โ s โง)โฉ
      t โฆ ฯ โ s โง
        โ
  nat (GlTm-โฆฮฑโฆ (ฮTwGl {ฮ} {A} {B} t)) {ฮ} ฯ ๐s =
    subtypeLem (โฆAโBโฆ-sec A B ฮ) (nat (ฮPSh (GlTm-โฆฮฑโฆ t)) ฯ ๐s)
  GlTm-ฮฑ (ฮTwGl t) = ฮ (GlTm-ฮฑ t)
  GlTm-nat (ฮTwGl t) ๐s = ฮTwGl-nat t ๐s

  GlTm-โฆฮฑโฆforget : {ฮ : GlCtx} {A B : GlTy} โ GlTm ฮ (A โTwGl B) โ
    PShMor (Gls-โฆฮโฆ ฮ) (โฆAโฆ-AโB A B)
  ob (GlTm-โฆฮฑโฆforget t) ๐s = fst (ob (GlTm-โฆฮฑโฆ t) ๐s)
  nat (GlTm-โฆฮฑโฆforget t) ฯ ๐s = ap fst (nat (GlTm-โฆฮฑโฆ t) ฯ ๐s)

  AppTwGl : {ฮ : GlCtx} {A B : GlTy} โ GlTm ฮ (A โTwGl B) โ GlTm ฮ A โ GlTm ฮ B
  GlTm-โฆฮฑโฆ (AppTwGl {ฮ} {A} {B} t s) = AppPSh (GlTm-โฆฮฑโฆforget {ฮ} {A} {B} t) (GlTm-โฆฮฑโฆ s)
  GlTm-ฮฑ (AppTwGl t s) = ๐๐๐ (GlTm-ฮฑ t) (GlTm-ฮฑ s)
  GlTm-nat (AppTwGl {ฮ} {A} {B} t s) {ฮ} ๐s =
    (ฮนNf โ โชGl-qโซ B โ ob (fst (โชGlTm-โฆฮฑโฆโซ t ๐s))) (R.๐พ๐น ฮ , โชGlTm-โฆฮฑโฆโซ s ๐s)
      โกโจ snd (โชGlTm-โฆฮฑโฆโซ t ๐s) ฮ (R.๐พ๐น ฮ) (โชGlTm-โฆฮฑโฆโซ s ๐s) โฉ
    ๐๐๐ (ฮนNf (ob (q-AโB A B) (fst (โชGlTm-โฆฮฑโฆโซ t ๐s)) [ R.๐พ๐น ฮ ]NF))
      ((ฮนNf โ โชGl-qโซ A โ โชGlTm-โฆฮฑโฆโซ s) ๐s)
      โกโจ (ฮป i โ ๐๐๐ (ฮนNf ([id]NF (ob (q-AโB A B) (fst (โชGlTm-โฆฮฑโฆโซ t ๐s))) i))
         ((ฮนNf โ โชGl-qโซ A โ โชGlTm-โฆฮฑโฆโซ s) ๐s) ) โฉ
    ๐๐๐ ((ฮนNf โ โชGl-qโซ (A โTwGl B) โ โชGlTm-โฆฮฑโฆโซ t) ๐s) ((ฮนNf โ โชGl-qโซ A โ โชGlTm-โฆฮฑโฆโซ s) ๐s)
      โกโจ (ฮป i โ ๐๐๐ (GlTm-nat t ๐s i) (GlTm-nat s ๐s i)) โฉ
    ๐๐๐ (GlTm-ฮฑ t โฆ (ฮนNfs โ โชGls-qโซ ฮ) ๐s โง) (GlTm-ฮฑ s โฆ (ฮนNfs โ โชGls-qโซ ฮ) ๐s โง)
      โกโจ ๐๐๐โฆโง (GlTm-ฮฑ t) (GlTm-ฮฑ s) ((ฮนNfs โ โชGls-qโซ ฮ) ๐s) โปยน โฉ
    ๐๐๐ (GlTm-ฮฑ t) (GlTm.GlTm-ฮฑ s) โฆ (ฮนNfs โ โชGls-qโซ ฮ) ๐s โง
      โ

  โกGlTmโ : {ฮ : GlCtx} {A B : GlTy} {t s : GlTm ฮ (A โTwGl B)} โ
    ({ฮ : ctx} โ (๐s : secs (Gls-โฆฮโฆ ฮ) ฮ)
      โ fst (ob (GlTm-โฆฮฑโฆ t) ๐s) โก fst (ob (GlTm-โฆฮฑโฆ s) ๐s)) โ
    GlTm-ฮฑ t โก GlTm-ฮฑ s โ t โก s
  โกGlTmโ {ฮ} {A} {B} {t} {s} p q =
    โกGlTm (โกPShMor (ฮป {ฮ} ๐s โ subtypeLem (โฆAโBโฆ-sec A B ฮ) (p ๐s))) q

  WโTwGl-โฆฮฑsโฆ : {ฮ ฮ : GlCtx} (A : GlTy) (ฯ : GlTms ฮ ฮ) โ
    GlTms-โฆฮฑsโฆ (T.Wโtms A ฯ) โก P.Wโtms (Gl-โฆAโฆ A) (GlTms-โฆฮฑsโฆ ฯ)
  WโTwGl-โฆฮฑsโฆ {ฮ} {ฮ} A ฯ =
    GlTms-โฆฮฑsโฆ (ฯ T.โ T.ฯ โ T.๐ง)
      โกโจ (ฮป i โ Gl-โฆฮฑsโฆโ ฯ (T.ฯ {ฮ} {A}) i โ GlTm-โฆฮฑโฆ (T.๐ง {ฮ} {A})) โฉ
    GlTms-โฆฮฑsโฆ ฯ P.โ GlTms-โฆฮฑsโฆ T.ฯ โ GlTm-โฆฮฑโฆ (T.๐ง {ฮ} {A})
      โกโจ (ฮป i โ GlTms-โฆฮฑsโฆ ฯ P.โ ฯ๐ธ๐๐? (idTwGl-โฆฮฑsโฆ (ฮ โน A) i) โ ๐ง๐ธ๐๐? (idTwGl-โฆฮฑsโฆ (ฮ โน A) i)) โฉ
    P.Wโtms (Gl-โฆAโฆ A) (GlTms-โฆฮฑsโฆ ฯ)
      โ

  WโTwGl-ฮฑs : {ฮ ฮ : GlCtx} (A : GlTy) (ฯ : GlTms ฮ ฮ) โ
    GlTms-ฮฑs (T.Wโtms A ฯ) โก Wโtms (Gl-A A) (GlTms-ฮฑs ฯ)
  WโTwGl-ฮฑs {ฮ} {ฮ} A ฯ =
    GlTms-ฮฑs (ฯ T.โ T.ฯ โ T.๐ง)
      โกโจ (ฮป i โ Gl-ฮฑsโ ฯ (T.ฯ {ฮ} {A}) i โ GlTm-ฮฑ (T.๐ง {ฮ} {A})) โฉ
    GlTms-ฮฑs ฯ โ GlTms-ฮฑs T.ฯ โ GlTm-ฮฑ (T.๐ง {ฮ} {A})
      โกโจ (ฮป i โ GlTms-ฮฑs ฯ โ ฯ๐ธ๐๐? (idTwGl-ฮฑs (ฮ โน A) i) โ ๐ง๐ธ๐๐? (idTwGl-ฮฑs (ฮ โน A) i)) โฉ
    Wโtms (Gl-A A) (GlTms-ฮฑs ฯ)
      โ

  ฮnatTwGl : {ฮ ฮ : T.ctx} {A B : T.ty} (t : T.tm (ฮ โน A) B) (ฯ : T.tms ฮ ฮ) โ
    ฮTwGl {ฮ} {A} {B} t T.โฆ ฯ โง โก ฮTwGl {ฮ} {A} {B} (t T.โฆ T.Wโtms A ฯ โง)
  ฮnatTwGl {A = A} {B} t ฯ =
    โกGlTmโ {A = A} {B}
      (ฮป {ฮฃ} ๐s โ
        (ob (ฮPSh (GlTm-โฆฮฑโฆ t)) โ โชGlTms-โฆฮฑsโฆโซ ฯ) ๐s
          โกโจ (ฮป i โ ob (ฮnatPSh (GlTm-โฆฮฑโฆ t) (GlTms-โฆฮฑsโฆ ฯ) i) ๐s) โฉ
        ob (ฮPSh (GlTm-โฆฮฑโฆ t P.โฆ P.Wโtms (Gl-โฆAโฆ A) (GlTms-โฆฮฑsโฆ ฯ) โง)) ๐s
          โกโจ (ฮป i โ ob (ฮPSh (GlTm-โฆฮฑโฆ t P.โฆ WโTwGl-โฆฮฑsโฆ A ฯ (~ i) โง)) ๐s) โฉ
        ob (ฮPSh (GlTm-โฆฮฑโฆ (t T.โฆ T.Wโtms A ฯ โง))) ๐s
          โ)
      (ฮ (GlTm-ฮฑ t) โฆ GlTms-ฮฑs ฯ โง
        โกโจ ฮnat (GlTm-ฮฑ t) (GlTms-ฮฑs ฯ) โฉ
      ฮ (GlTm-ฮฑ t โฆ Wโtms (Gl-A A) (GlTms-ฮฑs ฯ) โง)
        โกโจ (ฮป i โ ฮ (GlTm-ฮฑ t โฆ WโTwGl-ฮฑs A ฯ (~ i) โง)) โฉ
      ฮ (GlTm-ฮฑ (t T.โฆ T.Wโtms A ฯ โง))
        โ)

  AppฮฒGlTm : {ฮ : GlCtx} {A B : GlTy} (t : GlTm (ฮ โน A) B) (s : GlTm ฮ A) โ
    AppTwGl {ฮ} {A} {B} (ฮTwGl {ฮ} {A} {B} t) s โก t T.โฆ T.๐พ๐น ฮ โ s โง
  AppฮฒGlTm {ฮ} {A} {B} t s =
    โกGlTm
      (โกPShMor
        (ฮป {ฮ} ๐s โ
          โชGlTm-โฆฮฑโฆโซ t (homs (Gls-โฆฮโฆ ฮ) (R.๐พ๐น ฮ) ๐s โ โชGlTm-โฆฮฑโฆโซ s ๐s)
            โกโจ ap (ฮป x โ ob x ๐s) (AppฮฒPSh (GlTm-โฆฮฑโฆ t) (GlTm-โฆฮฑโฆ s)) โฉ
          ob (GlTm-โฆฮฑโฆ t P.โฆ P.๐พ๐น (Gls-โฆฮโฆ ฮ) โ GlTm-โฆฮฑโฆ s โง) ๐s
            โกโจ (ฮป i โ ob (GlTm-โฆฮฑโฆ t P.โฆ idTwGl-โฆฮฑsโฆ ฮ (~ i) โ GlTm-โฆฮฑโฆ s โง) ๐s) โฉ
          ob (GlTm-โฆฮฑโฆ (t T.โฆ T.๐พ๐น ฮ โ s โง)) ๐s
            โ))
      (๐๐๐ (ฮ (GlTm-ฮฑ t)) (GlTm-ฮฑ s)
        โกโจ ๐๐๐ฮฒ (GlTm-ฮฑ t) (GlTm-ฮฑ s) โฉ
      GlTm-ฮฑ t โฆ ๐พ๐น (Gls-ฮ ฮ) โ GlTm-ฮฑ s โง
        โกโจ (ฮป i โ GlTm-ฮฑ t โฆ idTwGl-ฮฑs ฮ (~ i) โ GlTm-ฮฑ s โง) โฉ
      GlTm-ฮฑ (t T.โฆ T.๐พ๐น ฮ โ s โง)
        โ)

  ๐ด๐๐TwGl : {ฮ : GlCtx} {A B : GlTy} โ GlTm ฮ (A โTwGl B) โ GlTm (ฮ โน A) B
  ๐ด๐๐TwGl {ฮ} {A} {B} t = AppTwGl {ฮ โน A} {A} {B} (t T.โฆ T.ฯ โง) (T.๐ง)

  TwGlโฆโง-โฆฮฑsโฆforget : {ฮ ฮ : GlCtx} {A B : GlTy} (t : GlTm ฮ (A โTwGl B)) (ฯ : GlTms ฮ ฮ) โ
    GlTm-โฆฮฑโฆforget {ฮ} {A} {B} (t T.โฆ ฯ โง) โก (GlTm-โฆฮฑโฆforget {ฮ} {A} {B} t P.โฆ GlTms-โฆฮฑsโฆ ฯ โง)
  TwGlโฆโง-โฆฮฑsโฆforget {ฮ} {ฮ} {A} {B} t ฯ =
    โกPShMorโ {Gls-โฆฮโฆ ฮ} {Gl-โฆAโฆ A} {Gl-โฆAโฆ B} (ฮป ๐s ฯ ๐ โ refl)

  AppฮทGlTm : {ฮ : T.ctx} {A B : T.ty} (t : T.tm ฮ (A โTwGl B)) โ
    t โก ฮTwGl {ฮ} {A} {B} (๐ด๐๐TwGl {ฮ} {A} {B} t)
  AppฮทGlTm {ฮ} {A} {B} t =
    โกGlTmโ {A = A} {B}
      (ฮป ๐s โ
        fst (ob (GlTm-โฆฮฑโฆ t) ๐s)
          โกโจ ap (ฮป x โ ob x ๐s) (AppฮทPSh {Gls-โฆฮโฆ ฮ} {Gl-โฆAโฆ A} {Gl-โฆAโฆ B}
            (GlTm-โฆฮฑโฆforget {ฮ} {A} {B} t)) โฉ
        ob (ฮPSh (AppPSh {ฮฑ = Gl-โฆAโฆ A} {Gl-โฆAโฆ B}
          (GlTm-โฆฮฑโฆforget {ฮ} {A} {B} t P.โฆ P.ฯ โง) P.๐ง)) ๐s
          โกโจ (ฮป i โ ob (ฮPSh (AppPSh {ฮฑ = Gl-โฆAโฆ A} {Gl-โฆAโฆ B}
            (GlTm-โฆฮฑโฆforget {ฮ} {A} {B} t P.โฆ ฯ๐ธ๐๐? (idTwGl-โฆฮฑsโฆ (ฮ โน A) (~ i)) โง) P.๐ง)) ๐s) โฉ
        ob (ฮPSh (AppPSh {ฮฑ = Gl-โฆAโฆ A} {Gl-โฆAโฆ B}
          (GlTm-โฆฮฑโฆforget {ฮ} {A} {B} t P.โฆ GlTms-โฆฮฑsโฆ T.ฯ โง) P.๐ง)) ๐s
          โกโจ (ฮป i โ ob (ฮPSh (AppPSh {ฮฑ = Gl-โฆAโฆ A} {Gl-โฆAโฆ B}
            (TwGlโฆโง-โฆฮฑsโฆforget {ฮ โน A} {ฮ} {A} {B} t T.ฯ (~ i)) P.๐ง)) ๐s) โฉ
        ob (ฮPSh (AppPSh {ฮฑ = Gl-โฆAโฆ A} {Gl-โฆAโฆ B}
          (GlTm-โฆฮฑโฆforget {ฮ โน A} {A} {B} (t T.โฆ T.ฯ โง)) P.๐ง)) ๐s
          โ)
      (GlTm-ฮฑ t
        โกโจ ๐๐๐ฮท (GlTm-ฮฑ t) โฉ
      ฮ (๐๐๐ (GlTm-ฮฑ t โฆ ฯ โง) ๐ง)
        โกโจ (ฮป i โ ฮ (๐๐๐ (GlTm-ฮฑ t โฆ ฯ๐ธ๐๐? (idTwGl-ฮฑs (ฮ โน A) (~ i)) โง) ๐ง)) โฉ
      ฮ (๐๐๐ (GlTm-ฮฑ t โฆ GlTms-ฮฑs T.ฯ โง) ๐ง)
        โ)

  instance
    isCCCTwGl : CCC TwGl
    CCC._โ_ isCCCTwGl = _โTwGl_
    CCC.ฮ isCCCTwGl {ฮ} {A} {B} = ฮTwGl {ฮ} {A} {B}
    CCC.๐๐๐ isCCCTwGl {ฮ} {A} {B} = AppTwGl {ฮ} {A} {B}
    CCC.ฮnat isCCCTwGl {ฮ} {ฮ} {A} {B} t ฯ = ฮnatTwGl {ฮ} {ฮ} {A} {B} t ฯ
    CCC.๐๐๐ฮฒ isCCCTwGl {ฮ} {A} {B} t s = AppฮฒGlTm {ฮ} {A} {B} t s
    CCC.๐๐๐ฮท isCCCTwGl {ฮ} {A} {B} t = AppฮทGlTm {ฮ} {A} {B} t
  
