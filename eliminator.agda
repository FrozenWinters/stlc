{-# OPTIONS --cubical #-}

module eliminator where

open import lists
open import contextual
open import ccc
open import functor
open import syn

open import Agda.Builtin.Char
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

-- We construct a canonical contextual functor from ΟΞΉΞ½ to any CCC π

module Eliminator {ββ ββ ββ} (π : Contextual ββ ββ) β¦ CCCπ : CCC π β¦
                  {X : Type ββ} (base : X β Contextual.ty π) where
  open Syn X
  open Contextual π
  private
    module S = Contextual ΟΞΉΞ½
    module R = Contextual S.ΟΞ΅Ξ½
  open CCC CCCπ

  interpTy : Ty β ty
  interpTy (Base x) = base x
  interpTy (A β B) = (interpTy A) β (interpTy B)

  interpCtx : Ctx β ctx
  interpCtx Ξ = mapπΆπ‘π₯ interpTy Ξ

  trVar = trπππ interpTy

  interpVar : {Ξ : Ctx} {A : Ty} (v : Var Ξ A) β tm (interpCtx Ξ) (interpTy A)
  interpVar v = makeVar (trπππ interpTy v)

  interpRen : {Ξ Ξ : Ctx} (Ο : Ren Ξ Ξ) β tms (interpCtx Ξ) (interpCtx Ξ)
  interpRen = mapπΈππ β interpVar

  interpIdRen : {Ξ : Ctx} β interpRen (idπππ Ξ) β‘ πΎπΉ (interpCtx Ξ)
  interpIdRen {Ξ} =
    mapπΈππ β (Ξ» v β makeVar (trπππ interpTy v)) (idπππ Ξ)
      β‘β¨ mapπΈππ compβ makeVar (trπππ interpTy) (idπππ Ξ) β»ΒΉ β©
    makeRen (trπππ interpTy (idπππ Ξ))
      β‘β¨ (Ξ» i β makeRen (trId interpTy Ξ i)) β©
    makeRen (idπππ (mapπΆπ‘π₯ interpTy Ξ))
      β‘β¨ πΎπΉΞ·β β©
    πΎπΉ (mapπΆπ‘π₯ interpTy Ξ)
      β

  interpWβRen : {Ξ Ξ : Ctx} {A : Ty} (Ο : Ren Ξ Ξ) β
    interpRen (Wβπππ A Ο) β‘ interpRen Ο β Ο
  interpWβRen ! = refl
  interpWβRen {Ξ} {Ξ} {A} (Ο β v) i = interpWβRen {A = A} Ο i β makeπ π£ (trπππ interpTy v) i

  Οlem : {Ξ : Ctx} {A : Ty} β interpRen (Wβπππ A (idπππ Ξ)) β‘ Ο
  Οlem {Ξ} {A} =
    interpRen (Wβπππ A (idπππ Ξ))
      β‘β¨ interpWβRen (idπππ Ξ) β©
    interpRen (idπππ Ξ) β Ο
      β‘β¨ ap (_β Ο) interpIdRen β©
    πΎπΉ (interpCtx Ξ) β Ο
      β‘β¨ πΎπΉL Ο β©
    Ο
      β

  interpTm  : {Ξ : Ctx} {A : Ty} (t : Tm Ξ A) β tm (interpCtx Ξ) (interpTy A)

  {-# TERMINATING #-}
  interpTms : {Ξ Ξ : Ctx} (Ο : Tms Ξ Ξ) β tms  (interpCtx Ξ)  (interpCtx Ξ)
  interpTms = mapπΈππ β interpTm

  interpVarify : {Ξ Ξ : Ctx} (Ο : Ren Ξ Ξ) β
    interpTms (varify Ο) β‘ interpRen Ο

  interpId : {Ξ : Ctx} β interpTms (idTms Ξ) β‘ πΎπΉ (interpCtx Ξ)
  interpId {Ξ} =
   interpTms (varify (idπππ Ξ))
     β‘β¨ interpVarify (idπππ Ξ) β©
   interpRen (idπππ Ξ)
     β‘β¨ interpIdRen β©
   πΎπΉ (interpCtx Ξ)
     β

  ΟlemTms : {Ξ : Ctx} {A : Ty} β interpTms (S.Ο {Ξ} {A}) β‘ Ο
  ΟlemTms {Ξ} {A} =
    interpTms (S.Ο {Ξ} {A})
      β‘β¨ interpVarify (Wβπππ A (idπππ Ξ)) β©
    interpRen (Wβπππ A (idπππ Ξ))
      β‘β¨ Οlem β©
    Ο
      β

  interpβTms : {Ξ Ξ Ξ£ : Ctx} (Ο : Tms Ξ Ξ£) (Ο : Tms Ξ Ξ) β
    interpTms (Ο βTms Ο) β‘ interpTms Ο β interpTms Ο

  interpWβTm : {Ξ : Ctx} (A : Ty) {B : Ty} (t : Tm Ξ B) β
    interpTm (WβTm A t) β‘ interpTm t β¦ Ο β§

  interpWβTms : {Ξ Ξ : Ctx} (A : Ty) (Ο : Tms Ξ Ξ) β
    interpTms (WβTms A Ο) β‘ interpTms Ο β Ο
  interpWβTms A ! = !Ξ· (! β Ο)
  interpWβTms A (Ο β t) =
    interpTms (WβTms A Ο) β interpTm (WβTm A t)
      β‘β¨ (Ξ» i β interpWβTms A Ο i β interpWβTm A t i) β©
    (interpTms Ο β Ο) β (interpTm t β¦ Ο β§)
      β‘β¨ ββ (interpTms Ο) (interpTm t) Ο β»ΒΉ β©
    interpTms Ο β interpTm t β Ο
      β

  interpTm (V v) =
    interpVar v
  interpTm (Lam t) =
    Ξ (interpTm t)
  interpTm (App t s) =
    πππ (interpTm t) (interpTm s)
  interpTm (t [ Ο ]) =
    interpTm t β¦ interpTms Ο β§

  interpTm (Ξ² {Ξ} t s i) =
    (πππ (Ξ (interpTm t)) (interpTm s)
      β‘β¨ πππΞ² (interpTm t) (interpTm s) β©
    interpTm t β¦ πΎπΉ (interpCtx Ξ) β interpTm s β§
      β‘β¨ (Ξ» j β interpTm t β¦ interpId (~ j) β interpTm s β§) β©
    interpTm t β¦ interpTms (idTms Ξ) β interpTm s β§
      β) i
  interpTm (Ξ· {Ξ} {A} t i) =
    (interpTm t
      β‘β¨ πππΞ· (interpTm t) β©
    Ξ (πππ (interpTm t β¦ Ο β§) π§)
      β‘β¨ (Ξ» i β Ξ (πππ (interpTm t β¦ ΟlemTms {Ξ} {A} (~ i) β§) π§)) β©
    Ξ (πππ (interpTm (t [ S.Ο ])) π§)
      β) i
  interpTm (π§π£[] Ο t i) =
    π§β¦β§ (interpTms (Ο β t)) i
  interpTm (π π£[] v Ο t i) =
    π π£β¦β§ (trπππ interpTy v) (interpTms Ο) (interpTm t) i
  interpTm (Lam[] {A = A} t Ο i) =
    (Ξ (interpTm t) β¦ interpTms Ο β§
      β‘β¨ Ξnat (interpTm t) (interpTms Ο) β©
    Ξ (interpTm t β¦ interpTms Ο β Ο β π§ β§)
      β‘β¨ (Ξ» j β Ξ (interpTm t β¦ interpWβTms A Ο (~ j) β π§ β§)) β©
    Ξ (interpTm t β¦ interpTms (WβTms A Ο) β π§ β§)
      β) i
  interpTm (App[] t s Ο i) =
    πππβ¦β§ (interpTm t) (interpTm s) (interpTms Ο) i
  interpTm ([][] t Ο Ο i) =
    (interpTm t β¦ interpTms Ο β§ β¦ interpTms Ο β§
      β‘β¨ β¦β§β¦β§ (interpTm t) (interpTms Ο) (interpTms Ο) β©
    interpTm t β¦ interpTms Ο β interpTms Ο β§
      β‘β¨ ap (interpTm t β¦_β§) (interpβTms Ο Ο β»ΒΉ) β©
    interpTm t β¦ interpTms (Ο βTms Ο) β§
      β) i
  interpTm (trunc t s p q i j) =
    isSetβSquareP (Ξ» i j β isSetTm)
      (Ξ» k β interpTm (p k))
      (Ξ» k β interpTm (q k))
      (Ξ» k β interpTm t)
      (Ξ» k β interpTm s) i j

  interpVarify ! = refl
  interpVarify (Ο β v) = ap (_β interpVar v) (interpVarify Ο)

  interpWβTm {Ξ} A t = ap (interpTm t β¦_β§) ΟlemTms

  interpβTms ! Ο = !Ξ· (! β interpTms Ο)
  interpβTms (Ο β t) Ο = ap (_β interpTm (t [ Ο ])) (interpβTms Ο Ο)

  open ContextualFunctor

  elim : ContextualFunctor ΟΞΉΞ½ π
  CF-ty elim = interpTy
  CF-tm elim = interpTm
  CF-id elim = interpId
  CF-sub elim t Ο = refl

  open CCCPreserving

  CCCPres : CCCPreserving elim
  pres-β CCCPres A B = refl
  pres-π΄ππ CCCPres {Ξ} {A} {B} t i =
    πππ (transportRefl (interpTm t) (~ i) β¦ ΟlemTms {Ξ} {A} i β§) π§

  BasePreserving : ContextualFunctor ΟΞΉΞ½ π β Type (ββ β ββ)
  BasePreserving F = (x : X) β CF-ty F (Base x) β‘ base x

  BasePres : BasePreserving elim
  BasePres c = refl

  module UP {F : ContextualFunctor ΟΞΉΞ½ π} (pβ : CCCPreserving F) (pβ : BasePreserving F) where
    UP-ty' : (A : Ty) β CF-ty F A β‘ CF-ty elim A
    UP-ty' (Base c) = pβ c
    UP-ty' (A β B) = pres-β pβ A B β (Ξ» i β UP-ty' A i β UP-ty' B i)

    UP-ty : CF-ty F β‘ CF-ty elim
    UP-ty = funExt UP-ty'

    UP-ctx : CF-ctx F β‘ CF-ctx elim
    UP-ctx i = mapπΆπ‘π₯ (UP-ty i)    

    {-# TERMINATING #-}
    UP-tm' : {Ξ : Ctx} {A : Ty} (t : Tm Ξ A) β
      PathP (Ξ» i β tm (UP-ctx i Ξ) (UP-ty i A)) (CF-tm F t) (CF-tm elim t)
    UP-sub' : {Ξ Ξ : Ctx} (Ο : Tms Ξ Ξ) β
      PathP (Ξ» i β tms (UP-ctx i Ξ) (UP-ctx i Ξ)) (CF-tms F Ο) (CF-tms elim Ο)

    UP-sub' ! i = !
    UP-sub' (Ο β t) i = UP-sub' Ο i β UP-tm' t i

    transpπππ : {P : Ty β ty} (a : CF-ty F β‘ P) β
      {Ξ : Ctx} {A B : Ty} (t : Tm Ξ (A β B)) (s : Tm Ξ A) β
      transport (Ξ» i β tm (mapπΆπ‘π₯ (a i) Ξ) (a i B)) (CF-tm F (App t s))
        β‘ πππ
          ((transport (Ξ» i β tm (mapπΆπ‘π₯ (a i) Ξ)
            ((pres-β pβ A B β (Ξ» j β a j A β a j B)) i)) (CF-tm F t)))
          (transport (Ξ» i β tm (mapπΆπ‘π₯ (a i) Ξ) (a i A)) (CF-tm F s))
    transpπππ a {Ξ} {A} {B} t s =
      J
        (Ξ» P b β
          transport (Ξ» i β tm (mapπΆπ‘π₯ (b i) Ξ) (b i B)) (CF-tm F (App t s))
          β‘ πππ
            ((transport (Ξ» i β tm (mapπΆπ‘π₯ (b i) Ξ)
              ((pres-β pβ A B β (Ξ» j β b j A β b j B)) i)) (CF-tm F t)))
            (transport (Ξ» i β tm (mapπΆπ‘π₯ (b i) Ξ) (b i A)) (CF-tm F s)))
        (transport (Ξ» i β tm (mapπΆπ‘π₯ (refl i) Ξ) (refl {x = CF-ty F} i B)) (CF-tm F (App t s))
          β‘β¨ transportRefl (CF-tm F (App t s)) β©
        CF-tm F (App t s)
          β‘β¨ pres-πππ pβ t s β©
        πππ (transport (Ξ» i β tm (CF-ctx F Ξ) (pres-β pβ A B i)) (CF-tm F t)) (CF-tm F s)
          β‘β¨ (Ξ» j β πππ
            (transport (Ξ» i β tm (CF-ctx F Ξ) (rUnit (pres-β pβ A B) j i)) (CF-tm F t))
            (transportRefl (CF-tm F s) (~ j))) β©
        πππ (transport (Ξ» i β tm (CF-ctx F Ξ) ((pres-β pβ A B β refl) i)) (CF-tm F t))
          (transport refl (CF-tm F s))
          β)
        a

    UP-tm' {Ξ} {A} (V v) =
      (CF-tm F (V v)
        β‘β¨ (Ξ» i β CF-tm F (V (R.πΎπΉβ¦β§ v (~ i)))) β©
      CF-tm F (V (derive (idπππ Ξ) v))
        β‘β¨ ap (CF-tm F) (deriveMap V (idπππ Ξ) v β»ΒΉ) β©
      CF-tm F (S.makeVar v)
        β‘β¨ CF-Var F v β©
      makeVar (trπππ (CF-ty F) v)
        β) β (Ξ» i β makeVar (trπππ (UP-ty i) v))
    UP-tm' (Lam {Ξ} {A} {B} t) =
      toPathP
        (transport (Ξ» j β tm (UP-ctx j Ξ) (UP-ty j (A β B))) (CF-tm F (Lam t))
          β‘β¨ (Ξ» i β transport (Ξ» j β tm (lUnit (UP-ctx) i j Ξ)
            (UP-ty j (A β B))) (CF-tm F (Lam t))) β©
        transport (Ξ» j β tm ((refl β (Ξ» i β UP-ctx i Ξ)) j) (UP-ty' (A β B) j)) (CF-tm F (Lam t))
          β‘β¨ transport-tm {tm = tm} refl (pres-β pβ A B) (Ξ» j β UP-ctx j Ξ)
            (Ξ» j β UP-ty' A j β UP-ty' B j) (CF-tm F (Lam t)) β»ΒΉ β©
        transport (Ξ» j β tm (UP-ctx j Ξ) (UP-ty' A j β UP-ty' B j))
          (transport (Ξ» i β tm (mapπΆπ‘π₯ (CF-ty F) Ξ) (pres-β pβ A B i)) (CF-tm F (Lam t)))
          β‘β¨ (Ξ» i β transport (Ξ» j β tm (UP-ctx j Ξ) (UP-ty' A j β UP-ty' B j))
            (transport (Ξ» i β tm (mapπΆπ‘π₯ (CF-ty F) Ξ) (pres-β pβ A B i))
              (transportRefl (CF-tm F (Lam t)) (~ i)))) β©
        transport (Ξ» j β tm (UP-ctx j Ξ) (UP-ty' A j β UP-ty' B j))
          (transport (Ξ» i β tm (mapπΆπ‘π₯ (CF-ty F) Ξ) (pres-β pβ A B i))
            (transport refl (CF-tm F (Lam t))))
          β‘β¨ fromPathP (compPathP (pres-Ξ pβ t) (Ξ» i β Ξ (UP-tm' t i))) β©
        Ξ (interpTm t)
          β)
    UP-tm' (App {Ξ} {A} {B} t s) =
      toPathP
        (transport (Ξ» i β tm (UP-ctx i Ξ) (UP-ty i B)) (CF-tm F (App t s))
          β‘β¨ transpπππ UP-ty t s β©
        πππ (transport (Ξ» i β tm (mapπΆπ‘π₯ (UP-ty i) Ξ) (UP-ty' (A β B) i)) (CF-tm F t))
          (transport (Ξ» i β tm (mapπΆπ‘π₯ (UP-ty i) Ξ) (UP-ty i A)) (CF-tm F s))
          β‘β¨ (Ξ» i β πππ (fromPathP (UP-tm' t) i) (fromPathP (UP-tm' s) i)) β©
        πππ (interpTm t) (interpTm s)
          β)
    UP-tm' (t [ Ο ]) =
      (CF-sub F tΒ Ο β (Ξ» i β UP-tm' t i β¦ UP-sub' Ο i β§)) β· CF-sub elim tΒ Ο β»ΒΉ
    UP-tm' {Ξ} (Ξ² t s i) =
      isSetβSquareP (Ξ» i j β isSetTm)
        (UP-tm' (App (Lam t) s))
        (UP-tm' (t [ idTms Ξ β s ]))
        (Ξ» k β CF-tm F (Ξ² t s k))
        (Ξ» k β CF-tm elim (Ξ² t s k)) i
    UP-tm' (Ξ· t i) =
      isSetβSquareP (Ξ» i j β isSetTm)
        (UP-tm' t)
        (UP-tm' (Lam (App (t [ varify (Contextual.Ο πππ) ]) (V π§π£))))
        (Ξ» k β CF-tm F (Ξ· t k))
        (Ξ» k β CF-tm elim (Ξ· t k)) i
    UP-tm' (π§π£[] Ο t i) =
      isSetβSquareP (Ξ» i j β isSetTm)
        (UP-tm' (V π§π£ [ Ο β t ]))
        (UP-tm' t)
        (Ξ» k β CF-tm F (π§π£[] Ο t k))
        (Ξ» k β CF-tm elim (π§π£[] Ο t k)) i
    UP-tm' (π π£[] v Ο t i) =
      isSetβSquareP (Ξ» i j β isSetTm)
        (UP-tm' (V (π π£ v) [ Ο β t ]))
        (UP-tm' (V v [ Ο ]))
        (Ξ» k β CF-tm F (π π£[] v Ο t k))
        (Ξ» k β CF-tm elim (π π£[] v Ο t k)) i
    UP-tm' (Lam[] t Ο i) =
      isSetβSquareP (Ξ» i j β isSetTm)
        (UP-tm' (Lam t [ Ο ]))
        (UP-tm' (Lam (t [ WβTms _ Ο ])))
        (Ξ» k β CF-tm F (Lam[] t Ο k))
        (Ξ» k β CF-tm elim (Lam[] t Ο k)) i
    UP-tm' (App[] t s Ο i) =
      isSetβSquareP (Ξ» i j β isSetTm)
        (UP-tm' (App t s [ Ο ]))
        (UP-tm' (App (t [ Ο ]) (s [ Ο ])))
        (Ξ» k β CF-tm F (App[] t s Ο k))
        (Ξ» k β CF-tm elim (App[] t s Ο k)) i
    UP-tm' ([][] t Ο Ο i) =
      isSetβSquareP (Ξ» i j β isSetTm)
        (UP-tm' (t [ Ο ] [ Ο ]))
        (UP-tm' (t [ Ο βTms Ο ]))
        (Ξ» k β CF-tm F ([][] t Ο Ο k))
        (Ξ» k β CF-tm elim ([][] t Ο Ο k)) i
    UP-tm' {Ξ} {A} (trunc t s p q i j) =
      isSetβSquareP
        (Ξ» i j β
          isOfHLevelPathP {A = Ξ» k β tm (UP-ctx k Ξ) (UP-ty k A)} 2 isSetTm
            (CF-tm F (trunc t s p q i j))
            (CF-tm elim (trunc t s p q i j)))
        (Ξ» k β UP-tm' (p k))
        (Ξ» k β UP-tm' (q k))
        (Ξ» k β UP-tm' t)
        (Ξ» k β UP-tm' s) i j

    UP-tm : PathP (Ξ» i β {Ξ : Ctx} {A : Ty} β Tm Ξ A β tm (UP-ctx i Ξ) (UP-ty i A))
                  (CF-tm F) (CF-tm elim)
    UP-tm i t = UP-tm' t i

    UP : F β‘ elim
    CF-ty (UP i) = UP-ty i
    CF-tm (UP i) = UP-tm i
    CF-id (UP i) {Ξ = Ξ} =
      isSetβSquareP (Ξ» i j β isSetTms)
        (CF-id F)
        interpId
        (Ξ» k β mapπΈππ β (UP-tm k) (idTms Ξ))
        (Ξ» k β πΎπΉ (mapπΆπ‘π₯ (UP-ty k) Ξ)) i
    CF-sub (UP i) t Ο =
      isSetβSquareP (Ξ» i j β isSetTm)
        (CF-sub F t Ο)
        (Ξ» k β interpTm t β¦ interpTms Ο β§)
        (Ξ» k β UP-tm k (t [ Ο ]))
        (Ξ» k β UP-tm k t β¦ mapπΈππ β (UP-tm k) Ο β§) i

module Initial {β} (X : Type β) where
  open Syn X

  ΟΞΉΞ½Initial : InitialCCC ΟΞΉΞ½ (Ξ» c β Base c)
  ΟΞΉΞ½Initial π base = initIn elim CCCPres BasePres (Ξ» F pβ pβ β UP.UP pβ pβ)
    where
      open Eliminator π base
