{-# OPTIONS --cubical --allow-unsolved-metas #-}

module psh where

open import lists
open import contextual
open import ccc

open import Cubical.Data.Sigma

module Presheaf {β : Level} (π : Category β β) where
  open Category π

  record PSh : Type (lsuc β) where
    field
      sec : ππ β Type β
      isSetSec : {A : ππ} β isSet (sec A)
      hom : {A B : ππ} β πππ A B β sec B β sec A
      id-hom : {A : ππ} (π : sec A) β
        hom (πΎπΉ A) π β‘ π
      β-hom : {A B C : ππ} (f : πππ B C) (g : πππ A B) (π : sec C) β
        hom (f β g) π β‘ hom g (hom f π)

  open PSh

  PShs = πΆπ‘π₯ PSh

  secs : PShs β ππ β Type (lsuc β)
  secs Ξ³ A = πΈππ  (Ξ» Ξ± β sec Ξ± A) Ξ³

  homs : (Ξ³ : PShs) {A B : ππ} β πππ A B β secs Ξ³ B β secs Ξ³ A
  homs Ξ³ f πs = mapπΈππ  (Ξ» {Ξ±} β hom Ξ± f) πs

  id-homs : (Ξ³ : PShs) {A : ππ} (πs : secs Ξ³ A) β
    homs Ξ³ (πΎπΉ A) πs β‘ πs
  id-homs β ! = refl
  id-homs (Ξ³ βΉ Ξ±) (πs β π) i = id-homs Ξ³ πs i β id-hom Ξ± π i

  β-homs : (Ξ³ : PShs) {A B C : ππ} (f : πππ B C) (g : πππ A B) (πs : secs Ξ³ C) β
    homs Ξ³ (f β g) πs β‘ homs Ξ³ g (homs Ξ³ f πs)
  β-homs β f g ! = refl
  β-homs (Ξ³ βΉ Ξ±) f g (πs β π) i = β-homs Ξ³ f g πs i β β-hom Ξ± f g π i

  record PShMor (Ξ³ : PShs) (Ξ± : PSh) : Type (lsuc β) where
    field
      ob : {A : ππ} β secs Ξ³ A β sec Ξ± A
      nat : {A B : ππ} (f : πππ A B) (πs : secs Ξ³ B) β
        ob (homs Ξ³ f πs) β‘ hom Ξ± f (ob πs)

  open PShMor

  β‘PShMor : {Ξ³ : PShs} {Ξ± : PSh} {t s : PShMor Ξ³ Ξ±} β
    ({A : ππ} (πs : secs Ξ³ A) β ob t πs β‘ ob s πs) β t β‘ s
  ob (β‘PShMor p i) πs = p πs i
  nat (β‘PShMor {Ξ³} {Ξ±} {t} {s} p i) f πs j =
    isSetβSquareP (Ξ» i j β isSetSec Ξ±)
      (nat t f πs)
      (nat s f πs)
      (p (homs Ξ³ f πs))
      (Ξ» k β hom Ξ± f (p πs k)) i j

  PShMors = πππ  PShMor

  obs : {Ξ³ Ξ΄ : PShs} β PShMors Ξ³ Ξ΄ β {A : ππ} β secs Ξ³ A β secs Ξ΄ A
  obs ! πs = !
  obs (Ο β t) πs = obs Ο πs β ob t πs

  nats : {Ξ³ Ξ΄ : PShs} (Ο : PShMors Ξ³ Ξ΄) {A B : ππ} (f : πππ A B) (πs : secs Ξ³ B) β
    obs Ο (homs Ξ³ f πs) β‘ homs Ξ΄ f (obs Ο πs)
  nats ! f πs = refl
  nats (Ο β t) f πs i = nats Ο f πs i β nat t f πs i

  infixl 30 _[_]PSh
  _[_]PSh : {Ξ³ Ξ΄ : PShs} {Ξ± : PSh} β PShMor Ξ΄ Ξ± β PShMors Ξ³ Ξ΄ β PShMor Ξ³ Ξ±
  ob (t [ Ο ]PSh) πs = ob t (obs Ο πs)
  nat (_[_]PSh {Ξ³} {Ξ΄} {Ξ±} t Ο) f πs =
    ob t (obs Ο (homs Ξ³ f πs))
      β‘β¨ ap (ob t) (nats Ο f πs) β©
    ob t (homs Ξ΄ f (obs Ο πs))
      β‘β¨ nat t f (obs Ο πs) β©
    hom Ξ± f (ob t (obs Ο πs))
      β

  _βPSh_ : {Ξ³ Ξ΄ Ξ΅ : PShs} β PShMors Ξ΄ Ξ΅ β PShMors Ξ³ Ξ΄ β PShMors Ξ³ Ξ΅
  Ο βPSh Ο = mapπΈππ  _[ Ο ]PSh Ο

  obsβPSh : {Ξ³ Ξ΄ Ξ΅ : PShs} (Ο : PShMors Ξ΄ Ξ΅) (Ο : PShMors Ξ³ Ξ΄) {A : ππ} (πs : secs Ξ³ A) β
    obs (Ο βPSh Ο) πs β‘ obs Ο (obs Ο πs)
  obsβPSh ! Ο πs = refl
  obsβPSh (Ο β t) Ο πs i = obsβPSh Ο Ο πs i β ob t (obs Ο πs)

  [][]PSh : {Ξ³ Ξ΄ Ξ΅ : PShs} {Ξ± : PSh} (t : PShMor Ξ΅ Ξ±) (Ο : PShMors Ξ΄ Ξ΅) (Ο : PShMors Ξ³ Ξ΄) β
    t [ Ο ]PSh [ Ο ]PSh β‘ t [ Ο βPSh Ο ]PSh
  [][]PSh t Ο Ο = β‘PShMor (Ξ» πs i β ob t (obsβPSh Ο Ο πs (~ i)))

  π§PSh : {Ξ³ : PShs} {Ξ± : PSh} β PShMor (Ξ³ βΉ Ξ±) Ξ±
  ob π§PSh (πs β π) = π
  nat π§PSh f (πs β π) = refl

  WβPSh : {Ξ³ : PShs} (Ξ± : PSh) {Ξ² : PSh} β PShMor Ξ³ Ξ² β PShMor (Ξ³ βΉ Ξ±) Ξ²
  ob (WβPSh Ξ± t) (πs β π) = ob t πs
  nat (WβPSh Ξ± t) f (πs β π) = nat t f πs

  WβPShs : {Ξ³ Ξ΄ : PShs} (Ξ± : PSh) β PShMors Ξ³ Ξ΄ β PShMors (Ξ³ βΉ Ξ±) Ξ΄
  WβPShs Ξ± Ο = mapπΈππ  (WβPSh Ξ±) Ο

  WβPShs : {Ξ³ Ξ΄ : PShs} (Ξ± : PSh) β PShMors Ξ³ Ξ΄ β PShMors (Ξ³ βΉ Ξ±) (Ξ΄ βΉ Ξ±)
  WβPShs Ξ± Ο = WβPShs Ξ± Ο β π§PSh

  idPSh : (Ξ³ : PShs) β PShMors Ξ³ Ξ³
  idPSh β = !
  idPSh (Ξ³ βΉ Ξ±) = WβPShs Ξ± (idPSh Ξ³)

  obsW : {Ξ³ Ξ΄ : PShs} (Ξ± : PSh) {A : ππ} (Ο : PShMors Ξ³ Ξ΄) (πs : secs Ξ³ A) (π : sec Ξ± A) β
    obs (WβPShs Ξ± Ο) (πs β π) β‘ obs Ο πs
  obsW Ξ± ! πs π = refl
  obsW Ξ± (Ο β t) πs π i = obsW Ξ± Ο πs π i β ob t πs 

  obsId : {Ξ³ : PShs} {A : ππ} (πs : secs Ξ³ A) β obs (idPSh Ξ³) πs β‘ πs
  obsId ! = refl
  obsId {Ξ³ = Ξ³ βΉ Ξ±} (πs β π) =
    obs (WβPShs Ξ± (idPSh Ξ³)) (πs β π) β π
      β‘β¨ (Ξ» i β obsW Ξ± (idPSh Ξ³) πs π i β π) β©
    obs (idPSh Ξ³) πs β π
      β‘β¨ (Ξ» i β obsId πs i β π) β©
    πs β π
      β

  WPShLem1 : {Ξ³ Ξ΄ : PShs} {Ξ± Ξ² : PSh} (t : PShMor Ξ΄ Ξ²) (Ο : PShMors Ξ³ Ξ΄) (s : PShMor Ξ³ Ξ±) β
    WβPSh Ξ± t [ Ο β s ]PSh β‘ t [ Ο ]PSh
  WPShLem1 Ο Ο t = β‘PShMor (Ξ» πs β refl)

  WPShLem2 : {Ξ³ Ξ΄ Ξ΅ : PShs} {Ξ± : PSh} (Ο : PShMors Ξ΄ Ξ΅) (Ο : PShMors Ξ³ Ξ΄) (s : PShMor Ξ³ Ξ±) β
    WβPShs Ξ± Ο βPSh (Ο β s) β‘ Ο βPSh Ο
  WPShLem2 ! Ο s = refl
  WPShLem2 (Ο β t) Ο s i = WPShLem2 Ο Ο s i β WPShLem1 t Ο s i

  WPShLem3 : {Ξ³ Ξ΄ : PShs} {Ξ± Ξ² : PSh} (t : PShMor Ξ΄ Ξ²) (Ο : PShMors Ξ³ Ξ΄) β
    t [ WβPShs Ξ± Ο ]PSh β‘ WβPSh Ξ± (t [ Ο ]PSh)
  WPShLem3 {Ξ± = Ξ±} t Ο = β‘PShMor (Ξ» {(πs β π) β ap (ob t) (obsW Ξ± Ο πs π)})

  WPShLem4 : {Ξ³ Ξ΄ Ξ΅ : PShs} {Ξ± : PSh} (Ο : PShMors Ξ΄ Ξ΅) (Ο : PShMors Ξ³ Ξ΄) β
    Ο βPSh WβPShs Ξ± Ο β‘ WβPShs Ξ± (Ο βPSh Ο)
  WPShLem4 ! Ο = refl
  WPShLem4 (Ο β t) Ο i = WPShLem4 Ο Ο i β WPShLem3 t Ο i

  π§PShLem : {Ξ³ Ξ΄ : PShs} {Ξ± : PSh} (Ο : PShMors Ξ³ Ξ΄) (t : PShMor Ξ³ Ξ±) β
    π§PSh [ Ο β t ]PSh β‘ t
  π§PShLem Ο t = β‘PShMor (Ξ» πs β refl)

  idLPSh : {Ξ³ Ξ΄ : PShs} (Ο : PShMors Ξ³ Ξ΄) β idPSh Ξ΄ βPSh Ο β‘ Ο
  idLPSh ! = refl
  idLPSh {Ξ΄ = Ξ΄ βΉ Ξ±} (Ο β t) =
    WβPShs Ξ± (idPSh Ξ΄) βPSh (Ο β t)
      β‘β¨ (Ξ» i β WPShLem2 (idPSh Ξ΄) Ο t i β π§PShLem Ο t i) β©
    (idPSh Ξ΄ βPSh Ο) β t
      β‘β¨ (Ξ» i β idLPSh Ο i β t) β©
    Ο β t
      β

  id[]PSh : {Ξ³ : PShs} {Ξ± : PSh} (t : PShMor Ξ³ Ξ±) β t [ idPSh Ξ³ ]PSh β‘ t
  id[]PSh t = β‘PShMor (Ξ» πs i β ob t (obsId πs i))

  open Contextual

  π«π?π½ : Contextual (lsuc β) (lsuc β)
  ty π«π?π½ = PSh
  tm π«π?π½ = PShMor
  _β¦_β§ π«π?π½ = _[_]PSh
  πΎπΉ π«π?π½ = idPSh
  πΎπΉL π«π?π½ = idLPSh
  πΎπΉβ¦β§ π«π?π½ = id[]PSh
  β¦β§β¦β§ π«π?π½ = [][]PSh
  isSetTm π«π?π½ = {!!}

  record PShMorCart (Ξ± Ξ² : PSh) : Type β where
    field
      ob : {A : ππ} β sec Ξ± A β sec Ξ² A
      nat : {A B : ππ} (f : πππ A B) (π : sec Ξ± B) β
        ob (hom Ξ± f π) β‘ hom Ξ² f (ob π)

  open PShMorCart

  β‘PShMorCart : {Ξ± Ξ² : PSh} {t s : PShMorCart Ξ± Ξ²} β
    ({A : ππ} (π : sec Ξ± A) β ob t π β‘ ob s π) β t β‘ s
  ob (β‘PShMorCart p i) π = p π i
  nat (β‘PShMorCart {Ξ±} {Ξ²} {t} {s} p i) f π j =
    isSetβSquareP (Ξ» i j β isSetSec Ξ²)
      (nat t f π)
      (nat s f π)
      (p (hom Ξ± f π))
      (Ξ» k β hom Ξ² f (p π k)) i j

  isSetPShMorCart : {Ξ± Ξ² : PSh} β isSet (PShMorCart Ξ± Ξ²)
  isSetPShMorCart = {!!}

module PresheafCCC {β : Level} (π : Category β β) where
  open Category π
  open Presheaf π
  
  private
    module P = Contextual π«π?π½

  open PSh
  open PShMor
  open PShMorCart

  γ : ππ β PSh
  sec (γ A) B = πππ B A
  isSetSec (γ A) = isSetMor
  hom (γ A) f g = g β f
  id-hom (γ A) f = πΎπΉR f
  β-hom (γ A) f g h = βAssoc h f g β»ΒΉ

  _ΓPSh_ : PSh β PSh β PSh
  sec (Ξ± ΓPSh Ξ²) A = sec Ξ± A Γ sec Ξ² A
  isSetSec (Ξ± ΓPSh Ξ²) = isSetΓ (isSetSec Ξ±) (isSetSec Ξ²)
  hom (Ξ± ΓPSh Ξ²) f (π , π) = hom Ξ± f π , hom Ξ² f π
  id-hom (Ξ± ΓPSh Ξ²) (π , π) i = id-hom Ξ± π i , id-hom Ξ² π i
  β-hom (Ξ± ΓPSh Ξ²) f g (π , π) i = β-hom Ξ± f g π i , β-hom Ξ² f g π i

  _βPSh_ : PSh β PSh β PSh
  sec (Ξ± βPSh Ξ²) A = PShMorCart (γ A ΓPSh Ξ±) Ξ²
  isSetSec (Ξ± βPSh Ξ²) = isSetPShMorCart
  ob (hom (Ξ± βPSh Ξ²) f t) (g , π) = ob t (f β g , π)
  nat (hom (Ξ± βPSh Ξ²) f t) g (h , π) =
    ob t (f β (h β g) , hom Ξ± g π)
      β‘β¨ (Ξ» i β ob t (βAssoc f h g (~ i) , hom Ξ± g π)) β©
    ob t (f β h β g , hom Ξ± g π)
      β‘β¨ nat t g (f β h , π) β©
    hom Ξ² g (ob t (f β h , π))
      β
  id-hom (Ξ± βPSh Ξ²) t =
    β‘PShMorCart (Ξ» {(f , π) i β ob t (πΎπΉL f i , π)})
  β-hom (Ξ± βPSh Ξ²) f g t =
    β‘PShMorCart (Ξ» {(h , π) i β ob t (βAssoc f g h i , π)})

  ΞPSh : {Ξ³ : PShs} {Ξ± Ξ² : PSh} β PShMor (Ξ³ βΉ Ξ±) Ξ² β PShMor Ξ³ (Ξ± βPSh Ξ²)
  ob (ob (ΞPSh {Ξ³} t) πs) (f , π) = ob t (homs Ξ³ f πs β π) 
  nat (ob (ΞPSh {Ξ³} {Ξ±} {Ξ²} t) πs) f (g , π) =
    ob t (homs Ξ³ (g β f) πs β hom Ξ± f π)
      β‘β¨ (Ξ» i β ob t (β-homs Ξ³ g f πs i β hom Ξ± f π)) β©
    ob t (homs (Ξ³ βΉ Ξ±) f (homs Ξ³ g πs β π))
      β‘β¨ nat t f (homs Ξ³ g πs β π) β©
    hom Ξ² f (ob t (homs Ξ³ g πs β π))
      β
  nat (ΞPSh {Ξ³} t) f πs =
    β‘PShMorCart (Ξ» {(g , π) i β ob t (β-homs Ξ³ f g πs (~ i) β π)})

  AppPSh : {Ξ³ : PShs} {Ξ± Ξ² : PSh} β PShMor Ξ³ (Ξ± βPSh Ξ²) β PShMor Ξ³ Ξ± β PShMor Ξ³ Ξ²
  ob (AppPSh t s) {A} πs = ob (ob t πs) (πΎπΉ A , ob s πs)
  nat (AppPSh {Ξ³} {Ξ±} {Ξ²} t s) {A} {B} f πs =
    ob (ob t (homs Ξ³ f πs)) (πΎπΉ A , ob s (homs Ξ³ f πs))
      β‘β¨ (Ξ» i β ob (nat t f πs i) (πΎπΉ A , nat s f πs i)) β©
    ob (ob t πs) (f β πΎπΉ A , hom Ξ± f (ob s πs))
      β‘β¨ (Ξ» i β ob (ob t πs) (πΎπΉL (πΎπΉR f i) (~ i) , hom Ξ± f (ob s πs))) β©
    ob (ob t πs) (πΎπΉ B β f , hom Ξ± f (ob s πs))
      β‘β¨ nat (ob t πs) f (πΎπΉ B , ob s πs) β©
    hom Ξ² f (ob (ob t πs) (πΎπΉ B , ob s πs))
      β

  β‘PShMorβ : {Ξ³ : PShs} {Ξ± Ξ² : PSh} {t s : PShMor Ξ³ (Ξ± βPSh Ξ²)} β
    ({A B : ππ} (πs : secs Ξ³ A) (f : πππ B A) (π : sec Ξ± B) β
      ob (ob t πs) (f , π) β‘ ob (ob s πs) (f , π)) β t β‘ s
  β‘PShMorβ {t = t} p = β‘PShMor (Ξ» πs β β‘PShMorCart (Ξ» {(f , π) β p πs f π}))

  ΞnatPSh : {Ξ³ Ξ΄ : PShs} {Ξ± Ξ² : PSh} (t : PShMor (Ξ΄ βΉ Ξ±) Ξ²) (Ο : PShMors Ξ³ Ξ΄) β
    ΞPSh t P.β¦ Ο β§ β‘ ΞPSh (t P.β¦ P.Wβtms Ξ± Ο β§)
  ΞnatPSh {Ξ³} {Ξ΄} {Ξ±} {Ξ²} t Ο =
    β‘PShMorβ {Ξ± = Ξ±} {Ξ²}
      (Ξ» πs f π β
        ob t (homs Ξ΄ f (obs Ο πs) β π)
          β‘β¨ (Ξ» i β ob t (nats Ο f πs (~ i) β π)) β©
        ob t (obs Ο (homs Ξ³ f πs) β π)
          β‘β¨ (Ξ» i β ob t (obs Ο (obsId (homs Ξ³ f πs) (~ i)) β π)) β©
        ob t (obs Ο (obs (P.πΎπΉ Ξ³) (homs Ξ³ f πs)) β π)
          β‘β¨ (Ξ» i β ob t (obs Ο (obsW Ξ± (P.πΎπΉ Ξ³) (homs Ξ³ f πs) π (~ i)) β π)) β©
        ob t (obs Ο (obs (WβPShs Ξ± (P.πΎπΉ Ξ³)) (homs Ξ³ f πs β π)) β π)
          β‘β¨ (Ξ» i β ob t (obsβPSh Ο (WβPShs Ξ± (P.πΎπΉ Ξ³)) (homs Ξ³ f πs β π) (~ i) β π)) β©
        ob t (obs (Ο P.β WβPShs Ξ± (P.πΎπΉ Ξ³)) (homs Ξ³ f πs β π) β π)
          β)

  AppΞ²PSh : {Ξ³ : PShs} {Ξ± Ξ² : PSh} (t : PShMor (Ξ³ βΉ Ξ±) Ξ²) (s : PShMor Ξ³ Ξ±) β
    AppPSh (ΞPSh t) s β‘ (t P.β¦ P.πΎπΉ Ξ³ β s β§)
  AppΞ²PSh {Ξ³} t s =
    β‘PShMor
      (Ξ» {A} πs β
        ob t (homs Ξ³ (πΎπΉ A) πs β ob s πs)
          β‘β¨ (Ξ» i β ob t (id-homs Ξ³ πs i β ob s πs)) β©
        ob t (πs β ob s πs)
          β‘β¨ (Ξ» i β ob t (obsId πs (~ i) β ob s πs)) β©
        ob t (obs (idPSh Ξ³) πs β ob s πs)
          β)

  π΄ππPSh : {Ξ³ : PShs} {Ξ± Ξ² : PSh} β PShMor Ξ³ (Ξ± βPSh Ξ²) β PShMor (Ξ³ βΉ Ξ±) Ξ²
  π΄ππPSh {Ξ³} {Ξ±} {Ξ²} t = AppPSh {Ξ³ βΉ Ξ±} {Ξ±} {Ξ²} (t P.β¦ P.Ο β§) (P.π§)

  AppΞ·PSh : {Ξ³ : PShs} {Ξ± Ξ² : PSh} (t : PShMor Ξ³ (Ξ± βPSh Ξ²)) β
    t β‘ ΞPSh (π΄ππPSh {Ξ³} {Ξ±} {Ξ²} t)
  AppΞ·PSh {Ξ³} {Ξ±} {Ξ²} t =
    β‘PShMorβ {Ξ± = Ξ±} {Ξ²}
      (Ξ» {Ξ} {Ξ} πs f π β
        ob (ob t πs) (f , π)
          β‘β¨ (Ξ» i β ob (ob t πs) (πΎπΉR f (~ i) , π)) β©
        ob (ob t πs) (f β πΎπΉ Ξ , π)
          β‘β¨ (Ξ» i β ob (nat t f πs (~ i)) (πΎπΉ Ξ , π)) β©
        ob (ob t (homs Ξ³ f πs)) (πΎπΉ Ξ , π)
          β‘β¨ (Ξ» i β ob (ob t (obsId (homs Ξ³ f πs) (~ i))) (πΎπΉ Ξ , π)) β©
        ob (ob t (obs (idPSh Ξ³) (homs Ξ³ f πs))) (πΎπΉ Ξ , π)
          β‘β¨ (Ξ» i β ob (ob t (obsW Ξ± (idPSh Ξ³) (homs Ξ³ f πs) π (~ i))) (πΎπΉ Ξ , π)) β©
        ob (ob t (obs (WβPShs Ξ± (idPSh Ξ³)) (homs Ξ³ f πs β π))) (πΎπΉ Ξ , π)
          β)

  open CCC

  π«π?π½CCC : CCC π«π?π½
  _β_ π«π?π½CCC = _βPSh_
  Ξ π«π?π½CCC = ΞPSh
  πππ π«π?π½CCC = AppPSh
  Ξnat π«π?π½CCC = ΞnatPSh
  πππΞ² π«π?π½CCC = AppΞ²PSh
  πππΞ· π«π?π½CCC {Ξ³} {Ξ±} {Ξ²} = AppΞ·PSh {Ξ³} {Ξ±} {Ξ²}

{-module PShWeave {β : Level} (π : Category β β) where
  open Presheaf π
  open Category π
  open PSh
  open PShMor

  record PShMorCart (Ξ± Ξ² : PSh) : Type β where
    field
      ob : {A : ππ} β sec Ξ± A β sec Ξ² A
      nat : {A B : ππ} (f : πππ A B) (π : sec Ξ± B) β
        ob (hom Ξ± f π) β‘ hom Ξ² f (ob π)

  open PShMorCart

  β‘PShMorCart : {Ξ± Ξ² : PSh} {t s : PShMorCart Ξ± Ξ²} β
    ({A : ππ} (π : sec Ξ± A) β ob t π β‘ ob s π) β t β‘ s
  ob (β‘PShMorCart p i) π = p π i
  nat (β‘PShMorCart {Ξ±} {Ξ²} {t} {s} p i) f π j =
    isSetβSquareP (Ξ» i j β isSetSec Ξ²)
      (nat t f π)
      (nat s f π)
      (p (hom Ξ± f π))
      (Ξ» k β hom Ξ² f (p π k)) i j

  WΞ³PSh : {Ξ± Ξ² : PSh} (Ξ³ : PShs) β PShMorCart Ξ± Ξ² β PShMor (Ξ³ βΉ Ξ±) Ξ²
  ob (WΞ³PSh Ξ³ t) (πs β π) = ob t π
  nat (WΞ³PSh Ξ³ t) f (πs β π) = nat t f π

  _βPSh_ : {Ξ³ Ξ΄ : PShs} {Ξ± Ξ² : PSh} β PShMors Ξ³ Ξ΄ β PShMorCart Ξ± Ξ² β PShMors (Ξ³ βΉ Ξ±) (Ξ΄ βΉ Ξ²)
  _βPSh_ {Ξ³} {Ξ΄} {Ξ±} Ο t = WβPShs Ξ± Ο β WΞ³PSh Ξ³ t

  module _ {ββ} {ty : Type ββ} where
    PShFamily = ty β PSh
    PShsFamily = πΆπ‘π₯ ty β PShs

    plurify : PShFamily β PShsFamily
    plurify π« = mapπΆπ‘π₯ π«

    βͺsecsβ« : (π« : PShFamily) (Ξ : πΆπ‘π₯ ty) β ππ β Type (β β ββ)
    βͺsecsβ« π« Ξ A = πΈππ  (Ξ» B β sec (π« B) A) Ξ

    β : {π« : PShFamily} {Ξ : πΆπ‘π₯ ty} {A : ππ} β
      secs (plurify π« Ξ) A β βͺsecsβ« π« Ξ A
    β {Ξ = β} πs = !
    β {Ξ = Ξ βΉ A} (πs β π) = β πs β π

    β : {π« : PShFamily} {Ξ : πΆπ‘π₯ ty} {A : ππ} β
      βͺsecsβ« π« Ξ A β secs (plurify π« Ξ) A
    β ! = !
    β (πs β π) = β πs β π

    βhom : {π« : PShFamily} {Ξ : πΆπ‘π₯ ty} {A B : ππ} (f : πππ A B) (πs : secs (plurify π« Ξ) B) β
      β (homs (plurify π« Ξ) f πs) β‘ mapπΈππ  (Ξ» {C} β hom (π« C) f) (β πs)
    βhom {Ξ = β} f πs = refl
    βhom {π} {Ξ βΉ A} f (πs β π) i = βhom f πs i β hom (π A) f π

    MorFamily : (π« π¬ : PShFamily) β Type (β β ββ)
    MorFamily π« π¬ = (A : ty) β PShMorCart (π« A) (π¬ A)

    weaveMor : {π« π¬ : PShFamily} (π : MorFamily π« π¬) β
      (Ξ : πΆπ‘π₯ ty) β PShMors (plurify π« Ξ) (plurify π¬ Ξ)
    weaveMor π β = !
    weaveMor π (Ξ βΉ A) = weaveMor π Ξ βPSh π A

    βͺobsβ« : {π« π¬ : PShFamily} (π : MorFamily π« π¬) (Ξ : πΆπ‘π₯ ty) {A : ππ} β
      βͺsecsβ« π« Ξ A β βͺsecsβ« π¬ Ξ A
    βͺobsβ« π Ξ πs = mapπΈππ  (Ξ» {B} β ob (π B)) πs

    ββ : {π« π¬ : PShFamily} (π : MorFamily π« π¬) {Ξ : πΆπ‘π₯ ty} {A : ππ}
      (πs : πΈππ  (Ξ» B β sec (π« B) A) Ξ) β
      β (obs (weaveMor π Ξ) (β πs)) β‘ βͺobsβ« π Ξ πs
    ββ π ! = refl
    ββ {π«} π {Ξ = Ξ βΉ A} (πs β π) =
      β (obs (WβPShs (π« A) (weaveMor π Ξ)) (β πs β π)) β ob (π A) π
        β‘β¨ (Ξ» i β β (obsW (π« A) (weaveMor π Ξ) (β πs) π i) β ob (π A) π) β©
      β (obs (weaveMor π Ξ) (β πs)) β ob (π A) π
        β‘β¨ (Ξ» i β ββ π πs i β ob (π A) π) β©
      mapπΈππ  (Ξ» {B} β ob (π B)) πs β ob (π A) π
        β

  infixl 20 _βπ©_
  _βπ©_ : {Ξ± Ξ² ΞΆ : PSh} β PShMorCart Ξ² ΞΆ β PShMorCart Ξ± Ξ² β PShMorCart Ξ± ΞΆ
  ob (t βπ© s) π = ob t (ob s π)
  nat (_βπ©_ {Ξ±} {Ξ²} {ΞΆ} t s) f π =
    ob t (ob s (hom Ξ± f π))
      β‘β¨ ap (ob t) (nat s f π) β©
    ob t (hom Ξ² f (ob s π))
      β‘β¨ nat t f (ob s π) β©
    hom ΞΆ f (ob t (ob s π))
      β

  βπ©Assoc : {Ξ± Ξ² ΞΆ ΞΎ : PSh} (t : PShMorCart ΞΆ ΞΎ) (s : PShMorCart Ξ² ΞΆ) (r : PShMorCart Ξ± Ξ²) β
    (t βπ© s) βπ© r β‘ t βπ© (s βπ© r)
  βπ©Assoc t s r = β‘PShMorCart (Ξ» π β refl)

  infixl 20 _[_]PShCart
  _[_]PShCart : {Ξ³ : PShs} {Ξ± Ξ² : PSh} β PShMorCart Ξ± Ξ² β PShMor Ξ³ Ξ± β PShMor Ξ³ Ξ²
  ob (t [ s ]PShCart) πs = ob t (ob s πs)
  nat (_[_]PShCart {Ξ³} {Ξ±} {Ξ²} t s) f πs =
    ob t (ob s (homs Ξ³ f πs))
      β‘β¨ ap (ob t) (nat s f πs) β©
    ob t (hom Ξ± f (ob s πs))
      β‘β¨ nat t f (ob s πs) β©
    hom Ξ² f (ob t (ob s πs))
      β

  WΞ³PShLem : {Ξ± Ξ² : PSh} {Ξ³ Ξ΄ : PShs} (t : PShMorCart Ξ± Ξ²) (Ο : PShMors Ξ³ Ξ΄) (s : PShMor Ξ³ Ξ±) β
    WΞ³PSh Ξ΄ t [ Ο β s ]PSh β‘ t [ s ]PShCart
  WΞ³PShLem t Ο s = β‘PShMor (Ξ» πs β refl)

  []WΞ³PShCart : {Ξ³ : PShs} {Ξ± Ξ² ΞΆ : PSh} (t : PShMorCart Ξ² ΞΆ) (s : PShMorCart Ξ± Ξ²) β
    t [ WΞ³PSh Ξ³ s ]PShCart β‘ WΞ³PSh Ξ³ (t βπ© s)
  []WΞ³PShCart t s = β‘PShMor (Ξ» {(πs β π) β refl})
  
  βlem1 : {Ξ³ Ξ΄ Ξ΅ : PShs} {Ξ± Ξ² : PSh} (Ο : PShMors Ξ΄ Ξ΅) (t : PShMorCart Ξ± Ξ²)
    (Ο : PShMors Ξ³ Ξ΄) (s : PShMor Ξ³ Ξ±) β
    (Ο βPSh t) βPSh (Ο β s) β‘ (Ο βPSh Ο) β (t [ s ]PShCart)
  βlem1 Ο t Ο s i = WPShLem2 Ο Ο s i β WΞ³PShLem t Ο s i

  βlem2 : {Ξ³ Ξ΄ Ξ΅ : PShs} {Ξ± Ξ² ΞΆ : PSh} (Ο : PShMors Ξ΄ Ξ΅) (t : PShMorCart Ξ² ΞΆ)
    (Ο : PShMors Ξ³ Ξ΄) (s : PShMorCart Ξ± Ξ²) β
    (Ο βPSh t) βPSh (Ο βPSh s) β‘ (Ο βPSh Ο) βPSh (t βπ© s)
  βlem2 {Ξ³ = Ξ³} {Ξ± = Ξ±} Ο t Ο s =
    (Ο βPSh t) βPSh (Ο βPSh s)
      β‘β¨ (Ξ» i β WPShLem2 Ο (WβPShs Ξ± Ο) (WΞ³PSh Ξ³ s) i β WΞ³PShLem t (WβPShs Ξ± Ο) (WΞ³PSh Ξ³ s) i) β©
    (Ο βPSh WβPShs Ξ± Ο) β (t [ WΞ³PSh Ξ³ s ]PShCart)
      β‘β¨ (Ξ» i β WPShLem4 Ο Ο i β []WΞ³PShCart t s i) β©
    (Ο βPSh Ο) βPSh (t βπ© s)
      β

  βIndLem : {Ξ³ Ξ΄ : PShs} {Ξ± Ξ² : PSh} (Ο : PShMors Ξ³ Ξ΄) (t : PShMorCart Ξ± Ξ²)
    {A : ππ} (πs : secs Ξ³ A) (π : sec Ξ± A) β
    obs (Ο βPSh t) (πs β π) β‘ obs Ο πs β ob t π
  βIndLem {Ξ± = Ξ±} Ο t πs π i = obsW Ξ± Ο πs π i β ob t π-}
