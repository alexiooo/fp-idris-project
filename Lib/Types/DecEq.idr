module Lib.Types.DecEq

import public Lib.Types

import public Decidable.Equality

export Uninhabited (PCFBool = PCFNat  ) where uninhabited Refl impossible
export Uninhabited (PCFBool = PCFUnit ) where uninhabited Refl impossible
export Uninhabited (PCFBool = x ~> y  ) where uninhabited Refl impossible
export Uninhabited (PCFBool = x * y   ) where uninhabited Refl impossible
export Uninhabited (PCFNat  = PCFBool ) where uninhabited Refl impossible
export Uninhabited (PCFNat  = PCFUnit ) where uninhabited Refl impossible
export Uninhabited (PCFNat  = x ~> y  ) where uninhabited Refl impossible
export Uninhabited (PCFNat  = x * y   ) where uninhabited Refl impossible
export Uninhabited (PCFUnit = PCFBool ) where uninhabited Refl impossible
export Uninhabited (PCFUnit = PCFNat  ) where uninhabited Refl impossible
export Uninhabited (PCFUnit = x ~> y  ) where uninhabited Refl impossible
export Uninhabited (PCFUnit = x * y   ) where uninhabited Refl impossible
export Uninhabited (x ~> y  = PCFBool ) where uninhabited Refl impossible
export Uninhabited (x ~> y  = PCFNat  ) where uninhabited Refl impossible
export Uninhabited (x ~> y  = PCFUnit ) where uninhabited Refl impossible
export Uninhabited (x ~> y  = z * w   ) where uninhabited Refl impossible
export Uninhabited (x * y   = PCFBool ) where uninhabited Refl impossible
export Uninhabited (x * y   = PCFNat  ) where uninhabited Refl impossible
export Uninhabited (x * y   = PCFUnit ) where uninhabited Refl impossible
export Uninhabited (x * y   = z ~> w  ) where uninhabited Refl impossible

-- These two Uninhabited impls are not needed to define DecEq, but it also can't hurt to have them
export
Uninhabited (x = z) => Uninhabited (x ~> y = z ~> y) where
  uninhabited Refl @{xz} = uninhabited @{xz} Refl

export
Uninhabited (y = w) => Uninhabited (x ~> y = z ~> w) where
  uninhabited Refl @{yw} = uninhabited @{yw} Refl

||| (~>) is injective
export
fnInjective : (x ~> y = z ~> w) -> (x = z, y = w)
fnInjective Refl = (Refl, Refl)

||| (*) is injective
export
pairInjective : (x * y = z * w) -> (x = z, y = w)
pairInjective Refl = (Refl, Refl)

public export
implementation DecEq PCFType where
  decEq PCFBool   PCFBool = Yes Refl
  decEq PCFNat    PCFNat  = Yes Refl
  decEq PCFUnit   PCFUnit = Yes Refl

  decEq (x ~> y)  (z ~> w) with (decEq x z, decEq y w) 
    _ | (Yes xz, Yes yw)  = Yes (rewrite xz in rewrite yw in Refl)
    _ | (No xz, _)        = No $ xz . fst . fnInjective
    _ | (_, No yw)        = No $ yw . snd . fnInjective

  decEq (x * y)   (z * w)  with (decEq x z, decEq y w)
    _ | (Yes xz, Yes yw)  = Yes (rewrite xz in rewrite yw in Refl)
    _ | (No xz, _)        = No $ xz . fst . pairInjective
    _ | (_, No yw)        = No $ yw . snd . pairInjective

  decEq PCFBool   PCFNat    = No absurd
  decEq PCFBool   PCFUnit   = No absurd
  decEq PCFBool   (x ~> y)  = No absurd
  decEq PCFBool   (x * y)   = No absurd
  decEq PCFNat    PCFBool   = No absurd
  decEq PCFNat    PCFUnit   = No absurd
  decEq PCFNat    (x ~> y)  = No absurd
  decEq PCFNat    (x * y)   = No absurd
  decEq PCFUnit   PCFBool   = No absurd
  decEq PCFUnit   PCFNat    = No absurd
  decEq PCFUnit   (x ~> y)  = No absurd
  decEq PCFUnit   (x * y)   = No absurd
  decEq (x ~> y)  PCFBool   = No absurd
  decEq (x ~> y)  PCFNat    = No absurd
  decEq (x ~> y)  PCFUnit   = No absurd
  decEq (x ~> y)  (z * w)   = No absurd
  decEq (x * y)   PCFBool   = No absurd
  decEq (x * y)   PCFNat    = No absurd
  decEq (x * y)   PCFUnit   = No absurd
  decEq (x * y)   (z ~> w)  = No absurd


