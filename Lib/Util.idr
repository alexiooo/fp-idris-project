
module Lib.Util

import public Lib.PCF.Terms

%default total

public export
JustS : Symbol ar -> Vect ar (PCFTerm k) -> Maybe (PCFTerm k)
JustS s arg = Just $ Terms.S s arg


||| HVect is a heterogenous list, so the types of each element may differ, 
||| but the length and individual types are all known.
||| For example, [1, "abc", 1.0] could be an instace of HVect [Integer, String, Double]
public export
data HVect : Vect n Type -> Type where
  Nil  : HVect []
  (::) : el -> HVect sig -> HVect (el :: sig)