

||| DSL allows us to write PCF terms using more familiar notation, such as
|||   * using λ instead of L for lambda abstraction
|||   * writing if' p (then' m) (else' n)
|||   * using nat' and bool' as types
||| Note the ' marks, which differentiate the embedded PCF notation from Idris
module Lib.DSL

import Lib.PCF

public export
λ : PCFType -> PCFTerm (S k) -> PCFTerm k
λ = L

infix 6 .

public export
(.) : PCFTerm k -> PCFTerm k -> PCFTerm k
(.) = C



public export
data Then : Nat -> Type where
  Then' : PCFTerm k -> Then k

public export
data Else : Nat -> Type where
  Else' : PCFTerm k -> Else k

public export
if' : PCFTerm k -> Then k -> Else k -> PCFTerm k
if' p (Then' m) (Else' n) = IfThenElse p m n

public export
then' : PCFTerm k -> Then k
then' = Then'

public export
else' : PCFTerm k -> Else k
else' = Else'

public export 
nat' : PCFType
nat' = PCFNat

public export 
bool' : PCFType
bool' = PCFBool

