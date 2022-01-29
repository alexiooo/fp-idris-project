

||| DSL allows us to write PCF terms using more familiar notation, such as
|||   * using λ instead of L for lambda abstraction
|||   * writing if' p (then' m) (else' n)
|||   * using nat' and bool' as types
||| Note the ' marks, which differentiate the embedded PCF notation from Idris
module Lib.DSL

import Lib.PCF

--     V    : Var k -> PCFTerm k                        -- variables
--     C    : PCFTerm k -> PCFTerm k     -> PCFTerm k   -- application
--     L    : PCFType   -> PCFTerm (S k) -> PCFTerm k   -- lambda
--     P    : PCFTerm k -> PCFTerm k     -> PCFTerm k   -- pairing
--     P1   : PCFTerm k -> PCFTerm k                    -- first projection
--     P2   : PCFTerm k -> PCFTerm k                    -- second projection
--     T    : PCFTerm k                                 -- true
--     F    : PCFTerm k                                 -- false
--     Zero : PCFTerm k                                -- zero value
--     Succ : PCFTerm k -> PCFTerm k                   -- successor
--     Pred : PCFTerm k -> PCFTerm k                   -- predecessor
--     IsZero : PCFTerm k -> PCFTerm k                 -- is zero predicate
--     IfElse : PCFTerm k -> PCFTerm k -> PCFTerm k -> PCFTerm k
--     Y : PCFTerm k -> PCFTerm k                      -- fixpoint / Y-combinator
--     I : PCFTerm k                                   -- unit value (*)

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
if' p (Then' m) (Else' n) = IfElse p m n

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

