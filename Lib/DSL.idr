

||| DSL allows us to write PCF terms using more familiar notation, such as
|||   * using λ instead of L for lambda abstraction
|||   * writing if' p (then' m) (else' n)
|||   * using nat' and bool' as types
|||   * using curried versions of the constructors
||| Note the ' marks, which differentiate the embedded PCF notation from Idris
module Lib.DSL

import Lib.Terms


public export IfElse : PCFTerm k -> PCFTerm k -> PCFTerm k -> PCFTerm k
public export App    : PCFTerm k -> PCFTerm k -> PCFTerm k   -- application
public export Pair   : PCFTerm k -> PCFTerm k -> PCFTerm k   -- pairing
public export Fst    : PCFTerm k -> PCFTerm k                    -- first projection
public export Snd    : PCFTerm k -> PCFTerm k                    -- second projection
public export Succ   : PCFTerm k -> PCFTerm k                   -- successor
public export Pred   : PCFTerm k -> PCFTerm k                   -- predecessor
public export IsZero : PCFTerm k -> PCFTerm k                 -- is zero predicate
public export Y      : PCFTerm k -> PCFTerm k                      -- fixpoint / Y-combinator
public export T      : PCFTerm k                                 -- true
public export F      : PCFTerm k                                 -- false
public export Zero   : PCFTerm k                                -- zero value
public export Unit   : PCFTerm k                                   -- unit value (*)

IfElse p m n = S IfElse [p, m, n]
App    m n = S App    [m, n]
Pair   m n = S Pair   [m, n]
Fst    m   = S Fst    [m]
Snd    m   = S Snd    [m]
Succ   m   = S Succ   [m]
Pred   m   = S Pred   [m]
IsZero m   = S IsZero [m]
Y      m   = S Y      [m]
T = S T []
F = S F []
Zero = S Zero []
Unit = S Unit []



public export
λ : PCFType -> PCFTerm (S k) -> PCFTerm k
λ = L

infixl 6 .

public export
(.) : PCFTerm k -> PCFTerm k -> PCFTerm k
(.) = App



public export
data Then : Nat -> Type where
  Then' : PCFTerm k -> Then k

public export
data Else : Nat -> Type where
  Else' : PCFTerm k -> Else k

public export
if' : PCFTerm k -> Then k -> Else k -> PCFTerm k
if' p (Then' m) (Else' n) = S IfElse [p, m, n]

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

public export
unit' : PCFType
unit' = PCFUnit
