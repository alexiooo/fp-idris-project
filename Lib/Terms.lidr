> module Lib.Terms
>
> import public Data.Fin  -- needed publically, since we publically export types that reference Fin

Terms for PCF
-------------

PCF is a simple language that models computing. Its types are as follows.

< public export
> data PCFType = PCFBool
>              | PCFNat
>              | (~>) PCFType PCFType
>              | (*) PCFType PCFType
>              | U
>
> infixr 0 ~>
> infixr 0 *

We want our types to be comparable. This definition enforces unique readability.

< public export
> implementation Eq PCFType where
>   PCFBool  == PCFBool  = True
>   PCFNat   == PCFNat   = True
>   (a ~> b) == (c ~> d) = a == c && b == d
>   (a * b)  == (c * d)  = a == c && b == d
>   U        == U        = True
>   _        == _        = False

We begin by defining terms. We use de Bruijn indices to representent bound
variables. This is an elegant way to deel with alpha-equivalence.
We also keep track of (an upper bound on) free variables in the type;
PCFTerm n encodes terms with at most n free variables

> ||| Var k is a De-Bruijn index less than k
< public export 
> Var : Nat -> Type
> Var = Fin
>
< public export
> data PCFTerm : Nat -> Type where 
>     V    : Var k -> PCFTerm k                        -- variables
>     C    : PCFTerm k -> PCFTerm k     -> PCFTerm k   -- application
>     L    : PCFType   -> PCFTerm (S k) -> PCFTerm k   -- lambda
>     P    : PCFTerm k -> PCFTerm k     -> PCFTerm k   -- pairing
>     P1   : PCFTerm k -> PCFTerm k                    -- first projection
>     P2   : PCFTerm k -> PCFTerm k                    -- second projection
>     T    : PCFTerm k                                 -- true
>     F    : PCFTerm k                                 -- false
>     Zero : PCFTerm k                                -- zero value
>     Succ : PCFTerm k -> PCFTerm k                   -- successor
>     Pred : PCFTerm k -> PCFTerm k                   -- predecessor
>     IsZero : PCFTerm k -> PCFTerm k                 -- is zero predicate
>     IfThenElse : PCFTerm k -> PCFTerm k -> PCFTerm k -> PCFTerm k
>     Y : PCFTerm k -> PCFTerm k                      -- fixpoint / Y-combinator
>     I : PCFTerm k                                   -- unit value (*)

Of special interest are the closed terms, those without any free variables

< public export
> ClosedPCFTerm : Type
> ClosedPCFTerm = PCFTerm 0

The Y constructor returns a fixed-point of the given term. It is required to
define functions by recursion. For example, the sum function on PCFNat is
defined recursively.

### Include SumExample.lidr here?


