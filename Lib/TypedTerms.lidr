< module Lib.TypedTerms
<
< import Lib.PCF
< import Data.DPair

Well-Typed Terms
-------------

Our use of dependent typing has been relatively mild so far.
This section will change that.

We have a notion of terms, some of which might be malformed, and a type inference function to 
recognize well-formed terms.
For coming developments we are really only interested in the latter, so we want a type whose inhabitants
are exactly the well-typed terms.

The construction goes as follows: WFTerm k ctx type, where k is the bound on free variables, ctx a corresponding context
and type a PCFType, should represent all terms t such that typeOf ctx t = Just type.
The definition has the same constructors as standard PCFTerms, but now the typing rules are also incorporated into the
signatures.

< public export
> data WFTerm : {k : Nat} -> (con : Context k) -> PCFType -> Type where
>     V    : (v : Var _)  -> WFTerm con (index v con)           -- variables
>     C    : WFTerm con (t1 ~> t2)  -> WFTerm con t1            -- application
>             -> WFTerm con t2  
>     L    : (t1 : PCFType)         -> WFTerm (t1 :: con) t2    -- lambda abstraction
>             -> WFTerm con (t1 ~> t2)   
>     P    : WFTerm con t1 -> WFTerm con t2                     -- pairing
>             -> WFTerm con (t1 * t2)
>     P1   : WFTerm con (t1 * _)                                -- first projection
>             -> WFTerm con t1
>     P2   : WFTerm con (_ * t2)                                -- second projection
>             -> WFTerm con t2
>     T    : WFTerm _ PCFBool                                   -- true
>     F    : WFTerm _ PCFBool                                   -- false
>     Zero : WFTerm _ PCFNat                                    -- zero value
>     Succ : WFTerm c PCFNat -> WFTerm c PCFNat                 -- successor
>     Pred : WFTerm c PCFNat -> WFTerm c PCFNat                 -- predecessor
>     IsZero : WFTerm c PCFNat -> WFTerm c PCFBool              -- is zero predicate
>     IfElse : WFTerm c PCFBool 
>                     -> WFTerm c t
>                     -> WFTerm c t
>                   -> WFTerm c t
>     Y : WFTerm c (t ~> t) -> WFTerm c t             -- fixpoint / Y-combinator
>     I : WFTerm c PCFUnit                            -- unit value (*)

Often we don't want to specify the concrete type of a WFTerm

< public export
> record TypedTerm {k : Nat} (con : Context k) where
>   constructor MkTypedTerm
>   type : PCFType
>   term : WFTerm con type

And in particular, the closed, well-formed terms inhabiting any given PCFType

< public export
> WellFormedTerm : PCFType -> Type
> WellFormedTerm = WFTerm []

Or any type at all

< public export
> WellTypedTerm : Type
> WellTypedTerm = TypedTerm []


Type checking now means to translate a PCFTerm to a TypedTerm

< public export
> typeCheck : (con : Context k) -> PCFTerm k -> Maybe (TypedTerm con)

< JustT : (type : PCFType) -> WFTerm con type -> Maybe (TypedTerm con)
< JustT type term = Just (MkTypedTerm type term)

> typeCheck c (V v)   = JustT (index v c) (V v) 
> typeCheck c (C x y) = case (typeCheck c x, typeCheck c y) of
>                         (JustT _ (t1 ~> t2), JustT _ t1) => JustT (C x y) t2
>                                                        _ => Nothing
> typeCheck c (L t m) = ?typeCheck_rhs_3
> typeCheck c (P x y) = ?typeCheck_rhs_4
> typeCheck c (P1 x) = ?typeCheck_rhs_5
> typeCheck c (P2 x) = ?typeCheck_rhs_6
> typeCheck c T = ?typeCheck_rhs_7
> typeCheck c F = ?typeCheck_rhs_8
> typeCheck c Zero = ?typeCheck_rhs_9
> typeCheck c (Succ x) = ?typeCheck_rhs_10
> typeCheck c (Pred x) = ?typeCheck_rhs_11
> typeCheck c (IsZero x) = ?typeCheck_rhs_12
> typeCheck c (IfElse x y z) = ?typeCheck_rhs_13
> typeCheck c (Y x) = ?typeCheck_rhs_14
> typeCheck c I = ?typeCheck_rhs_15