< module Lib.TypedTerms
<
< import Lib.PCF
< import Data.DPair
< import Lib.Terms.DecEq

Well-Typed Terms
-------------

Our use of dependent typing has been relatively mild so far.
This section will change that.

We have a notion of terms, some of which might be malformed, and a type inference function to 
recognize well-formed terms.
For coming developments we are really only interested in the latter, so we want a type whose inhabitants
are exactly the well-typed terms.

The construction goes as follows: TermOfType k ctx type, where k is the bound on free variables, ctx a corresponding context
and type a PCFType, should represent all terms t such that typeOf ctx t = Just type.
The definition has the same constructors as standard PCFTerms, but now the typing rules are also incorporated into the
signatures.

< public export
> data TermOfType : {k : Nat} -> (con : Context k) -> (0 t : PCFType) -> Type where
>     V    : (v : Var _)  -> TermOfType con (index v con)           -- variables
>     App  : TermOfType con (t1 ~> t2)  -> TermOfType con t1            -- application
>             -> TermOfType con t2  
>     L    : (t1 : PCFType)         -> TermOfType (t1 :: con) t2    -- lambda abstraction
>             -> TermOfType con (t1 ~> t2)   
>     Pair : TermOfType con t1 -> TermOfType con t2                     -- pairing
>             -> TermOfType con (t1 * t2)
>     Fst   : TermOfType con (t1 * _)                                -- first projection
>             -> TermOfType con t1
>     Snd   : TermOfType con (_ * t2)                                -- second projection
>             -> TermOfType con t2
>     T    : TermOfType _ PCFBool                                   -- true
>     F    : TermOfType _ PCFBool                                   -- false
>     Zero : TermOfType _ PCFNat                                    -- zero value
>     Succ : TermOfType c PCFNat -> TermOfType c PCFNat                 -- successor
>     Pred : TermOfType c PCFNat -> TermOfType c PCFNat                 -- predecessor
>     IsZero : TermOfType c PCFNat -> TermOfType c PCFBool              -- is zero predicate
>     IfElse : TermOfType c PCFBool 
>                     -> TermOfType c t
>                     -> TermOfType c t
>                   -> TermOfType c t
>     Y     : TermOfType c (t ~> t) -> TermOfType c t             -- fixpoint / Y-combinator
>     Unit  : TermOfType c PCFUnit                            -- unit value (*)

Often we don't want to specify the concrete type of a WFTerm

< public export
> TypedTerm : {k : Nat} -> (con : Context k) -> Type
> TypedTerm con = DPair PCFType (\t => TermOfType con t)

And in particular, the closed, well-formed terms inhabiting any given PCFType

< public export
> ClosedTermOfType : (0 _ : PCFType) -> Type
> ClosedTermOfType = TermOfType []

Or any type at all

< public export
> ClosedTypedTerm : Type
> ClosedTypedTerm = TypedTerm []

Type checking now means to translate a PCFTerm to a TypedTerm

< public export total 
> typeCheck : (con : Context k) -> PCFTerm k -> Maybe (TypedTerm con)


< public export total
> typeCheckVect : (con: Context k) -> Vect n (PCFTerm k) -> Maybe (Vect n (TypedTerm con))
< typeCheckVect x (y :: ys) = [| (typeCheck x y) :: (typeCheckVect x ys) |]
< typeCheckVect _ []        = Just []

< JustT : {type : PCFType} -> TermOfType con type -> Maybe (TypedTerm con)
< JustT m = Just (type ** m)

> typeCheck con (V v)    = JustT (V v) 
> typeCheck con (L t m)  = ?typeCheck_rhs_3

-- > typeCheck con (S s ms) with (s, typeCheckVect con ms)
-- >   _ | (IfElse, [(PCFBool ** p), (a ** m), (b ** n)]) => Nothing
-- >   _ | _ => Nothing


> typeCheck con (S s ms) = case ( s,  !(typeCheckVect con ms) ) of
>   (IfElse,  [(PCFBool ** p), (a ** m), (a ** n)]) => JustT (IfElse p m n)
>   (App,     [((a ~> b) ** m), (a ** n)])          => JustT (App m n)
>   (Pair,    [(_ ** m), (_ ** n)] )  => JustT (Pair m n)
>   (Fst,     [((_ * _) ** m)])       => JustT (Fst m)
>   (Snd,     [((_ * _) ** m)])       => JustT (Snd m)
>   (Succ,    [(PCFNat ** m)])        => JustT (Succ m)
>   (Pred,    [(PCFNat ** m)])        => JustT (Pred m)
>   (IsZero,  [(PCFNat ** m)])        => JustT (IsZero m)
>   (T,       [])                     => JustT T
>   (F,       [])                     => JustT F
>   (Zero,    [])                     => JustT Zero
>   (Unit,    [])                     => JustT Unit
>   (_, _)                            => Nothing
