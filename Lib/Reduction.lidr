
< module Lib.Reduction
<
< import Lib.Terms
< import Lib.Types
< import Lib.TypedTerms
< import Lib.Substitute
< import Lib.Util
<
< %default total


Reduction
---------

We can now define reduction. We begin with small-step reduction. Not all terms
can reduce, it is thus important that the result is of type Maybe PCFTerm.

< public export
> smallStep    : {k : _} -> PCFTerm k -> Maybe (PCFTerm k)

Neither variables nor top-level lambdas are reducable, so we restrict attention to the symbols


> smallStep (S s arg) = ssSym s arg where 
>   ssSym : Symbol ar -> Vect ar (PCFTerm k) -> Maybe (PCFTerm k)

We start with the top-level reducts

>   ssSym Pred [S Zero []]      = JustS Zero []   -- JustS s ms is defined as Just (S s ms)
>   ssSym Pred [S Succ [m]]     = Just m

>   ssSym IsZero [S Zero _]     = JustS T []
>   ssSym IsZero [S Succ _]     = JustS F []
> 
>   ssSym App [(L _ m), n]      = Just (substitute m n)
> 
>   ssSym Fst [S Pair [m, _]]   = Just m
>   ssSym Snd [S Pair [_, n]]   = Just n
> 
>   ssSym IfElse [S T _, m, _]  = Just m
>   ssSym IfElse [S F _, _, n]  = Just n
> 
>   ssSym Y [m]                 = Just (S App [m, (S Y [m])])

If a term had no top-level reducts, then we try to reduce its first argument.
The only exception is Pair, which does not evaluate its arguments at all.

>   ssSym Pair _                = Nothing
>   ssSym s (m::ms)             = JustS s (!(smallStep m) :: ms)

Alternatively, if the term is of the unit type, but not the unit value itself, we reduce it to the 
unit value

>   ssSym Unit _ = Nothing
>   ssSym s arg = let m = (S s arg) in
>                 case tryClose m >>= typeOfClosed of
>                   Just PCFUnit => Just (S Unit [])
>                   _            => Nothing
>
> smallStep _         = Nothing



### Include Lib.Values here

Values are exactly the normal forms for small-step reduction, that is, values
are the terms that cannot be reduced further.

By successively applying small-step reductions, terms can reduce to values.
This is the so called big-step reduction.

< public export
> partial eval : ClosedPCFTerm -> ClosedPCFTerm
> eval (L t m)        = L t m
> eval (S Pair ms)    = S Pair ms
> eval (S Y [m])      = eval (S App [m, S Y [m]])
> eval (S IfElse [p, m, n]) = case (eval p) of
>                               (S T []) => eval m
>                               (S F []) => eval n
>                               p'       => (S IfElse [p', m, n])
> eval (S s [])         = (S s [])  -- constants eval to themselves
> eval (S s (m :: ms))  = evSym s (eval m :: ms) where
>   evSym : Symbol ar -> Vect ar ClosedPCFTerm -> ClosedPCFTerm
>   evSym Pred    [S Zero _]    = S Zero []
>   evSym Pred    [S Succ [m]]  = m
>   evSym IsZero  [S Zero _]    = S T []
>   evSym IsZero  [S Succ _]    = S F []
>   evSym App     [L _ m, n]    = eval (substitute m n)
>   evSym Fst   [S Pair [m, _]] = m
>   evSym Snd   [S Pair [_, n]] = n
>   evSym s ms = let m = (S s ms) in
>                if ((tryClose m >>= typeOfClosed) == Just PCFUnit)
>                   then (S Unit [])
>                   else (S s ms)     -- everything that hasn't evaluated so far, just evaluates to itself


