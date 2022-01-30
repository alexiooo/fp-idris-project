
< module Lib.Reduction
<
< import public Lib.Terms
< import public Lib.Types
< import public Lib.TypedTerms
< import public Lib.Substitute
< import public Lib.Values
< import public Lib.Util
<
< import Data.Fuel
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

Not all PCFTerms evaluate to a Value, some may enter an infinite loop.
To still define eval as a total function, we supply it with some `fuel'. This fuel acts as an upper
bound on computation steps. The function will only return Nothing if this upper bound was reached

< public export
> eval : Fuel -> ClosedPCFTerm -> Maybe ClosedPCFTerm
> eval Dry _ = Nothing
> eval (More f) (L t m)        = Just $ L t m
> eval (More f) (S Pair ms)    = JustS Pair ms
> eval (More f) (S Y [m])      = eval f (S App [m, S Y [m]])
> eval (More f) (S IfElse [p, m, n]) = case !(eval f p) of
>                                         (S T []) => eval f m
>                                         (S F []) => eval f n
>                                         p'       => JustS IfElse [p', m, n]
> eval (More f) (S s [])         = JustS s []  -- constants eval to themselves
> eval (More f) (S s (m :: ms))  = evSym s (!(eval f m) :: ms) where
>   evSym : Symbol ar -> Vect ar ClosedPCFTerm -> Maybe ClosedPCFTerm
>   evSym Pred    [S Zero _]    = JustS Zero []
>   evSym Pred    [S Succ [m]]  = Just m
>   evSym IsZero  [S Zero _]    = JustS T []
>   evSym IsZero  [S Succ _]    = JustS F []
>   evSym App     [L _ m, n]    = eval f (substitute m n)
>   evSym Fst   [S Pair [m, _]] = Just m
>   evSym Snd   [S Pair [_, n]] = Just n
>   evSym s ms = let m = (S s ms) in
>                case tryClose m >>= typeOfClosed of
>                   Just PCFUnit => Just (S Unit [])
>                   -- everything that hasn't evaluated so far, just evaluates to itself
>                   -- notice that we are using the evaluated first argument here, not the original
>                   -- one
>                   _            => Just m


