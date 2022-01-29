
< module Lib.Reduction
<
< import Lib.Terms
< import Lib.Types
< import Lib.TypedTerms
< import Lib.Substitute
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
>   JustS : Symbol ar -> Vect ar (PCFTerm k) -> Maybe (PCFTerm k)
>   JustS s arg = Just $ S s arg
>   ssSym : Symbol ar -> Vect ar (PCFTerm k) -> Maybe (PCFTerm k)

We start with the top-level reducts

>   ssSym Pred [S Zero []]      = JustS Zero _
>   ssSym Pred [S Succ [m]]     = Just m

>   ssSym IsZero [S Zero _]     = JustS T _
>   ssSym IsZero [S Succ _]     = JustS F _
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

If a term had no top-level reducts, then we try to reduce the first argument.
Alternatively, if the term is a nullary symbol and of the unit type, we reduce it to the unit value

>   ssSym s (m::ms)             = JustS s (!(smallStep m) :: ms)
>   ssSym s arg = let m = (S s arg) in
>                      if (m /= (S Unit _) && (tryClose m >>= typeOfClosed) == Just PCFUnit)
>                         then Just (S Unit [])
>                         else Nothing

> smallStep _         = Nothing



### Include Lib.Values here

Values are exactly the normal forms for small-step reduction, that is, values
are the terms that cannot be reduced further.

By successively applying small-step reductions, terms can reduce to values.
This is the so called big-step reduction.

> public export
> partial eval : ClosedTypedTerm -> ClosedTypedTerm
> eval T                  = T
> eval F                  = F
> eval Zero               = Zero
> eval (P m n)            = (P m n)
> eval (L t m)            = (L t m)
> eval (Pred Zero)        = Zero
> eval (Pred (Succ m))    = m
> eval (Pred m)           = Pred (eval m)
> eval (IsZero Zero)      = T
> eval (IsZero (Succ m))  = F
> eval (IsZero m)         = IsZero (eval m)
> eval (Succ m)           = Succ (eval m)
> eval (C (L t m) n)      = eval (substitute m n)
> eval (C m n)            = C (eval m) n
> eval (P1 (P m _))       = eval m
> eval (P2 (P _ n))       = eval n
> eval (P1 m)             = P1 (eval m)
> eval (P2 m)             = P2 (eval m)
> eval (IfElse T m _) = eval m
> eval (IfElse F _ n) = eval n
> eval (IfElse p m n) = eval (IfElse (eval p) m n)
> eval (Y m)              = eval (C m (Y m))
> eval m with (typeOfClosed m)
>        _ | Just PCFUnit = I


