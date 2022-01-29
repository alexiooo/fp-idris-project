
< module Lib.Reduction
<
< import Lib.Terms
< import Lib.Substitute


Reduction
---------

We can now define reduction. We begin with small-step reduction. Not all terms
can reduce, it is thus important that the result is of type Maybe PCFTerm.

< public export
> total smallStep    : PCFTerm k -> Maybe (PCFTerm k)
< public export
> total smallStepSym : Symbol ar -> Vect ar (PCFTerm k) -> Maybe (PCFTerm k)

> smallStep (S s ms) = smallStepSym s ms
> smallStep m = if (m /= (S Unit) && (tryClose m >>= typeOfClosed) == Just U)
>               then Just I
>               else Nothing

> smallStep (Pred Zero)           = Just Zero
> smallStep (Pred (Succ m))       = Just m
> smallStep (Pred m)              = do n <- smallStep m
>                                      Just (Pred n)
>
> smallStep (IsZero Zero)         = Just T
> smallStep (IsZero (Succ m))     = Just F
> smallStep (IsZero m)            = do n <- smallStep m
>                                      Just (IsZero (n))
>
> smallStep (Succ m)              = do n <- smallStep m
>                                      Just (Succ n)
>
> smallStep (C (L _ m) n)         = Just (substitute m n)
> smallStep (C m p)               = do n <- smallStep m
>                                      Just (C n p)
>
> smallStep (P1 (P m _))          = Just m
> smallStep (P2 (P _ n))          = Just n
> smallStep (P1 m)                = do n <- smallStep m
>                                      Just (P1 n)
> smallStep (P2 m)                = do n <- smallStep m
>                                      Just (P2 n)
>
> smallStep (IfElse T m _)    = Just m
> smallStep (IfElse F _ n)    = Just n
> smallStep (IfElse p m n)    = do p' <- smallStep p
>                                  Just (IfElse p' m n)
>
> smallStep (Y m)                 = Just (C m (Y m))
>



### Include Lib.Values here

Values are exactly the normal forms for small-step reduction, that is, values
are the terms that cannot be reduced further.

By successively applying small-step reductions, terms can reduce to values.
This is the so called big-step reduction.

> public export
> partial eval : ClosedPCFTerm -> ClosedPCFTerm
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


