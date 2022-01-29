> module Lib.PCF
>
> import public Lib.Terms
> import public Lib.Type
> import Data.Fin
> import Data.List
> import Data.Vect
> import Data.DPair

### Include Lib.Terms here

### Include Lib.Type here

In order to define small-step reduction, we must be able to substitute a term
for a variable in another term.
We only allow the maximal variable, indicated k in the following signature, to be substituted,
so that we can decrease that upper bound by one for the return type and maintain a sharp upper bound.

When substituting a term inside another, we might need to rename (increase)
free variables. The following function does this.
The depth argument keeps track of how many lambda's have been encoutered,
while the types reflect that the upper bound on free variables also increases.

Because of the totality checker, we have to give a *Vect version of the function as well, following 
the same pattern as we did while type checking.

> total incFreeVar : (n : Nat) -> PCFTerm k -> PCFTerm (S k)

> total incFreeVarVect : (n : Nat) -> Vect m (PCFTerm k) -> Vect m (PCFTerm (S k))
> incFreeVarVect x (y::ys) = (incFreeVar x y) :: (incFreeVarVect x ys)
> incFreeVarVect _ [] = []

> incFreeVar depth (V v)    = if (finToNat v) < depth
>                               then (V (weaken v))
>                               else (V (FS v))
> incFreeVar depth (L t m)  = L t (incFreeVar (S depth) m)
> incFreeVar depth (S s ms) = S s (incFreeVarVect depth ms)


< public export
> total substitute : {k :_} -> PCFTerm (S k) -> PCFTerm k -> PCFTerm k

Note that in the *Vect version, we flip the term arguments to be consistent with earlier *Vect functions
> total substituteVect : {k :_} -> PCFTerm k -> Vect n (PCFTerm (S k)) -> Vect n (PCFTerm k)

We try to strengthen (i.e., decrement) the bound on the variable index.
The only reason for this to fail is if the index is already at the upper bound; if w == k, thus
if strengthening fails, we should substitute

> substitute (V w) s =  case Fin.strengthen w of
>                         Nothing => s
>                         Just w' => V w'

Recall that the body of a lambda has one more (potential) free-variable, thus the upper bound is
automatically incremented

> substitute (L t m) s = L t (substitute m (incFreeVar 0 s))

All the other cases are straightforward, once again, the substitution is just passed on.

> substitute (S sym ms) s = S sym (substituteVect s ms)
> substituteVect x (y::ys) = (substitute y x) :: (substituteVect x ys)
> substituteVect _ [] = []


Reduction
---------

We can now define reduction. We begin with small-step reduction. Not all terms
can reduce, it is thus important that the result is of type Maybe PCFTerm.

> public export
> total smallStep : {k :_} -> PCFTerm k -> Maybe (PCFTerm k)
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
> smallStep m = if (m /= I && (tryClose m >>= typeOfClosed) == Just U)
>               then Just I
>               else Nothing


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





