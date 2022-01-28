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

Remember that the type only gives an upper bound, so an inhabitant of say PCFType 3 might still
be closed. The following will try to strengthen any such term.
This really is just a wrapper around Fin.strengthen, with straightforward recursive cases, so we 
detail only variables and lambdas.

> strengthen : {k :_} -> PCFTerm (S k) -> Maybe (PCFTerm k)
> strengthen (V v)    = Fin.strengthen v >>= Just . V
> strengthen (L t m)  = strengthen m     >>= Just . L t

< strengthen (C m n)            = Just (C !(strengthen m) !(strengthen n))
< strengthen (P m n)            = Just (P !(strengthen m) !(strengthen n))
< strengthen (P1 m)             = strengthen m >>= Just . P1
< strengthen (P2 m)             = strengthen m >>= Just . P2
< strengthen T                  = Just T
< strengthen F                  = Just F
< strengthen Zero               = Just Zero
< strengthen (Succ m)           = strengthen m >>= Just . Succ
< strengthen (Pred m)           = strengthen m >>= Just . Pred
< strengthen (IsZero m)         = strengthen m >>= Just . IsZero
< strengthen (IfThenElse p m n) = do p <- strengthen p
<                                    m <- strengthen m
<                                    n <- strengthen n
<                                    Just (IfThenElse p m n)
< strengthen (Y m)              = strengthen m >>= Just . Y
< strengthen I                  = Just I

> public export
> tryClose : {k:_} -> PCFTerm k -> Maybe ClosedPCFTerm
> tryClose {k} t = case k of 
>                   0      => Just t
>                   (S k') => strengthen t >>= tryClose 

We are now able to define equality for terms. The important case is
lambda-abstraction. We are using de Bruijn indices, which make comparing terms
very easy.

> implementation Eq (PCFTerm k) where
>   V v              == V w              = v == w
>   C m n            == C p q            = m == p && n == q
>   L a m            == L b n            = a == b && m == n

The other cases are just as simple.

<   P m n            == P p q            = m == p && n == q
<   P1 m             == P1 n             = m == n
<   P2 m             == P2 n             = m == n
<   T                == T                = True
<   F                == F                = True
<   Zero             == Zero             = True
<   Succ m           == Succ n           = m == n
<   Pred m           == Pred n           = m == n
<   IsZero m         == IsZero n         = m == n
<   IfThenElse m n p == IfThenElse q r s = m == q && n == r && p == s
<   Y m              == Y n              = m == n
<   I                == I                = True
>   _                == _                = False

In order to define small-step reduction, we must be able to substitute a term
for a variable in another term. 
We only allow the maximal variable, indicated k in the following signature, to be substituted,
so that we can decrease that upper bound by one for the return type and maintain a sharp upper bound.

The following functions implement this.

> public export
> total substitute : {k :_} -> PCFTerm (S k) -> PCFTerm k -> PCFTerm k

When substituting a term inside another, we might need to rename (increase)
free variables. The following function does this.
The depth argument keeps track of how many lambda's have been encoutered, 
while the types reflect that the upper bound on free variables also increases.

> total incFreeVar : (n : Nat) -> PCFTerm k -> PCFTerm (S k)
> incFreeVar depth (V v)              = if (finToNat v) < depth
>                                       then (V (weaken v))
>                                       else (V (FS v))
> incFreeVar depth (L t m)            = L t (incFreeVar (S depth) m)

The other cases are uninteresting, the increment function is just passed on.

< incFreeVar depth (C m n)            = C (incFreeVar depth m) (incFreeVar depth n)
< incFreeVar depth (P m n)            = P (incFreeVar depth m) (incFreeVar depth n)
< incFreeVar depth (P1 m)             = P1 (incFreeVar depth m)
< incFreeVar depth (P2 m)             = P2 (incFreeVar depth m)
< incFreeVar depth T                  = T
< incFreeVar depth F                  = F
< incFreeVar depth Zero               = Zero
< incFreeVar depth (Succ m)           = Succ (incFreeVar depth m)
< incFreeVar depth (Pred m)           = Pred (incFreeVar depth m)
< incFreeVar depth (IsZero m)         = IsZero (incFreeVar depth m)
< incFreeVar depth (IfThenElse p m n) =
<     IfThenElse (incFreeVar depth p) (incFreeVar depth m) (incFreeVar depth n)
< incFreeVar depth (Y m)              = Y (incFreeVar depth m)
< incFreeVar depth I                  = I

The important cases are the variables and lambda-abstractions.

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

< substitute (C m n)            s = C (substitute m s) (substitute n s)
< substitute (P m n)            s = P (substitute m s) (substitute n s)
< substitute (P1 m)             s = P1 (substitute m s)
< substitute (P2 m)             s = P2 (substitute m s)
< substitute T                  s = T
< substitute F                  s = F
< substitute Zero               s = Zero
< substitute (Succ m)           s = Succ (substitute m s)
< substitute (Pred m)           s = Pred (substitute m s)
< substitute (IsZero m)         s = IsZero (substitute m s)
< substitute (IfThenElse p m n) s =
<     IfThenElse (substitute p s ) (substitute m s) (substitute n s)
< substitute (Y m)              s = Y (substitute m s)
< substitute I                  s = I


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
> smallStep (IfThenElse T m _)    = Just m
> smallStep (IfThenElse F _ n)    = Just n
> smallStep (IfThenElse p m n)    = do p' <- smallStep p
>                                      Just (IfThenElse p' m n)
>
> smallStep (Y m)                 = Just (C m (Y m))
>
> smallStep m = if (m /= I && (tryClose m >>= typeOfClosed) == Just U) 
>               then Just I
>               else Nothing

An important notion is a value, which is a term that cannot be reduced further.

> public export
> total isValue : PCFTerm k -> Bool
> isValue T        = True
> isValue F        = True
> isValue Zero     = True
> isValue (Succ m) = isValue m
> isValue (P m n)  = True
> isValue (L t m)  = True
> isValue I        = True
> isValue _        = False

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
> eval (IfThenElse T m _) = eval m
> eval (IfThenElse F _ n) = eval n
> eval (IfThenElse p m n) = eval (IfThenElse (eval p) m n)
> eval (Y m)              = eval (C m (Y m))
> eval m with (typeOfClosed m)
>        _ | Just U       = I





