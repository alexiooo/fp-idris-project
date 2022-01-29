
< module Lib.Substitute
<
< import Lib.Terms

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