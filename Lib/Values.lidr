
< module Lib.Values

< import Lib.Types
< import Lib.Terms
< import Data.Maybe
<
< %default total

Values and Normal Forms
-------------

A certain subset of terms are called `values'

> public export
> data PCFValue : Nat -> Type where
>   ||| All constants (nullary symbols) are values
>   C     : Symbol 0 -> PCFValue k 
>   Succ  : PCFValue k -> PCFValue k
>   Pair  : PCFTerm k -> PCFTerm k     -> PCFValue k
>   L     : PCFType   -> PCFTerm (S k) -> PCFValue k


Some terms are values
< public export
> fromTerm : PCFTerm k -> Maybe (PCFValue k)
> fromTerm (L t m)        = Just (L t m)
> fromTerm (S s [])       = Just (C s)
> fromTerm (S Succ [m])   = Just (Succ !(fromTerm m))
> fromTerm (S Pair [m,n]) = Just (Pair m n)
> fromTerm _              = Nothing

All values are terms
< public export
> toTerm : PCFValue k -> PCFTerm k
> toTerm (C s)      = S s []
> toTerm (Succ v)   = S Succ [toTerm v]
> toTerm (Pair m n) = S Pair [m, n]
> toTerm (L t m)    = L t m

< public export
> isValue : PCFTerm k -> Bool
> isValue t = case fromTerm t of 
>                Nothing  => False
>                _        => True

Values correspond exactly to terms that are in normal forms

-- >   valuesAreNormalForms : (v : PCFValue 0) -> smallStep (toTerm v) = Nothing
-- >   valuesAreNormalForms T        = Refl
-- >   valuesAreNormalForms F        = Refl
-- >   valuesAreNormalForms Zero     = Refl
-- >   valuesAreNormalForms (Succ t) = rewrite (valuesAreNormalForms t)
-- >                                   in Refl
-- >   valuesAreNormalForms I        = Refl
-- >   valuesAreNormalForms (P m n)  = ?pair
-- >   valuesAreNormalForms (L t m)  = ?lambda

-- >   normalFormsAreValues : (t : PCFTerm) -> {auto hnf : smallStep t = Nothing} -> exists (\v -> fromTerm t = Just v)
-- >   normalFormsAreValues = ?undefined2
