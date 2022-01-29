
< module Lib.Values

< import Lib.PCF
< import Data.Maybe

Values and Normal Forms
-------------

A certain subset of terms are called `values'

> namespace Value
>   public export
>   data PCFValue : Nat -> Type where
>     T     : PCFValue k
>     F     : PCFValue k
>     Zero  : PCFValue k
>     Succ  : PCFValue k -> PCFValue k
>     I     : PCFValue k
>     P     : PCFTerm k -> PCFTerm k     -> PCFValue k
>     L     : PCFType   -> PCFTerm (S k) -> PCFValue k
>
>   public export
>   fromTerm : PCFTerm k -> Maybe (PCFValue k)
>   fromTerm T          = Just T
>   fromTerm F          = Just F
>   fromTerm Zero       = Just Zero
>   fromTerm (Succ t)   = do v <- fromTerm t
>                            Just (Succ v)
>   fromTerm I          = Just I
>   fromTerm (P m n)    = Just (P m n)
>   fromTerm (L t m)    = Just (L t m)
>   fromTerm _          = Nothing
>
>   public export
>   total isValue : PCFTerm k -> Bool
>   isValue T        = True
>   isValue F        = True
>   isValue Zero     = True
>   isValue (Succ m) = isValue m
>   isValue (P m n)  = True
>   isValue (L t m)  = True
>   isValue I        = True
>   isValue _        = False

>   public export
>   toTerm : PCFValue k -> PCFTerm k
>   toTerm T          = T
>   toTerm F          = F
>   toTerm Zero       = Zero
>   toTerm (Succ v)   = Succ (toTerm v)
>   toTerm I          = I
>   toTerm (P m n)    = P m n
>   toTerm (L t m)  = L t m

Values correspond exactly to terms that are in normal forms

>   valuesAreNormalForms : (v : PCFValue 0) -> smallStep (toTerm v) = Nothing
>   valuesAreNormalForms T        = Refl
>   valuesAreNormalForms F        = Refl
>   valuesAreNormalForms Zero     = Refl
>   valuesAreNormalForms (Succ t) = rewrite (valuesAreNormalForms t)
>                                   in Refl
>   valuesAreNormalForms I        = Refl
>   valuesAreNormalForms (P m n)  = ?pair
>   valuesAreNormalForms (L t m)  = ?lambda

-- >   normalFormsAreValues : (t : PCFTerm) -> {auto hnf : smallStep t = Nothing} -> exists (\v -> fromTerm t = Just v)
-- >   normalFormsAreValues = ?undefined2
