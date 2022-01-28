
> module Lib.Type
> 
> import Lib.PCF
> import public Data.Vect

Type Checking
-------------

We are now ready to define a type infering function. Such a function takes as
arguments a context and a term, and return a type if the term is typeable in
the given context, or Nothing otherwise.

We've been keeping track of free variables in the type of terms, 
so we'd like to restrict to contexts that actually provide a type for all (potential) free variables

< public export
> Context : Nat -> Type
> Context n = Vect n PCFType

< public export
> total typeOf : Context k -> PCFTerm k -> Maybe PCFType
> typeOf con (V v)                               = Just (index v con)
>
> typeOf con (C m n) with (typeOf con m)
>   typeOf con (C m n) | Just (a ~> b)           = if Just a == typeOf con n
>                                                    then Just b
>                                                  else Nothing
>   typeOf con (C m n) | _                       = Nothing
>
> typeOf con (L t m) with (typeOf (t::con) m)
>   typeOf con (L t m) | Just a                  = Just (t ~> a)
>   typeOf con (L t m) | _                       = Nothing
>
> typeOf con (P m n)                             = (map (*) (typeOf con m)) <*> (typeOf con n)
>
> typeOf con (P1 m) with (typeOf con m)
>   typeOf con (P1 m) | Just (a * b)             = Just a
>   typeOf con (P1 m) | _                        = Nothing
>
> typeOf con (P2 m) with (typeOf con m)
>   typeOf con (P2 m) | Just (a * b)             = Just b
>   typeOf con (P2 m) | _                        = Nothing
>
> typeOf con T                                   = Just PCFBool
>
> typeOf con F                                   = Just PCFBool
>
> typeOf con Zero                                = Just PCFNat
>
> typeOf con (Succ m) with (typeOf con m)
>   typeOf con (Succ m) | Just PCFNat            = Just PCFNat
>   typeOf con (Succ m) | _                      = Nothing
>
> typeOf con (Pred m) with (typeOf con m)
>   typeOf con (Pred m) | Just PCFNat            = Just PCFNat
>   typeOf con (Pred m) | _                      = Nothing
>
> typeOf con (IsZero m) with (typeOf con m)
>   typeOf con (IsZero m) | Just PCFNat          = Just PCFBool
>   typeOf con (IsZero m) | _                    = Nothing
>
> typeOf con (IfThenElse p m n) with (typeOf con p)
>   typeOf con (IfThenElse p m n) | Just PCFBool = let t1 = typeOf con m
>                                                      t2 = typeOf con n
>                                                  in if t1 == t2
>                                                       then t1
>                                                     else Nothing
>   typeOf con (IfThenElse p m n) | _            = Nothing
>
> typeOf con (Y m) with (typeOf con m)
>   typeOf con (Y m) | Just (a ~> b)             = if a == b
>                                                    then Just a
>                                                  else Nothing
>   typeOf con (Y m) | _                         = Nothing
>
> typeOf con I                                   = Just U

Closed terms are typeable exactly when they are typeable with an empty context.

> typeOfClosed = typeOf []


