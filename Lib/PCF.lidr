> module Lib.PCF
>
> import Data.List

Terms for PCF
-------------

PCF is a simple language that models computing. Its types are as follows.

> data PCFType = PCFBool
>              | PCFNat
>              | (~>) PCFType PCFType
>              | (*) PCFType PCFType
> --           | U
>
> infixr 0 ~>
> infixr 0 *

We want our type to be comparable. This definition enforces unique readability.

> implementation Eq PCFType where
>   PCFBool  == PCFBool  = True
>   PCFNat   == PCFNat   = True
>   (a ~> b) == (c ~> d) = a == c && b == d
>   (a * b)  == (c * d)  = a == c && b == d
>   _        == _        = False

We begin by defining terms.

> Var = String
>
> data PCFTerm = V Var
>              | C PCFTerm PCFTerm
>              | L Var PCFType PCFTerm
>              | P PCFTerm PCFTerm
>              | P1 PCFTerm
>              | P2 PCFTerm
>              | T
>              | F
>              | Zero
>              | Succ PCFTerm
>              | Pred PCFTerm
>              | IsZero PCFTerm
>              | IfThenElse PCFTerm PCFTerm PCFTerm
>              | Y PCFTerm
> --           | I

Our goal here is to write a function that returns the type of any term:

> typeOf : PCFTerm -> Maybe PCFType

Before defining reduction, we need to define substitution.

> substitute : PCFTerm -> PCFTerm -> Var -> PCFTerm

The base case is substitution of a variable.

> substitute   (V w)              s  v    = if v == w then s else V w

When substituting in a lambda abstraction, we have to pay attention to not
substitute bound variables.

> substitute   (L w t m)          s  v    = if v == w then L v t m else L w t (substitute m s v)

The other cases are straightforward, the substitution is simply done recursively.

> substitute   (C m n)            s  v    = C (substitute m s v) (substitute n s v)
> substitute   (P m n)            s  v    = P (substitute m s v) (substitute n s v)
> substitute   (P1 m)             s  v    = P1 (substitute m s v)
> substitute   (P2 m)             s  v    = P2 (substitute m s v)
> substitute   T                  s  v    = T
> substitute   F                  s  v    = F
> substitute   Zero               s  v    = Zero
> substitute   (Succ m)           s  v    = Succ (substitute m s v)
> substitute   (Pred m)           s  v    = Pred (substitute m s v)
> substitute   (IsZero m)         s  v    = IsZero (substitute m s v)
> substitute   (IfThenElse p m n) s  v    = IfThenElse (substitute p s v) (substitute m s v) (substitute n s v)
> substitute   (Y m)              s  v    = Y (substitute m s v)
> --substitute   I                  s  v    = I

This allows us to define small-step reduction. Not all terms can reduce,
it is thus important that the result is of type Maybe PCFTerm

> smallStep : PCFTerm           -> Maybe PCFTerm
> smallStep   (Pred Zero)        = Just Zero
> smallStep   (Pred (Succ m))    = Just m
> smallStep   (Pred m)           = map Pred (smallStep m)
> smallStep   (IsZero Zero)      = Just T
> smallStep   (IsZero (Succ m))  = Just F
> smallStep   (IsZero m)         = map IsZero (smallStep m)
> smallStep   (Succ m)           = map Succ (smallStep m )
> smallStep   (C (L v t m) n)    = Just (substitute m n v)
> smallStep   (C m n)            = map (`C` n) (smallStep m)
> smallStep   (P1 (P m n))       = Just m
> smallStep   (P2 (P m n))       = Just n
> smallStep   (P1 m)             = map P1 (smallStep m)
> smallStep   (P2 m)             = map P2 (smallStep m)
> smallStep   (IfThenElse T m n) = Just m
> smallStep   (IfThenElse F m n) = Just n
> smallStep   (IfThenElse p m n) = map (\p => IfThenElse p m n) (smallStep p)
> smallStep   (Y m)              = Just (C m (Y m))
> --smallStep   m with (typeOf m)
> --smallStep   m | Just U       = if m /= I
> --                                 then Just I
> --                               else Nothing
> --smallStep   m | _            = Nothing
> smallStep   _                  = Nothing

An important notion is a value, which is a term that cannot be reduced further.

> isValue : PCFTerm  -> Bool
> isValue   T         = True
> isValue   F         = True
> isValue   Zero      = True
> isValue   (Succ m)  = isValue m
> isValue   (P m n)   = True
> isValue   (L v t m) = True
> isValue   _         = False

Values are exactly the normal forms for small-step reduction, that is, values
are the terms that cannot be reduced further.

By successively applying small-step reductions, terms can reduce to values.
This is the so called big-step reduction.

> eval : PCFTerm           -> PCFTerm
> eval   (Pred Zero)        = Zero
> eval   (Pred (Succ m))    = eval m
> eval   (Pred m)           = eval $ Pred (eval m)
> eval   (IsZero Zero)      = T
> eval   (IsZero (Succ m))  = F
> eval   (IsZero m)         = eval $ IsZero (eval m)
> eval   (Succ m)           = Succ (eval m)
> eval   (C (L v t m) n)    = eval $ substitute m n v
> eval   (C m n)            = eval $ C (eval m) n
> eval   (P1 (P m n))       = eval m
> eval   (P2 (P m n))       = eval n
> eval   (P1 m)             = eval $ P1 (eval m)
> eval   (P2 m)             = eval $ P2 (eval m)
> eval   (IfThenElse T m n) = eval m
> eval   (IfThenElse F m n) = eval n
> eval   (IfThenElse p m n) = eval $ IfThenElse (eval p) m n
> eval   (Y m)              = eval $ C m (Y m)      -- /!\ This can create infinite loops
> --eval   m with (typeOf m)
> --eval   m | Just U       = I
> --eval   m | _            = m
> eval   m                  = m

Type Checking
-------------

> typeOfEnv : List (Var, PCFType) -> PCFTerm                           -> Maybe PCFType
> typeOfEnv   env                    (V v)                                = lookup v env
> typeOfEnv   env                    (C m n)            with (typeOfEnv env m)
>   typeOfEnv   env                    (C m n)            | Just (a ~> b) = if Just a == typeOfEnv env n
>                                                                             then Just b
>                                                                           else Nothing
>   typeOfEnv   env                    (C m n)            | _             = Nothing
> typeOfEnv   env                    (L v t m)          with (typeOfEnv ((v,t)::env) m)
>   typeOfEnv   env                    (L v t m)          | Just a        = Just (t ~> a)
>   typeOfEnv   env                    (L v t m)          | _             = Nothing
> typeOfEnv   env                    (P m n)                              = (map (*) (typeOfEnv env m)) <*> (typeOfEnv env n)
> typeOfEnv   env                    (P1 m)             with (typeOfEnv env m)
>   typeOfEnv   env                    (P1 m)             | Just (a * b)  = Just a
>   typeOfEnv   env                    (P1 m)             | _             = Nothing
> typeOfEnv   env                    (P2 m)             with (typeOfEnv env m)
>   typeOfEnv   env                    (P2 m)             | Just (a * b)  = Just b
>   typeOfEnv   env                    (P2 m)             | _             = Nothing
> typeOfEnv   env                    T                                    = Just PCFBool
> typeOfEnv   env                    F                                    = Just PCFBool
> typeOfEnv   env                    Zero                                 = Just PCFNat
> typeOfEnv   env                    (Succ m)           with (typeOfEnv env m)
>   typeOfEnv   env                    (Succ m)           | Just PCFNat   = Just PCFNat
>   typeOfEnv   env                    (Succ m)           | _             = Nothing
> typeOfEnv   env                    (Pred m)           with (typeOfEnv env m)
>   typeOfEnv   env                    (Pred m)           | Just PCFNat   = Just PCFNat
>   typeOfEnv   env                    (Pred m)           | _             = Nothing
> typeOfEnv   env                    (IsZero m)         with (typeOfEnv env m)
>   typeOfEnv   env                    (IsZero m)         | Just PCFNat   = Just PCFBool
>   typeOfEnv   env                    (IsZero m)         | _             = Nothing
> typeOfEnv   env                    (IfThenElse p m n) with (typeOfEnv env p)
>   typeOfEnv   env                    (IfThenElse p m n) | Just PCFBool  = let t1 = typeOfEnv env m
>                                                                               t2 = typeOfEnv env n
>                                                                           in if t1 == t2
>                                                                                then t1
>                                                                              else Nothing
>   typeOfEnv   env                    (IfThenElse p m n) | _             = Nothing
> typeOfEnv   env                    (Y m)              with (typeOfEnv env m)
>   typeOfEnv   env                    (Y m)              | Just (a ~> b) = if a == b
>                                                                             then Just a
>                                                                           else Nothing
>   typeOfEnv   env                    (Y m)              | _             = Nothing
> --typeOfEnv   env                    I                                    = Just U

> typeOf = typeOfEnv []
