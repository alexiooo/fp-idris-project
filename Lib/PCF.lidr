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
>              | U
>
> infixr 0 ~>
> infixr 0 *

We want our types to be comparable. This definition enforces unique readability.

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
>              | I

The Y constructor returns a fixed-point of the given term. It is required to
define functions by recursion. For examplen the sum function on PCFNat is
defined recursively.

> sum : PCFTerm
> sum = Y (L "f" (PCFNat ~> (PCFNat ~> PCFNat)) (L "m" PCFNat (L "n" PCFNat (IfThenElse (IsZero (V "n")) (V "m") (Succ (C (C (V "f") (V "m")) (Pred (V "n"))))))))

Our goal here is to write a function that returns the type of any closed term

> total
> typeOfClosed : PCFTerm -> Maybe PCFType

We also want our terms to be comparable. However, we have to pay particular
attention to alpha-equivalence. In order to implement that, we must define
substitution first.

We want to be able to substitute terms for variable.
The following function implements that.

> total
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
> substitute   I                  s  v    = I

We are now able to define equality for terms. The important case is lambda-abstraction.

> implementation Eq PCFTerm where
>   L v a m          == L w b n          = a == b && m == substitute n (V v) w

The other cases are straightforward.

>   V v              == V w      = v == w
>   C m n            == C p q    = m == p && n == q
>   P m n            == P p q            = m == p && n == q
>   P1 m             == P1 n             = m == n
>   P2 m             == P2 n             = m == n
>   T                == T                = True
>   F                == F                = True
>   Zero             == Zero             = True
>   Succ m           == Succ n           = m == n
>   Pred m           == Pred n           = m == n
>   IsZero m         == IsZero n         = m == n
>   IfThenElse m n p == IfThenElse q r s = m == q && n == r && p == s
>   Y m              == Y n              = m == n
>   I                == I                = True
>   _                == _                = False

Reduction
---------

We can now define reduction. We begin with small-step reduction. Not all terms
can reduce, it is thus important that the result is of type Maybe PCFTerm.

> partial
> smallStep : PCFTerm               -> PCFTerm
> smallStep   (Pred Zero)            = Zero
> smallStep   (Pred (Succ m))        = m
> smallStep   (Pred m)               = Pred (smallStep m)
> smallStep   (IsZero Zero)          = T
> smallStep   (IsZero (Succ m))      = F
> smallStep   (IsZero m)             = IsZero (smallStep m)
> smallStep   (Succ m)               = Succ (smallStep m )
> smallStep   (C (L v t m) n)        = substitute m n v
> smallStep   (C m n)                = C (smallStep m) n
> smallStep   (P1 (P m n))           = m
> smallStep   (P2 (P m n))           = n
> smallStep   (P1 m)                 = P1 (smallStep m)
> smallStep   (P2 m)                 = P2 (smallStep m)
> smallStep   (IfThenElse T m n)     = m
> smallStep   (IfThenElse F m n)     = n
> smallStep   (IfThenElse p m n)     = IfThenElse (smallStep p) m n
> smallStep   (Y m)                  = C m (Y m)
> smallStep   m with (typeOfClosed m, m == I)
>    smallStep   m | (Just U, False) = I

An important notion is a value, which is a term that cannot be reduced further.

> total
> isValue : PCFTerm  -> Bool
> isValue   T         = True
> isValue   F         = True
> isValue   Zero      = True
> isValue   (Succ m)  = isValue m
> isValue   (P m n)   = True
> isValue   (L v t m) = True
> isValue   I         = True
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
> eval   m with (typeOfClosed m)
>   eval   m | Just U       = I
>   eval   m | _            = m

Type Checking
-------------

We are now ready to define a type infering function. Such a function takes as
arguments a context and a term, and return a type if the term is typeable in
the given context, or Nothing otherwise.

> Context = List (Var, PCFType)
>
> total
> typeOf : Context -> PCFTerm                             -> Maybe PCFType
> typeOf   con        (V v)                                = lookup v con
>
> typeOf   con        (C m n)            with (typeOf con m)
>   typeOf   con        (C m n)            | Just (a ~> b) = if Just a == typeOf con n
>                                                              then Just b
>                                                            else Nothing
>   typeOf   con        (C m n)            | _             = Nothing
>
> typeOf   con        (L v t m)          with (typeOf ((v,t)::con) m)
>   typeOf   con        (L v t m)          | Just a        = Just (t ~> a)
>   typeOf   con        (L v t m)          | _             = Nothing
>
> typeOf   con        (P m n)                              = (map (*) (typeOf con m)) <*> (typeOf con n)
>
> typeOf   con        (P1 m)             with (typeOf con m)
>   typeOf   con        (P1 m)             | Just (a * b)  = Just a
>   typeOf   con        (P1 m)             | _             = Nothing
>
> typeOf   con        (P2 m)             with (typeOf con m)
>   typeOf   con        (P2 m)             | Just (a * b)  = Just b
>   typeOf   con        (P2 m)             | _             = Nothing
>
> typeOf   con        T                                    = Just PCFBool
>
> typeOf   con        F                                    = Just PCFBool
>
> typeOf   con        Zero                                 = Just PCFNat
>
> typeOf   con        (Succ m)           with (typeOf con m)
>   typeOf   con        (Succ m)           | Just PCFNat   = Just PCFNat
>   typeOf   con        (Succ m)           | _             = Nothing
>
> typeOf   con        (Pred m)           with (typeOf con m)
>   typeOf   con        (Pred m)           | Just PCFNat   = Just PCFNat
>   typeOf   con        (Pred m)           | _             = Nothing
>
> typeOf   con        (IsZero m)         with (typeOf con m)
>   typeOf   con        (IsZero m)         | Just PCFNat   = Just PCFBool
>   typeOf   con        (IsZero m)         | _             = Nothing
>
> typeOf   con        (IfThenElse p m n) with (typeOf con p)
>   typeOf   con        (IfThenElse p m n) | Just PCFBool  = let t1 = typeOf con m
>                                                                t2 = typeOf con n
>                                                            in if t1 == t2
>                                                                 then t1
>                                                               else Nothing
>   typeOf   con        (IfThenElse p m n) | _             = Nothing
>
> typeOf   con        (Y m)              with (typeOf con m)
>   typeOf   con        (Y m)              | Just (a ~> b) = if a == b
>                                                              then Just a
>                                                            else Nothing
>   typeOf   con        (Y m)              | _             = Nothing
>
> typeOf     con        I                                  = Just U

We can now infer the type of closed terms.

> typeOfClosed = typeOf []
