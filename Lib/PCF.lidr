> module Lib.PCF
>
> import Data.List
> import Lib.Existentials

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

We begin by defining terms. We use de Bruijn indices to representent bound
variables. This is an elegant way to deel with alpha-equivalence.

> Var : Type
> Var = Nat
>
> data PCFTerm = V Var                    -- variables
>              | C PCFTerm PCFTerm        -- composition / application
>              | L PCFType PCFTerm    -- lambda
>              | P PCFTerm PCFTerm        -- pairing
>              | P1 PCFTerm               -- first projection
>              | P2 PCFTerm               -- second projection
>              | T                        -- true
>              | F                        -- false
>              | Zero                     -- zero
>              | Succ PCFTerm             -- successor
>              | Pred PCFTerm             -- predecessor
>              | IsZero PCFTerm           
>              | IfThenElse PCFTerm PCFTerm PCFTerm
>              | Y PCFTerm                -- fixpoint / Y-combinator
>              | I                        -- unit value (*)

The Y constructor returns a fixed-point of the given term. It is required to
define functions by recursion. For example, the sum function on PCFNat is
defined recursively.

> sum : PCFTerm
> sum = Y (L (PCFNat ~> (PCFNat ~> PCFNat)) (L PCFNat (L PCFNat (IfThenElse (IsZero (V 0)) (V 1) (Succ (C (C (V 2) (V 1)) (Pred (V 0))))))))

Our goal here is to write a function that returns the type of any closed term

> total typeOfClosed : PCFTerm -> Maybe PCFType

We are now able to define equality for terms. The important case is
lambda-abstraction. We are using de Bruijn indices, which make comparing terms
very easy.

> implementation Eq PCFTerm where
>   V v              == V w              = v == w
>   C m n            == C p q            = m == p && n == q
>   L a m            == L b n            = a == b && m == n
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

In order to define small-step reduction, we must be able to substitute a term
for a variable in another term. The following functions implement this.

> total substitute : PCFTerm -> PCFTerm -> Var -> PCFTerm

The important cases are the variables and lambda-abstractions.

> substitute (V w)              s v = if v == w
>                                         then s
>                                       else (V w)
> substitute (L t m)            s v = L t (substitute m s (S v))

All the other cases are straightforward.

> substitute (C m n)            s v = C (substitute m s v) (substitute n s v)
> substitute (P m n)            s v = P (substitute m s v) (substitute n s v)
> substitute (P1 m)             s v = P1 (substitute m s v)
> substitute (P2 m)             s v = P2 (substitute m s v)
> substitute T                  s v = T
> substitute F                  s v = F
> substitute Zero               s v = Zero
> substitute (Succ m)           s v = Succ (substitute m s v)
> substitute (Pred m)           s v = Pred (substitute m s v)
> substitute (IsZero m)         s v = IsZero (substitute m s v)
> substitute (IfThenElse p m n) s v =
>     IfThenElse (substitute p s v) (substitute m s v) (substitute n s v)
> substitute (Y m)              s v = Y (substitute m s v)
> substitute I                  s v = I


Reduction
---------

We can now define reduction. We begin with small-step reduction. Not all terms
can reduce, it is thus important that the result is of type Maybe PCFTerm.

> total smallStep : PCFTerm -> Maybe PCFTerm
> smallStep (Pred Zero)           = Just (Zero)
> smallStep (Pred (Succ m))       = Just (m)
> smallStep (Pred m)              = do m' <- smallStep m
>                                      Just (Pred m')
> smallStep (IsZero Zero)         = Just (T)
> smallStep (IsZero (Succ m))     = Just (F)
> smallStep (IsZero m)            = do m' <- smallStep m
>                                      Just (IsZero (m'))
> smallStep (Succ m)              = do m' <- smallStep m
>                                      Just (Succ m')
> smallStep (C (L _ m) n)         = Just (substitute m n 0)
> smallStep (C m n)               = do m' <- smallStep m
>                                      Just (C m' n)
> smallStep (P1 (P m _))          = Just (m)
> smallStep (P2 (P _ n))          = Just (n)
> smallStep (P1 m)                = do m' <- smallStep m
>                                      Just (P1 m')
> smallStep (P2 m)                = do m' <- smallStep m
>                                      Just (P2 m')
> smallStep (IfThenElse T m _)    = Just (m)
> smallStep (IfThenElse F _ n)    = Just (n)
> smallStep (IfThenElse p m n)    = do p' <- smallStep p
>                                      Just (IfThenElse p' m n)
> smallStep (Y m)                 = Just (C m (Y m))
> smallStep m with (typeOfClosed m, m /= I)
>    smallStep m | (Just U, True) = Just I
>    smallStep _ | (_, _)         = Nothing

An important notion is a value, which is a term that cannot be reduced further.

> total isValue : PCFTerm -> Bool
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

> Environment : Type
> Environment = List PCFTerm
>
> partial evalEnv : Environment -> PCFTerm -> PCFTerm
> evalEnv env T                  = T
> evalEnv env F                  = F
> evalEnv env Zero               = Zero
> evalEnv env (P m n)            = (P m n)
> evalEnv env (L t m)            = (L t m)
> evalEnv env (Pred Zero)        = Zero
> evalEnv env (Pred (Succ m))    = evalEnv env m
> evalEnv env (Pred m)           = evalEnv env $ Pred (evalEnv env m)
> evalEnv env (IsZero Zero)      = T
> evalEnv env (IsZero (Succ m))  = F
> evalEnv env (IsZero m)         = evalEnv env $ IsZero (evalEnv env m)
> evalEnv env (Succ m)           = Succ (evalEnv env m)
> evalEnv env (C (L t m) n)      = evalEnv (n::env) m
> evalEnv env (C m n)            = evalEnv env $ C (evalEnv env m) n
> evalEnv env (P1 (P m n))       = evalEnv env m
> evalEnv env (P2 (P m n))       = evalEnv env n
> evalEnv env (P1 m)             = evalEnv env $ P1 (evalEnv env m)
> evalEnv env (P2 m)             = evalEnv env $ P2 (evalEnv env m)
> evalEnv env (IfThenElse T m n) = evalEnv env m
> evalEnv env (IfThenElse F m n) = evalEnv env n
> evalEnv env (IfThenElse p m n) = evalEnv env $ IfThenElse (evalEnv env p) m n
> evalEnv env (Y m)              = evalEnv env $ C m (Y m)      -- /!\ This can create infinite loops
> evalEnv env (V v) with (inBounds v env)
>   evalEnv env (V v) | Yes _    = index v env
> evalEnv env m with (typeOfClosed m)
>   evalEnv env m | Just U       = I
>
> partial eval : PCFTerm -> PCFTerm
> eval = evalEnv []



Type Checking
-------------

We are now ready to define a type infering function. Such a function takes as
arguments a context and a term, and return a type if the term is typeable in
the given context, or Nothing otherwise.

> Context : Type
> Context = List PCFType
>
> total typeOf : Context -> PCFTerm -> Maybe PCFType
> typeOf con (V v) with (inBounds v con)
>   typeOf con (V v) | Yes _                     = Just (index v con)
>   typeOf con (V v) | No _                      = Nothing
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

We can now infer the type of closed terms.

> typeOfClosed = typeOf []


Values and Normal Forms
-------------

A certain subset of terms are called `values'

> namespace Value
>   public export
>   data PCFValue = T 
>                 | F 
>                 | Zero 
>                 | Succ PCFValue
>                 | I
>                 | P PCFTerm PCFTerm
>                 | L PCFType PCFTerm
>
>   public export
>   fromTerm : PCFTerm -> Maybe PCFValue
>   fromTerm T          = Just T
>   fromTerm F          = Just F
>   fromTerm Zero       = Just Zero
>   fromTerm (Succ t)   = do v <- fromTerm t
>                            Just (Succ v)
>   fromTerm I          = Just I
>   fromTerm (P m n)    = Just (P m n)
>   fromTerm (L t m)  = Just (L t m)
>   fromTerm _          = Nothing
>
>   public export
>   toTerm : PCFValue -> PCFTerm
>   toTerm T          = T
>   toTerm F          = F
>   toTerm Zero       = Zero
>   toTerm (Succ v)   = Succ (toTerm v)
>   toTerm I          = I
>   toTerm (P m n)    = P m n
>   toTerm (L t m)  = L t m

Values correspond exactly to terms that are in normal forms

>   valuesAreNormalForms : (v : PCFValue) -> smallStep (toTerm v) = Nothing
>   valuesAreNormalForms T        = Refl
>   valuesAreNormalForms F        = Refl
>   valuesAreNormalForms Zero     = Refl
>   -- valuesAreNormalForms Succ t = Refl 
>   -- valuesAreNormalForms Succ t = Refl
>   valuesAreNormalForms I        = Refl
>   valuesAreNormalForms (P m n)  = Refl

-- >   normalFormsAreValues : (t : PCFTerm) -> {auto hnf : smallStep t = Nothing} -> exists (\v -> fromTerm t = Just v)
-- >   normalFormsAreValues = ?undefined2
