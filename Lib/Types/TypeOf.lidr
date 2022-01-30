
< module Lib.Types.TypeOf
< 
< import public Lib.Types
< import public Lib.Types.DecEq
< import public Lib.Terms
< import public Lib.Util
< import public Data.Vect

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

Type checking occurs in two mutually recursive functions. TypeOf infers the type of a single term,
while typeOfVect handles lists of terms.

< public export
> total typeOf : Context k -> PCFTerm k -> Maybe PCFType

< public export
> total typeOfVect : Context k -> Vect n (PCFTerm k) -> Maybe (Vect n PCFType)

The latter is equivalent to
> -- typeOfVect con args = sequence (typeOf con <$> args)

But we need to spell it out explicitly, or the totality checker will complain that our code might
enter an infinite loop
> typeOfVect x (y :: ys) = [| (typeOf x y) :: (typeOfVect x ys) |]
> typeOfVect _ []        = Just []

> typeOf con (V v)      = Just (index v con)
> typeOf con (L t m)    = typeOf (t::con) m >>= Just . ( t ~> )
> typeOf con (S s ms)   = case ( s,  !(typeOfVect con ms) ) of
>   (IfElse,  [PCFBool, a, b])  => if a == b then Just a
>                                            else Nothing
>   (App,     [(a ~> b), c])    => if a == c then Just b
>                                            else Nothing
>   (Pair,    [a, b])           => Just (a * b)
>   (Fst,     [a * _])          => Just a
>   (Snd,     [_ * b])          => Just b
>   (Succ,    [PCFNat])         => Just PCFNat
>   (Pred,    [PCFNat])         => Just PCFNat
>   (IsZero,  [PCFNat])         => Just PCFBool
>   (T,       [])               => Just PCFBool
>   (F,       [])               => Just PCFBool
>   (Zero,    [])               => Just PCFNat
>   (Unit,    [])               => Just PCFUnit
>   (_, _)                      => Nothing

Closed terms are typeable exactly when they are typeable with an empty context.

< public export
> typeOfClosed : ClosedPCFTerm -> Maybe PCFType
> typeOfClosed = typeOf []
