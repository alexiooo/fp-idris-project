< module Lib.Terms
<
< import public Lib.Types
<
< import public Data.Fin  -- needed publically, since we publically export types that reference Fin
< import public Data.Vect
<
< %default total

Terms for PCF
-------------

PCF is a simple language that models computing. Its types are as follows.

### Include Lib.Types here

We begin by defining terms. We use de Bruijn indices to representent bound
variables. This is an elegant way to deel with alpha-equivalence.
We also keep track of (an upper bound on) free variables in the type;
PCFTerm n encodes terms with at most n free variables

> ||| Var k is a De-Bruijn index less than k
< public export
> Var : Nat -> Type
> Var = Fin
>
> namespace Symbol
<   public export
>   data Symbol : (0 ar : Nat) -> Type where
>     IfElse : Symbol 3       -- if-then-else construct
>     App    : Symbol 2       -- application
>     Pair   : Symbol 2       -- pairing
>     Fst    : Symbol 1       -- first projection
>     Snd    : Symbol 1       -- second projection
>     Succ   : Symbol 1       -- successor
>     Pred   : Symbol 1       -- predecessor
>     IsZero : Symbol 1       -- is zero predicate
>     Y      : Symbol 1       -- fixpoint / Y-combinator
>     T      : Symbol 0       -- true
>     F      : Symbol 0       -- false
>     Zero   : Symbol 0       -- zero value
>     Unit   : Symbol 0       -- unit value (*)

< public export
> data PCFTerm : Nat -> Type where 
>     V    : Var k -> PCFTerm k                             -- variables
>     L    : PCFType   -> PCFTerm (S k) -> PCFTerm k        -- lambda
>     S    : Symbol ar -> Vect ar (PCFTerm k) -> PCFTerm k  -- other symbols

Of special interest are the closed terms, those without any free variables

< public export
> ClosedPCFTerm : Type
> ClosedPCFTerm = PCFTerm 0

The Y constructor returns a fixed-point of the given term. It is required to
define functions by recursion. For example, the sum function on PCFNat is
defined recursively.

### Include SumExample.lidr here?  Use \begin{showCode} so it doesn't compile.


Remember that the type only gives an upper bound, so an inhabitant of say PCFType 3 might still
be closed. The following will try to strengthen any such term.
This really is just a wrapper around Fin.strengthen, with straightforward recursive cases, so we 
detail only variables and lambdas.

> strengthen : {k :_} -> PCFTerm (S k) -> Maybe (PCFTerm k)
> strengthenVect : {k :_} -> Vect n (PCFTerm (S k)) -> Maybe (Vect n (PCFTerm k))
> strengthenVect (y::ys) = [| (strengthen y) :: (strengthenVect ys) |]
> strengthenVect [] = Just []

> strengthen (V v)    = Fin.strengthen v >>= Just . V
> strengthen (L t m)  = strengthen m     >>= Just . L t
> strengthen (S s ar) = Just (S s !(strengthenVect ar))


< public export
> tryClose : {k:_} -> PCFTerm k -> Maybe ClosedPCFTerm
> tryClose {k} t = case k of 
>                   0      => Just t
>                   (S k') => strengthen t >>= tryClose 



Sadly, Idris does not have an equivalent of Haskell's `deriving` statement, so we'll have to 
implement equality ourselves. We omit the details here and in any other similarly trivial 
implementation blocks

> implementation Eq (Symbol k) where
>   -- ...
<   IfElse == IfElse = True
<   App    == App    = True
<   Pair   == Pair   = True
<   Fst    == Fst    = True
<   Snd    == Snd    = True
<   Succ   == Succ   = True
<   Pred   == Pred   = True
<   IsZero == IsZero = True
<   Y      == Y      = True
<   T      == T      = True
<   F      == F      = True
<   Zero   == Zero   = True
<   Unit   == Unit   = True
<   _      == _      = False


Eq requires that it's arguments are of the same type, so it only works for symbols of known arity.
s1 ~~ s2 holds iff s1 == s2, but the former will typecheck even if the arities don't match.

> namespace Symbol
<   infixr 6 ~~
<   public export
>   (~~) : Symbol k -> Symbol l -> Bool
>   -- trivial implementation omitted
<   IfElse ~~ IfElse = True
<   App    ~~ App    = True
<   Pair   ~~ Pair   = True
<   Fst    ~~ Fst    = True
<   Snd    ~~ Snd    = True
<   Succ   ~~ Succ   = True
<   Pred   ~~ Pred   = True
<   IsZero ~~ IsZero = True
<   Y      ~~ Y      = True
<   T      ~~ T      = True
<   F      ~~ F      = True
<   Zero   ~~ Zero   = True
<   Unit   ~~ Unit   = True
<   _      ~~ _      = False

We are now able to define equality for terms. The important case is
lambda-abstraction. We are using de Bruijn indices, which make comparing terms
very easy.

< public export partial
> implementation Eq (PCFTerm k) where
>   -- Trivial implementation omitted
<   V v         == V w          = v == w
<   L a m       == L b n        = a == b && m == n
<   S s [a]     == S p [x]      = s == p && a == x
<   S s [a,b]   == S p [x,y]    = s == p && a == x && b == y
<   S s [a,b,c] == S p [x,y,z]  = s == p && a == x && b == y && c == z
<   _           == _            = False


< public export
< Show (PCFTerm k) where
<   show (V x)   = show x
<   show (L x y) = "( λ " ++ show x ++ " . " ++ show y ++ ")"
<   show (S IfElse [p, m, n]) = ?hole_4
<   show (S App    [m,n]) = (show m) ++ (show n)
<   show (S Pair   [m,n]) = "<" ++ show m ++ ", " ++ show n ++ ">"
<   show (S Fst    [m])   = "π₁(" ++ show m ++ ")"
<   show (S Snd    [m])   = "π₂(" ++ show m ++ ")"
<   show (S Succ   [m])   = "Succ (" ++ show m ++ ")"
<   show (S Pred   [m])   = "Pred (" ++ show m ++ ")"
<   show (S IsZero [m])   = "IsZero (" ++ show m ++ ")"
<   show (S Y      [m])   = "Y (" ++ show m ++ ")"
<   show (S T      _)     = "T"
<   show (S F      _)     = "F"
<   show (S Zero   _)     = "Zero"
<   show (S Unit   _)     = "Unit"
