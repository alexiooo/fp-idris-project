
module Lib.SystemFc.TermTyp

import Data.Vect

mutual
  --
  -- Types of variables
  --
  -- For now implemented as type aliases, but possibly with newtypes in future

  public export
  TypVar : Type         -- type variables
  TypVar = String

  public export
  TermVar : Type        -- term variables
  TermVar = String

  public export
  CoercConst : Type     -- coercion constant
  CoercConst = String

  public export
  ValConstr : Type      -- value type constructor
  ValConstr = String

  public export
  DataConstr  : Type    -- data constructor
  DataConstr = String

  public export
  TypFun : Nat -> Type  -- n-ary type function
  TypFun _ = String


  --
  -- Sorts and Kinds
  --

  namespace Sort
    public export
    data Sort = Ty | Co 

    Eq Sort where
      Ty == Ty = True
      Co == Co = True
      _  == _  = False

  namespace Kind
    public export
    data Kind = Star | Fn Kind Kind | Coerc Typ Typ

    public export
    Eq Kind where
      Star        == Star         = True
      Fn k1 i1    == Fn k2 i2     = k1 == k2 && i1 == i2
      Coerc t1 u1 == Coerc t2 u2  = t1 == t2 && u1 == u2
      _           == _            = False


  --
  -- Types and Coercions
  --

  namespace Typ
    public export
    data Typ =  Var TypVar 
              | TC CoercConst
              | TT ValConstr
              | App Typ Typ
              | ForAll TypVar Kind Typ
              | Sym Typ
              | Circ Typ Typ  -- γ₁ ◯ γ₂   
              | At Typ Typ    -- γ @ φ
              | Left Typ
              | Right Typ
              | Coerc Typ Typ -- γ₁ ∼ γ₂
              | RightC Typ
              | LeftC Typ
              | Triangle Typ Typ -- γ₁ ▶ γ₂

    export
    FnApp : {n : Nat} -> TypFun n -> Vect n Typ -> Typ

    public export
    Eq Typ where
      Var v1          == Var v2           = v1 == v2
      TC c1           == TC c2            = c1 == c2
      TT t1           == TT t2            = t1 == t2
      App t1 u1       == App t2 u2        = t1 == t2 && u1 == u2
      ForAll v1 k1 t1 == ForAll v2 k2 t2  = v1 == v2 && k1 == k2 && t1 == t2
      Sym t1          == Sym t2           = t1 == t2 
      Circ t1 u1      == Circ t2 u2       = t1 == t2 && u1 == u2     
      At t1 u1        == At t2 u2         = t1 == t2 && u1 == u2  
      Left t1         == Left t2          = t1 == t2   
      Right t1        == Right t2         = t1 == t2   
      Coerc t1 u1     == Coerc t2 u2      = t1 == t2 && u1 == u2
      RightC t1       == RightC t2        = t1 == t2     
      LeftC t1        == LeftC t2         = t1 == t2   
      Triangle t1 u1  == Triangle t2 u2   = t1 == t2 && u1 == u2
      _               == _                = False



  --
  -- Terms
  --

  namespace Term
    public export
    data Pattern =
      Pat DataConstr (List (TypVar, Kind)) (List (TermVar, Typ))

    public export
    data Term = Var TermVar
              | Cons DataConstr
              | TypLam TypVar Kind Term
              | TypApp Term Typ
              | Lam TermVar Typ Term
              | Let TermVar Typ Term Term
              | Case Term Pattern Term
              | Cast Term Typ



  --
  -- Atoms
  --

  namespace TyAtom
    public export
    data TyAtom = Var TypVar | Cons ValConstr

    public export
    toTyp : TyAtom -> Typ
    toTyp (Var v) = Typ.Var v
    toTyp (Cons c) = Typ.TT c

  namespace CoAtom
    public export
    data CoAtom = Var TypVar | Cons CoercConst

    public export
    toTyp : CoAtom -> Typ
    toTyp (Var v) = Typ.Var v
    toTyp (Cons c) = Typ.TC c    

  namespace TeAtom
    public export
    data TeAtom = Var TermVar | Cons DataConstr

    public export
    toTerm : TeAtom -> Term
    toTerm (Var v) = Term.Var v
    toTerm (Cons c) = Term.Cons c

