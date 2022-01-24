
module Lib.SystemFc.TermTyp

import Data.Vect

--
-- Forwards declarations
--

namespace Typ
  export
  data Typ : Type

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


TypFun : Nat -> Type  -- n-ary type function
TypFun _ = String


--
-- Sorts and Kinds
--

namespace Sort
  export
  data Sort = Ty | Co

namespace Kind
  export
  data Kind = Star | Fn Kind Kind | Coerc Typ Typ



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

