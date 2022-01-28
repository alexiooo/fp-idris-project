
module Lib.Check.Kind

-- import Lib.SystemFc
import Lib.SystemFc.TermTyp
import Lib.SystemFc.Env

||| Determine the sort (TY or CO) of a kind
||| Represents judgements Γ ⊢_k κ : δ 
||| See Fig. 3
getSort: Context -> Kind -> Maybe Sort

||| Determing the kind of a type
||| Represents judgements Γ ⊢_TY σ : κ
||| See Fig. 2
getKind : Context -> Typ -> Maybe Kind


--
-- Declarations for getSort
--

-- (Star)
getSort _   Star          = Just Ty

-- (FunK)
getSort ctx (Fn k1 k2)    = let s1 = getSort ctx k1 in
                            let s2 = getSort ctx k2 in
                            case (s1, s2) of
                              (Just Ty, Just Ty)  => Just Ty
                              _                   => Nothing

-- (EqCo)
getSort ctx (Coerc (c1@(Coerc _ _)) c2) 
                          = do  Just s1 <- getKind ctx c1
                                  | Nothing => Nothing
                                Just s2 <- getKind ctx c2
                                  | Nothing => Nothing
                                if s1 == s2 then Just Co
                                            else Nothing

-- (EqTy)
-- getSort ctx (Coerc c1 c2) = let Just s1 = getSort ctx c1 in
--                             let Just s2 = getSort ctx c2 in
--                             if s1 == s2 then Just Co
--                                         else Nothing

getSort _ _ = Nothing

                        

--
-- Declarations for kinding
--

-- getKind ctx (Typ.Var v)   = do  k <- lookupTypVar ctx v    -- TyVar
                                  -- pure k
-- getKind ctx (Typ.TT _)    = Nothing      -- TyVar
getKind _   _             = Nothing      -- TyVar