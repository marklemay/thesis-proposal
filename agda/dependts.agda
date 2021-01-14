module dependts where

open import Data.Nat


postulate
  Ctx  : ℕ -> Set

data PreSyntax {n : ℕ} : Set
data _|-_::_ {n : ℕ}  : (Γ : Ctx n) -> PreSyntax {n}  -> PreSyntax {n} -> Set

--postulate
--  v  : {n : ℕ} {Γ : Ctx n} -> ℕ -> Type {n} {Γ} --TODO

data PreSyntax {n} where
  pVar : (i : ℕ) -> PreSyntax
  pTyU : PreSyntax
  pPi : PreSyntax {n} -> PreSyntax {suc n} -> PreSyntax
  pfun : PreSyntax {n} -> PreSyntax {suc n} -- annotation TODO remove?
    -> (bod : PreSyntax {suc (suc n)}) -> PreSyntax
  papp :  PreSyntax {n} -> PreSyntax {n} -> PreSyntax

Type : {n : ℕ} (Γ : Ctx n) -> PreSyntax {n}  -> Set
Type Γ x = Γ |- x :: pTyU

data _|-_::_ {n}   where
--  Var :  {Γ : Ctx n} -> (i : ℕ) ->  Γ  |- (v i)
  
--  ty :  {Γ : Ctx n} -> Type {n} {Γ} ->  Γ  |- TyU
  -- 
  --Conv
