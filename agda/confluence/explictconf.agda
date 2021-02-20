module explictconf where

open import Data.Nat
open import Data.Fin
open import Data.Maybe 
open import Data.List hiding (lookup ; [_])
-- open import Data.Vec hiding (lookup ; [_])
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])


data Syntax {n : ℕ} : Set  where
  Var : {ty : Syntax {n}} -> (i : Fin n) -> Syntax
  Fun : (ty : Syntax {n}) -> (bod : Syntax {suc (suc n)}) -> Syntax
  App : (ty : Syntax {n}) -> Syntax {n} -> Syntax {n} -> Syntax

  Pi : Syntax {n} -> (bod : Syntax {suc n}) -> Syntax -- TODO Ty here?
  TyU :  Syntax


postulate
  o : {n : ℕ} -> Syntax {n} -> Syntax {suc n}

  _[_::_] :{n : ℕ} -> Syntax {suc n} -> Syntax {n} -> (ty : Syntax {n}) -> Syntax {n}
    --  technically incorrect assumption becuase this needs type equality,  but as long as this is handwaved, minimize type annotations

 

data _~>p_ {n : ℕ} : Syntax {n}  -> Syntax {n} -> Set  where

  par-fun-red : {a a' aTy aTy' : _} -> {bodTy bodTy' : _} -> {bod bod' : _ } 
    -> (par-aTy : aTy ~>p aTy')
    -> (par-bod : bodTy ~>p bodTy')
    -> (par-a : a ~>p a')
    -> (par-bod : bod ~>p bod')
    -> {whatev : _}
    -> App  whatev (Fun (Pi aTy bodTy) bod) a ~>p (bod' [ o (Fun (Pi aTy' bodTy') bod') :: o (Pi aTy' bodTy') ]  [ a' :: aTy' ] )
    
  -- structural
  par-Var : {ty ty' : Syntax {n}}-> (par-ty : ty ~>p ty')
    -> {i : Fin n}
    -> Var {_} {ty}  i ~>p Var {_} {ty'}  i
    
  par-Fun : {ty ty' : Syntax {n}}-> (par-ty : ty ~>p ty')
    -> {bod bod' : _}
    -> (par-bod : bod ~>p bod')
    -> Fun  (ty)  bod ~>p Fun  (ty') bod'

  par-App : {f f' a a' : _} {ty ty' : Syntax {n}}-> (par-ty : ty ~>p ty')
    -> (par-f : f ~>p f')
    -> (par-a : a ~>p a')
    -> App  (ty)  f a ~>p App  (ty') f' a'

  par-Pi : {aTy aTy' : _} -> {bodTy bodTy' : _}
    -> (par-aTy : aTy ~>p aTy')
    -> (par-bodTy : bodTy ~>p bodTy')
    -> Pi aTy bodTy  ~>p  Pi aTy' bodTy'  

  par-TyU :  TyU  ~>p  TyU

par-refll : {n : ℕ}  (a : Syntax {n}) -> a ~>p a
par-refll (Var {ty}  i) = par-Var (par-refll ty)
par-refll (Fun (ty) x) = par-Fun (par-refll ty) (par-refll x)
par-refll (App (ty) x x₁) = par-App (par-refll ty) (par-refll x) (par-refll x₁)
par-refll (Pi x x₁) = par-Pi (par-refll x) (par-refll x₁)
par-refll TyU = par-TyU

postulate
  sub-par : {n : ℕ} {a a' : Syntax {suc n}} {b b' bTy bTy' : Syntax {n}}
    -> a ~>p  a'
    -> b ~>p b'
    -> bTy ~>p bTy'
    -> (a [ b :: bTy ]  ) ~>p  (a' [ b' :: bTy' ])
    --  technically incorrect assumption becuase this needs type equality
    
  o-par : {n : ℕ} {a a' : Syntax { n}} 
      -> a ~>p  a'
      -> o a ~>p  o a'


par-max : {n : ℕ} -> Syntax {n} -> Syntax {n}
par-max (App (_) (Fun fty@(Pi aTy bodTy) bod) a) = (par-max bod) [ o (Fun (par-max fty) (par-max bod)) :: o (par-max fty) ]  [ par-max a :: par-max aTy ] 
par-max (App (ty) f a) = App  (par-max ty) (par-max f) (par-max a)
par-max (Var {ty} i) = (Var {_} {par-max ty} i)  -- wierd, patterns and values not symetric
par-max (Fun (ty) bod) = Fun (par-max ty) (par-max bod)
par-max (Pi aTy bodTy) = Pi (par-max aTy) (par-max bodTy)
par-max TyU = TyU

par-triangle :  {n : ℕ} {a b : Syntax {n}}
   -> a ~>p b
   -> b ~>p (par-max a)
par-triangle (par-fun-red par-aTy par-bodTy par-a par-bod) =  sub-par (sub-par (par-triangle par-bod) (o-par (par-Fun (par-Pi (par-triangle par-aTy) (par-triangle par-bodTy))
                                                                                                                (par-triangle par-bod))) (o-par (par-Pi (par-triangle par-aTy) (par-triangle par-bodTy))))
                                                                                                                (par-triangle par-a) (par-triangle par-aTy)
par-triangle (par-App par-ty (par-Fun (par-Pi par-aTy par-bodTy) par-bod) par-a) = par-fun-red (par-triangle par-aTy) (par-triangle par-bodTy) (par-triangle par-a) (par-triangle par-bod)

par-triangle (par-Var x) = par-Var (par-triangle x)
par-triangle (par-Fun x x₁) = par-Fun (par-triangle x) (par-triangle x₁)
par-triangle (par-Pi x x₁) = par-Pi (par-triangle x) (par-triangle x₁)
par-triangle par-TyU = par-TyU

par-triangle (par-App par-ty par-f@(par-Fun (par-fun-red x x₁ x₂ x₃) par-bod) par-a)
  = par-App (par-triangle par-ty) (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-ty par-f@(par-Fun (par-Var x) par-bod) par-a)
  = par-App (par-triangle par-ty) (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-ty par-f@(par-Fun (par-Fun x x₁) par-bod) par-a)
  = par-App (par-triangle par-ty) (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-ty par-f@(par-Fun (par-App x x₁ x₂) par-bod) par-a)
  = par-App (par-triangle par-ty) (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-ty par-f@(par-Fun par-TyU par-bod) par-a)
  = par-App (par-triangle par-ty) (par-triangle par-f) (par-triangle par-a)
-- par-f
par-triangle (par-App par-ty par-f@(par-fun-red _ _ _ _) par-a)
  = par-App (par-triangle par-ty) (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-ty par-f@(par-Var x) par-a)
  = par-App (par-triangle par-ty) (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-ty par-f@(par-App x x₁ x₂) par-a)
  = par-App (par-triangle par-ty) (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-ty par-f@(par-Pi x x₁) par-a)
  = par-App (par-triangle par-ty) (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-ty par-f@par-TyU par-a)
  = par-App (par-triangle par-ty) (par-triangle par-f) (par-triangle par-a)
  


confulent-~> : {n : ℕ} {a b b' : Syntax {n}}
   -> a ~>p b
   -> a ~>p b'
   -> Σ _ \ v  -> b ~>p v  × b' ~>p v
confulent-~> {_} {a} ab ab' = (par-max a) , (par-triangle ab) , par-triangle ab'

{-



data _val {n : ℕ} : PreSyntax {n} -> Set where
  -- ..
-}
