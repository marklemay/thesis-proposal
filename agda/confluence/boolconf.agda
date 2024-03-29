module boolconf where

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
  Var : (i : Fin n) -> Syntax
  Fun :
    (bod : Syntax {suc (suc n)}) -> Syntax
  App :  Syntax {n} -> Syntax {n} -> Syntax
  BT BF :  Syntax
  If :  Syntax {n} -> Syntax {n} -> Syntax {n} -> Syntax


 
postulate
  o : {n : ℕ} -> Syntax {n} -> Syntax {suc n}

  _[_] :{n : ℕ} -> Syntax {suc n} -> Syntax {n} -> Syntax {n}


data _~>p_ {n : ℕ} : Syntax {n}  -> Syntax {n} -> Set  where

  par-fun-red : {a a' : _} -> {bod bod' : _ } 
    -> a ~>p a'
    -> bod ~>p bod'
    -> App (Fun bod) a ~>p (bod' [ o (Fun bod') ] [ a' ])
    
  par-BT-red : {else then then' : _} 
    -> then ~>p then'
    -> If BT then else ~>p  then' 
    
  par-BF-red : {else else' then  : _} 
    -> else ~>p else'
    -> If BF then else ~>p else' 
    
  -- structural
  par-Var : {i : Fin n}
    -> Var i ~>p Var i
    
  par-Fun : 
    {bod bod' : _}
    -> bod ~>p bod'
    -> Fun bod ~>p Fun  bod'

  par-App : {f f' a a' : _}
    -> f ~>p f'
    -> a ~>p a'
    -> App f a ~>p App f' a'

  par-BT : BT ~>p BT
  par-BF : BF ~>p BF
  
  par-If : {cond cond' then then' else else' : _} 
    -> cond ~>p cond'
    -> then ~>p then'
    -> else ~>p else'
    -> If cond then else ~>p If cond' then' else'


postulate
  sub-par : {n : ℕ} {a a' : Syntax {suc n}} {b b' : Syntax {n}}
    -> a ~>p  a'
    -> b ~>p b'
    -> (a [ b ] ) ~>p  (a' [ b' ])
    
  o-par : {n : ℕ} {a a' : Syntax { n}} 
      -> a ~>p  a'
      -> o a ~>p  o a'



par-refll : {n : ℕ}  (a : Syntax {n}) -> a ~>p a
par-refll {n} (Var i) = par-Var
par-refll {n} (Fun x) = par-Fun (par-refll x)
par-refll {n} (App x x₁) = par-App (par-refll x) (par-refll x₁)
par-refll {n} BT = par-BT
par-refll {n} BF = par-BF
par-refll {n} (If x x₁ x₂) = par-If (par-refll x) (par-refll x₁) (par-refll x₂)

par-max : {n : ℕ} -> Syntax {n} -> Syntax {n}
par-max (App (Fun bod) a) = (par-max bod) [ o (Fun (par-max bod)) ] [ par-max a ]
par-max (If BT t _) = (par-max t)
par-max (If BF _ e) = (par-max e) 
par-max (Var i) = Var i
par-max (Fun bod) = Fun (par-max bod)
par-max BT = BT
par-max BF = BF
par-max (App f a) = App (par-max f) (par-max a)
par-max (If c t e) = If (par-max c) (par-max t) (par-max e)

par-triangle :  {n : ℕ} {a b : Syntax {n}}
   -> a ~>p b
   -> b ~>p (par-max a)
par-triangle (par-fun-red par-a par-bod) = sub-par (sub-par (par-triangle par-bod) (o-par (par-Fun (par-triangle par-bod)))) (par-triangle par-a)
par-triangle (par-App (par-Fun par-bod) par-a) =  par-fun-red (par-triangle par-a) (par-triangle par-bod)
par-triangle (par-BT-red x) = par-triangle x
par-triangle (par-BF-red x) = par-triangle x
par-triangle (par-If par-BT par-t par-e) = par-BT-red (par-triangle par-t)
par-triangle (par-If par-BF par-t par-e) = par-BF-red (par-triangle par-e)
par-triangle par-Var = par-Var
par-triangle (par-Fun x) = par-Fun (par-triangle x)
par-triangle par-BT = par-BT
par-triangle par-BF = par-BF
--  par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@(par-fun-red x x₁) par-a) =
  par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@(par-BT-red x) par-a) =
  par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@(par-BF-red x) par-a) =
  par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@par-Var par-a) =
  par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@(par-App x x₁) par-a) =
  par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@par-BT par-a) =
  par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@par-BF par-a) =
  par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@(par-If x x₁ x₂) par-a) =
  par-App (par-triangle par-f) (par-triangle par-a)
-- par-If (par-triangle par-c) (par-triangle par-t) (par-triangle par-e)
par-triangle (par-If par-c@(par-fun-red x x₁) par-t par-e) =
  par-If (par-triangle par-c) (par-triangle par-t) (par-triangle par-e)
par-triangle (par-If par-c@(par-BT-red x) par-t par-e) =
  par-If (par-triangle par-c) (par-triangle par-t) (par-triangle par-e)
par-triangle (par-If par-c@(par-BF-red x) par-t par-e) =
  par-If (par-triangle par-c) (par-triangle par-t) (par-triangle par-e)
par-triangle (par-If par-c@par-Var par-t par-e) = 
  par-If (par-triangle par-c) (par-triangle par-t) (par-triangle par-e)
par-triangle (par-If par-c@(par-Fun x) par-t par-e) = 
  par-If (par-triangle par-c) (par-triangle par-t) (par-triangle par-e)
par-triangle (par-If par-c@(par-App x x₁) par-t par-e) = 
  par-If (par-triangle par-c) (par-triangle par-t) (par-triangle par-e)
par-triangle (par-If par-c@(par-If x x₁ x₂) par-t par-e) = 
  par-If (par-triangle par-c) (par-triangle par-t) (par-triangle par-e)


confulent-~> : {n : ℕ} {a b b' : Syntax {n}}
   -> a ~>p b
   -> a ~>p b'
   -> Σ _ \ v  -> b ~>p v  × b' ~>p v
confulent-~> {_} {a} ab ab' = (par-max a) , (par-triangle ab) , par-triangle ab'

{-

data _val {n : ℕ} : PreSyntax {n} -> Set where
  vTyU2 : pTyU2 val
  vPi2 : { aTy : PreSyntax } -> {bodTy : PreSyntax }
     -> (pPi2 aTy bodTy) val
  -- ..
-}
