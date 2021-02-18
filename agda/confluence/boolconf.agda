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
  subsSyntax : ∀ {i j}
    → (σ : (Fin i → Syntax {j} ))
    → (Syntax {i}  → Syntax {j})
   
  o : {n : ℕ} -> Syntax {n} -> Syntax {suc n}

  _[_] :{n : ℕ} -> Syntax {suc n} -> Syntax {n} -> Syntax {n}


{-

  _[_:=_] :{n : ℕ} -> PreSyntax {suc n} -> (i : Fin n) -> PreSyntax {n} -> PreSyntax {n}
  
  _~>peq_ : {n : ℕ} -> List (PreSyntax {n})  -> List (PreSyntax {n}) -> Set
  allPi : {n : ℕ} -> List (PreSyntax {n}) -> List (PreSyntax {suc n}) -> Set
  
  _~:~_ : {n : ℕ} -> PreSyntax {n} -> List (PreSyntax {n}) -> PreSyntax {n}
-}


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
par-max (Var i) = Var i
par-max (Fun bod) = Fun (par-max bod)
par-max BT = BT
par-max BF = BF
par-max (If c t e) = If (par-max c) (par-max t) (par-max e)
par-max (App f a) = App (par-max f) (par-max a)

par-triangle :  {n : ℕ} {a b : Syntax {n}}
   -> a ~>p b
   -> b ~>p (par-max a)
par-triangle (par-fun-red par-bod par-a) = {!!}
par-triangle (par-BT-red x) = {!!}
par-triangle (par-BF-red x) = {!!}
par-triangle par-Var = {!!}
par-triangle (par-Fun x) = {!!}
par-triangle (par-App x x₁) = {!!}
par-triangle par-BT = par-BT
par-triangle par-BF = par-BF
par-triangle (par-If par-c par-t par-e) = {!!}

{-
par-triangle (par-red par-casts par-arg par-bod fcasts bodcasts all-pi) with allPi?-max fcasts
par-triangle (par-red par-casts par-arg par-bod fcasts bodcasts all-pi) | just x
  = ~:~-par (sub-par (~:~-par (sub-par ( par-triangle par-bod) (o-par (par-triangle (par-Fun eqs-par-refl par-bod)))) {!!}) (par-triangle par-arg)) (eqs-par-triangle par-casts)
par-triangle (par-red par-casts par-arg par-bod fcasts bodcasts all-pi) | nothing = {!par-red!}
par-triangle = {!!}
   {-
par-triangle (par-red par-casts par-arg par-bod fcasts bodcasts all-pi) with allPi? fcasts
par-triangle (par-red par-casts par-arg par-bod fcasts bodcasts all-pi) | inj₁ (bodsubs , snd)
  =  ~:~-par (sub-par (~:~-par (sub-par ( par-triangle par-bod) (o-par (par-triangle (par-Fun eqs-par-refl par-bod)))) {!!}) (par-triangle par-arg)) (eqs-par-triangle par-casts) -- intresting,  all-pi maximally pre reduces 
par-triangle (par-red par-casts par-arg par-bod fcasts bodcasts all-pi) | inj₂ y = {!!} -- contrediction
par-triangle (par-App par-casts (par-Fun {_} {_} {fcasts} par-fcasts par-bod) par-arg) with allPi? fcasts
par-triangle (par-App par-casts (par-Fun {_} {_} {fcasts} par-fcasts par-bod) par-arg) | inj₁ (bodsubs , snd)
  = {!!} -- par-red ? ? ? ? ?  -- 6 implicit
par-triangle (par-App par-casts par-f par-arg) | inj₂ y = par-App (eqs-par-triangle par-casts) (par-triangle par-f) (par-triangle par-arg)
-- "easy"
par-triangle (par-App par-casts (par-red x par-f par-f₁ fcasts bodcasts x₁) par-arg) = {!!}
par-triangle (par-App par-casts (par-Var x) par-arg) = {!!}
par-triangle (par-App par-casts (par-TyU x) par-arg) = {!!}
par-triangle (par-App par-casts par-TyU2 par-arg) = {!!}
par-triangle (par-App par-casts (par-Pi2 par-f par-f₁) par-arg) = {!!}
par-triangle (par-App par-casts (par-Pi x par-f par-f₁) par-arg) = {!!}
par-triangle (par-App par-casts (par-App x par-f par-f₁) par-arg) = {!!}
par-triangle (par-Var x) = {!!}
par-triangle (par-TyU x) = {!!}
par-triangle par-TyU2 = {!!}
par-triangle (par-Pi2 x x₁) = {!!}
par-triangle (par-Pi x x₁ x₂) = {!!}
par-triangle (par-Fun x x₁) = {!!}
-}


confulent-~> : {n : ℕ} {a b b' : PreSyntax {n}}
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
-}
