module dependts where

open import Data.Nat
open import Data.Fin
open import Data.List hiding (lookup ; [_])
-- open import Data.Vec hiding (lookup ; [_])
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])


data PreSyntax {n : ℕ} : Set 
data PreHeadSyntax {n : ℕ} : Set  where
  pVar : (i : Fin n) -> PreHeadSyntax
  pTyU : PreHeadSyntax
  pPi : PreSyntax {n} -> PreSyntax {suc n} -> PreHeadSyntax
  pFun :
    (bod : PreSyntax {suc (suc n)}) -> PreHeadSyntax
  pApp :  PreSyntax {n} -> PreSyntax {n} -> PreHeadSyntax

data PreSyntax {n}  where
  pCast : PreHeadSyntax {n} -> List (PreSyntax {n}) -> PreSyntax
  pTyU2 : PreSyntax
  pPi2 : PreSyntax {n} -> PreSyntax {suc n} -> PreSyntax

-- degenerate context extention
extPreSyntax : {i j : ℕ}
  -> (ρ : (Fin i -> Fin j))
  -> Fin (suc i) -> (Fin (suc j))
extPreSyntax ρ 0F = 0F
extPreSyntax ρ (suc x) = suc (ρ x)

 
postulate
  substPreSyntax : ∀ {i j}
    → (σ : (Fin i → PreSyntax {j} ))
    → (PreSyntax {i}  → PreSyntax {j})
   
  o : {n : ℕ} -> PreSyntax {n} -> PreSyntax {suc n}

  _[_] :{n : ℕ} -> PreSyntax {suc n} -> PreSyntax {n} -> PreSyntax {n}

postulate
  Ctx  : ℕ -> Set
  Emp : Ctx 0
  extCtx : {n : ℕ} -> Ctx n -> PreSyntax {n} -> Ctx (suc n)
  lookup : {n : ℕ} (Γ : Ctx n) -> (i : Fin n)  -> PreSyntax {n}

  _[_:=_] :{n : ℕ} -> PreSyntax {suc n} -> (i : Fin n) -> PreSyntax {n} -> PreSyntax {n}
  
  _~>peq_ : {n : ℕ} -> List (PreSyntax {n})  -> List (PreSyntax {n}) -> Set
  allPi : {n : ℕ} -> List (PreSyntax {n}) -> List (PreSyntax {suc n}) -> Set
  allPi? :  {n : ℕ} -> (eqs : List (PreSyntax {n}))
    -> (Σ (List (PreSyntax {suc n})) (λ out → allPi eqs out)) ⊎  ((out :  List (PreSyntax {suc n}) ) -> ¬ allPi eqs out)
  
  _~:~_ : {n : ℕ} -> PreSyntax {n} -> List (PreSyntax {n}) -> PreSyntax {n}
  

data _~>p_ {n : ℕ} : PreSyntax {n}  -> PreSyntax {n} -> Set  where

  par-red : {a a' : _} -> {bod bod' : _ } -> {casts casts' : List (PreSyntax {n})}  -> casts ~>peq casts'
    -> a ~>p a'
    -> bod ~>p bod'
    -> (fcasts : _) (bodcasts : _) -> allPi fcasts bodcasts -- TODO will need fcasts' ?
    ->  pCast (pApp (pCast (pFun bod) fcasts)  a) casts
         ~>p ((( (bod' [ o (pCast (pFun bod') fcasts) ])  ~:~ bodcasts ) [ a' ]) ~:~ casts')

  -- structural
  par-Var : {i : Fin n} -> {casts casts' : List (PreSyntax {n})}  -> casts ~>peq casts'
    -> (pCast (pVar i) casts) ~>p (pCast (pVar i) casts')

  par-TyU : {casts casts' : List (PreSyntax {n})} -> casts ~>peq casts'
    -> (pCast pTyU casts) ~>p (pCast pTyU casts')
    
  par-TyU2 : (pTyU2) ~>p pTyU2

  par-Pi2 : {aTy aTy' : _} -> {bodTy bodTy' : _}
    -> aTy ~>p aTy' 
    -> bodTy ~>p bodTy'
    -> (pPi2 aTy bodTy) ~>p pPi2 aTy' bodTy'

  par-Pi : {aTy aTy' : _} -> {bodTy bodTy' : _} -> {casts casts' : List (PreSyntax {n})}  -> casts ~>peq casts'
    -> aTy ~>p aTy' 
    -> bodTy ~>p bodTy'
    -> pCast  (pPi aTy bodTy) casts ~>p pCast (pPi aTy' bodTy') casts'

  par-Fun : 
    {bod bod' : _} -> {casts casts' : List (PreSyntax {n})}  -> casts ~>peq casts'
    -> bod ~>p bod'
    -> pCast (pFun bod) casts ~>p pCast (pFun  bod') casts'

  par-App : {f f' a a' : _} -> {casts casts' : List (PreSyntax {n})}  -> casts ~>peq casts'
    -> f ~>p f'
    -> a ~>p a'
    -> pCast (pApp f a) casts ~>p pCast (pApp f' a') casts'




postulate
  sub-par : {n : ℕ} {a a' : PreSyntax {suc n}} {b b' : PreSyntax {n}}
    -> a ~>p  a'
    -> b ~>p b'
    -> (a [ b ] ) ~>p  (a' [ b' ])
    
  o-par : {n : ℕ} {a a' : PreSyntax { n}} 
      -> a ~>p  a'
      -> o a ~>p  o a'

  ~:~-par : {n : ℕ} {a a' : PreSyntax { n}}  {b b' : List (PreSyntax {n})}
      -> a ~>p  a'  -> b ~>peq  b'
      -> (a ~:~ b) ~>p  (a' ~:~ b') 

  confulent-eqs-par :  {n : ℕ} {a b b' : List (PreSyntax {n})}
   -> a ~>peq b
   -> a ~>peq b'
      -> Σ _ \ v  -> b ~>peq v  × b' ~>peq v

  eqs-par-refl :  {n : ℕ} {a : List (PreSyntax {n})}
   -> a ~>peq a
   
  eqs-par-max  :  {n : ℕ} -> List (PreSyntax {n})  -> List (PreSyntax {n})
  
  eqs-par-triangle  :  {n : ℕ} {a b : List (PreSyntax {n}) }
   -> a ~>peq b
   -> b ~>peq (eqs-par-max a)

  allPi?-max : {n : ℕ} -> List (PreSyntax {n})  -> List (PreSyntax {suc n}) ⊎  List (PreSyntax {n})


par-refll : {n : ℕ}  (a : PreSyntax {n}) -> a ~>p a
par-refll (pCast (pVar i) eqs) = par-Var eqs-par-refl 
par-refll (pCast pTyU eqs) = par-TyU eqs-par-refl 
par-refll (pCast (pPi x x₁) eqs) = par-Pi eqs-par-refl  (par-refll x) (par-refll x₁)
par-refll (pCast (pFun bod) eqs) = par-Fun eqs-par-refl  (par-refll bod)
par-refll (pCast (pApp x x₁) eqs) = par-App eqs-par-refl  (par-refll x) (par-refll x₁)
par-refll pTyU2 = par-TyU2
par-refll (pPi2 a a₁) = par-Pi2 (par-refll a) (par-refll a₁)

par-max : {n : ℕ} -> PreSyntax {n} -> PreSyntax {n} 
par-max (pCast (pApp (pCast (pFun bod) feqs) a) eqs) with allPi? feqs
par-max (pCast (pApp f@(pCast (pFun bod) feqs) a) eqs) | inj₁ (bodeqs , _)
  = (((par-max bod [ o (par-max f) ]) ~:~ eqs-par-max bodeqs)  [ par-max a ]) ~:~ eqs-par-max eqs
par-max (pCast (pApp f a) eqs) | inj₂ _ = pCast (pApp (par-max f) (par-max a)) (eqs-par-max eqs)
par-max (pCast (pApp f a) eqs) = pCast (pApp (par-max f) (par-max a)) (eqs-par-max eqs)
par-max (pCast (pVar i) eqs) = pCast (pVar i) (eqs-par-max eqs)
par-max pTyU2 = pTyU2
par-max (pCast pTyU eqs) = pCast pTyU (eqs-par-max eqs)
par-max (pPi2 aTy bodTy) = pPi2 (par-max aTy) (par-max bodTy)
par-max (pCast (pPi aTy bodTy) eqs) = pCast (pPi (par-max aTy) (par-max bodTy)) (eqs-par-max eqs)
par-max (pCast (pFun bod) eqs) = pCast (pFun (par-max bod)) (eqs-par-max eqs)

-- pCast ? (eqs-par-max eqs)
-- ((( (bod' [ o (pCast (pFun bod) fcasts) ])  ~:~ bodcasts ) [ a' ]) ~:~ casts')

par-triangle :  {n : ℕ} {a b : PreSyntax {n}}
   -> a ~>p b
   -> b ~>p (par-max a)
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
