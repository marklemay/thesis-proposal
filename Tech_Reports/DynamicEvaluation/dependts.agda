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
  pFun : -- PreSyntax {n} -> PreSyntax {suc n} -- annotations
    -- ->
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
  _~:~_ : {n : ℕ} -> PreSyntax {n} -> List (PreSyntax {n}) -> PreSyntax {n}
  

data _~>p_ {n : ℕ} : PreSyntax {n}  -> PreSyntax {n} -> Set  where

  par-red : {a a' : _} -> {bod bod' : _ } -> {casts casts' : List (PreSyntax {n})}  -> casts ~>peq casts'
    -> a ~>p a'
    -> bod ~>p bod'
    -> (fcasts : _) (bodcasts : _) -> allPi fcasts bodcasts -- TODO will need fcasts'
    ->  pCast (pApp (pCast (pFun bod) fcasts)  a) casts
         ~>p ((( (bod' [ o (pCast (pFun bod) fcasts) ])  ~:~ bodcasts ) [ a' ]) ~:~ casts')

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

  par-Fun : -- crimp this to refl
    {bod : _} -> {casts : List (PreSyntax {n})} 
    -> pCast (pFun bod) casts ~>p pCast (pFun  bod) casts
{-
  par-Fun : 
    {bod bod' : _} -> {casts casts' : List (PreSyntax {n})}  -> casts ~>peq casts'
    -> bod ~>p bod'
    -> pCast (pFun bod) casts ~>p pCast (pFun  bod') casts'
-}
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


  eqs-par :  {n : ℕ} {a b b' : List (PreSyntax {n})}
   -> a ~>peq b
   -> a ~>peq b'
      -> Σ _ \ v  -> b ~>peq v  × b' ~>peq v

  eqs-par-refl :  {n : ℕ} {a : List (PreSyntax {n})}
   -> a ~>peq a

par-refll : {n : ℕ}  (a : PreSyntax {n}) -> a ~>p a
par-refll = {!!}


confulent-~> : {n : ℕ} {a b b' : PreSyntax {n}}
   -> a ~>p b
   -> a ~>p b'
   -> Σ _ \ v  -> b ~>p v  × b' ~>p v
 
confulent-~> {_} {pCast (pApp (pCast (pFun bod) feqs) a) eqs} (par-red {_} {_} {_} {bod'} eqs-casts' a-a' bod-bod' .feqs bodcasts tysok) (par-App eqs-casts'' (par-Fun  ) a-a'')
  with (eqs-par eqs-casts' eqs-casts'' , confulent-~> a-a' a-a''  )
... | ((veqs , casts'-veqs , casts''-veqs ) , (va , a'-va , a''-va))  --  with  confulent-~> bod-bod' (par-refll bod)
  = ((( (bod' [ o (pCast (pFun bod) feqs) ] )  ~:~  bodcasts ) [ va ])  ~:~ veqs) , ~:~-par (sub-par (par-refll _) a'-va) casts'-veqs , par-red casts''-veqs a''-va bod-bod' feqs bodcasts tysok


-- pCast (pApp (pCast (pFun bod) fcasts)  a) casts  ~>p ((( (bod' [ o (pCast (pFun bod) fcasts) ])  ~:~ bodcasts ) [ a' ]) ~:~ casts')

--, (vbod , _) = ((( (bod' [ o (pCast (pFun bod) feqs) ] )  ~:~  bodcasts ) [ va ])  ~:~ veqs) , {!!} , {!!}

-- ~>p ((( (bod [ o (pCast (pFun bod') fcasts) ])  ~:~ bodcasts ) [ a' ]) ~:~ casts')

confulent-~> {_} {pCast (pApp (pCast (pFun bod) feqs) arg) eqs} (par-red x ab  bod-bod' .feqs bodcasts x₁) (par-red eqs-cast arg-a'' bod-bod'' .feqs bodcasts₁ tysok) = {!!}
confulent-~> {_} {pCast (pApp (pCast (pFun bod) feqs) a) eqs} (par-App x ab ab₁) ab' = {!!}

confulent-~> {_} {pCast (pApp (pCast (pVar i) feqs) a) eqs} ab ab' = {!!}
confulent-~> {_} {pCast (pApp (pCast pTyU feqs) a) eqs} ab ab' = {!!}
confulent-~> {_} {pCast (pApp (pCast (pPi x x₁) feqs) a) eqs} ab ab' = {!!}
confulent-~> {_} {pCast (pApp (pCast (pApp x x₁) feqs) a) eqs} ab ab' = {!!}

confulent-~> {_} {pCast (pApp pTyU2 a) eqs} ab ab' = {!!}
confulent-~> {_} {pCast (pApp (pPi2 f f₁) a) eqs} ab ab' = {!!}

confulent-~> {_} {pCast (pVar i) eqs} ab ab' = {!!}
confulent-~> {_} {pCast pTyU eqs} ab ab' = {!!}
confulent-~> {_} {pCast (pPi x x₁) eqs} ab ab' = {!!}
confulent-~> {_} {pCast (pFun bod) eqs} ab ab' = {!!}
confulent-~> {_} {pTyU2} ab ab' = {!!}
confulent-~> {_} {pPi2 a a₁} ab ab' = {!!}


{-
confulent-~> {_} {pCast (pApp (pCast (pFun bod) feqs) a) eqs} (par-red eqs-casts' a-a' bod-bod' .feqs bodcasts tysok) (par-App eqs-casts'' (par-Fun feqs-casts'' bod-bod'') a-a'')
  with eqs-par eqs-casts' eqs-casts'' , confulent-~> a-a' a-a'' , confulent-~> bod-bod' bod-bod''
... | xx = {!!}

confulent-~> {_} {a} {b} {b'} ab ab' = {!!}



data _val {n : ℕ} : PreSyntax {n} -> Set where
  vTyU2 : pTyU2 val
  vPi2 : { aTy : PreSyntax } -> {bodTy : PreSyntax }
     -> (pPi2 aTy bodTy) val
  -- ..
-}
