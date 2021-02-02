module dependts where

open import Data.Nat
open import Data.Fin
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])


data PreSyntax {n : ℕ} : Set
data PreSyntax {n} where
  pVar : (i : Fin n) -> PreSyntax
  pTyU : PreSyntax
  pPi : PreSyntax {n} -> PreSyntax {suc n} -> PreSyntax
  pFun : PreSyntax {n} -> PreSyntax {suc n} -- annotation TODO remove?
    -> (bod : PreSyntax {suc (suc n)}) -> PreSyntax
  pApp :  PreSyntax {n} -> PreSyntax {n} -> PreSyntax

--Type : {n : ℕ} (Γ : Ctx n) -> PreSyntax {n}  -> Set
--Type Γ x = Γ |- x :: pTyU

postulate
  Ctx  : ℕ -> Set
  Emp : Ctx 0
  extCtx : {n : ℕ} -> Ctx n -> PreSyntax {n} -> Ctx (suc n)
  lookup : {n : ℕ} (Γ : Ctx n) -> (i : Fin n)  -> PreSyntax {n}

  o : {n : ℕ} -> PreSyntax {n} -> PreSyntax {suc n}
  _[_] :{n : ℕ} -> PreSyntax {suc n} -> PreSyntax {n} -> PreSyntax {n}
  -- _[_ , _] :{n : ℕ} -> PreSyntax {suc (suc n)} -> PreSyntax {n} -> PreSyntax {n} ->  PreSyntax {n}
  _[_::=_] :{n : ℕ} -> PreSyntax {suc n} -> (i : Fin n) -> PreSyntax {n} -> PreSyntax {n}
  -- TODO and wll typed variants

data _val {n : ℕ} : PreSyntax {n} -> Set where
  vTyU : pTyU val
  vPi : { aTy : PreSyntax } -> {bodTy : PreSyntax }
    -> (pPi aTy bodTy) val
  pFun : { aTy : PreSyntax } -> {bodTy : PreSyntax } -> {bod : PreSyntax {suc (suc n)} }
    -> (pFun aTy bodTy bod) val

data  _~>_ {n : ℕ} : PreSyntax {n} ->  PreSyntax {n} -> Set where
  app-red : {a aTy : PreSyntax} -> {bodTy : PreSyntax} -> {bod : PreSyntax {suc (suc n)} }
    ->  a val
    -> (pApp (pFun aTy  bodTy bod)  a) ~> ( bod [ o (pFun aTy  bodTy bod) ] [ a ]  )
  -- structural
  appf : {f f' a : PreSyntax } -> f ~> f' -> pApp f a ~> pApp f' a
  appa : {f a a' : PreSyntax } -> f val -> a ~> a' -> pApp f a ~> pApp f a'


data _|-_::_ {n : ℕ} (Γ : Ctx n) : PreSyntax {n}  -> PreSyntax {n} -> Set

data  _|-_~>p_::_ {n : ℕ} (Γ : Ctx n) : PreSyntax {n} -> PreSyntax {n} -> PreSyntax {n} -> Set

-- definitional eq
data  _|-_==_::_ {n : ℕ} (Γ : Ctx n) : PreSyntax {n} -> PreSyntax {n} -> PreSyntax {n} -> Set  where
  join : {n m m' ty : _}
    -> Γ |- m ~>p n :: ty
    -> Γ |- m' ~>p n :: ty
    -> Γ |- m == m' :: ty
    


data _|-_~>p_::_ {n} Γ  where
  par-red : {a a' aTy : _} -> {bodTy : _} -> {bod bod' : _ }
    -> Γ |- a ~>p a' :: aTy
    -> extCtx (extCtx Γ aTy) (o (pPi aTy bodTy))  |- bod ~>p bod' :: o bodTy 
    -> Γ |- (pApp (pFun aTy  bodTy bod)  a) ~>p ( bod [ o (pFun aTy  bodTy bod') ] [ a' ]  ) :: (bodTy [ a ])
  
    -- structural
  par-Pi : {aTy aTy' : _} -> {bodTy bodTy' : _}
    -> Γ |- aTy ~>p aTy' :: pTyU
    -> extCtx Γ aTy  |- bodTy ~>p bodTy' :: pTyU
    -> Γ |- (pPi aTy bodTy) ~>p pPi aTy' bodTy' :: pTyU
  par-Fun :
    {aTy aTy' : _} -> {bodTy bodTy' : _} ->
    -- {aTy : _} -> {bodTy : _} ->
    {bod bod' : _}
    -> Γ |- aTy ~>p aTy' :: pTyU  
    -> extCtx Γ aTy  |- bodTy ~>p bodTy' :: pTyU
    -- -> Γ |- aTy :: pTyU -- let conversion deal with these?
    -- -> extCtx Γ aTy  |- bodTy :: pTyU
    -> extCtx (extCtx Γ aTy) (o (pPi aTy bodTy))  |- bod ~>p bod' :: o bodTy 
    -> Γ |- (pFun aTy bodTy bod) ~>p pFun aTy' bodTy' bod' ::  pPi aTy bodTy
  par-App : {aTy f f' a a' : _} -> {bodTy : _}
    -> Γ |- f ~>p f' :: pPi aTy bodTy
    -> Γ |- a ~>p a' :: aTy
    -> Γ |- (pApp f a) ~>p (pApp f' a') :: (bodTy [ a ])

  -- TODO this could be admissable
  par-refl : {m n : _} -> Γ |- m :: n
    -> Γ |- m ~>p m :: n
    -- TODO step?

trans-~> : {n : ℕ} {Γ : Ctx n} {a b c ty : _}
   -> Γ |- a ~>p b :: ty
   -> Γ |- b ~>p c :: ty
   -> Γ |- a ~>p c :: ty
trans-~> = {!!}

confulent : {n : ℕ} {Γ : Ctx n} {m a a'  ty : _}
   -> Γ |- m ~>p a :: ty
   -> Γ |- m ~>p a' :: ty
   -> Σ _ \ v  ->  Γ |- a ~>p v :: ty × Γ |- a' ~>p v :: ty
confulent = {!!}

stable-tyu :  {n : ℕ} {Γ : Ctx n}  {a  ty : _}
   -> Γ |- pTyU ~>p a :: ty
   -> a ≡ pTyU
stable-tyu (par-refl x) = refl


stable-pi :  {n : ℕ} {Γ : Ctx n}  {a aTy ty : _} {bodTy : _}
   -> Γ |- pPi aTy bodTy ~>p a :: ty
   ->  Σ _ \ aTy'  -> Σ _ \ bodTy'  -> a ≡ pPi aTy' bodTy' 
stable-pi (par-Pi {_} {aTy'} {_} {bodTy'} x x₁) = aTy' , bodTy' , refl
stable-pi {_} {_}  {_}  {aTy} {_}  {bodTy} (par-refl x) = aTy , bodTy , refl


data _|-_::_ {n} Γ  where
  Var :  (v : Fin n) -> Γ |- pVar v :: lookup Γ v
  TyU : Γ |- pTyU :: pTyU
  Pi : { aTy : PreSyntax } -> {bodTy : PreSyntax }
    -> Γ |- aTy :: pTyU ->  extCtx Γ aTy  |- bodTy :: pTyU
    -> Γ |-  pPi aTy bodTy :: pTyU
  Fun : { aTy : PreSyntax } -> {bodTy : PreSyntax }
    -> {bod : PreSyntax }
    -> Γ |-  pFun aTy bodTy bod  :: pPi aTy bodTy
  App : {f a aTy : PreSyntax } -> {bodTy : PreSyntax }
    -> Γ |-  f  :: pPi aTy bodTy -> Γ  |- a :: aTy 
    -> Γ |-  pApp f a  :: (bodTy [ a ])
  Conv : {a m m' : PreSyntax }
    -> Γ |-  a  :: m
    -> Γ |- m == m' :: pTyU
    -> Γ |-  a  :: m'

wf-ty : {n : ℕ} {Γ : Ctx n} {a ty : _}
  -> Γ |- a :: ty
  -> Γ |- ty :: pTyU
wf-ty = {!!}


-- TODO need a stronger hypothisis
--consitent : {aTy : _} -> {bodTy : _} -> 

trans-== : {n : ℕ} {Γ : Ctx n} {a b c ty : _}
    -> Γ |- a == b :: ty
    -> Γ |- b == c :: ty
    -> Γ |- a == c :: ty
trans-== (join {n} an bn) (join {m} bm cm) with confulent bn bm
trans-== (join {n} an bn) (join {m} bm cm) | o , mo , n~>o = join {_} {_} {o} (trans-~> an mo) (trans-~> cm n~>o) -- ...

refl-== : {n : ℕ} {Γ : Ctx n} {a ty : _}
    -> Γ |- a :: ty
    -> Γ |- a == a :: ty
refl-== x = join (par-refl x) (par-refl x)

tyu=/=pi : {n : ℕ} {Γ : Ctx n} {aty ty : _} {bodTy : _}
    -> ¬ Γ |- pTyU == pPi aty bodTy :: ty
tyu=/=pi (join {n} an bn) with (stable-tyu an , stable-pi bn)
tyu=/=pi (join {.pTyU} an bn) | refl , _ , _ , ()

{-
canonical-form-ty' : {m tyu : _}
  -> Emp |- m :: tyu -> m val
  -> Emp |- tyu == pTyU :: pTyU
  -> m ≡ pTyU ⊎ (Σ _ \ aTy  -> Σ _ \ bodTy   -> m ≡ pPi aTy bodTy)
canonical-form-ty' der val eq = {!!}
-}
canonical-form-pi : {m pi aTy : _} -> {bodTy : _}
  -> Emp |- m :: pi -> m val
  -> Emp |- pi == pPi aTy bodTy :: pTyU
  ->  Σ _ \ aTy'  -> Σ _ \ bodTy'  ->  Σ _ \ bod  -> m ≡ pFun aTy' bodTy' bod
canonical-form-pi TyU vTyU eq = ⊥-elim (tyu=/=pi eq) --!
canonical-form-pi (Conv der x) vTyU eq = canonical-form-pi der vTyU (trans-==  x eq)
canonical-form-pi (Pi der der₁) vPi eq = ⊥-elim (tyu=/=pi eq) --!
canonical-form-pi (Conv der x) vPi eq = canonical-form-pi  der vPi (trans-==  x eq)
canonical-form-pi der (pFun {aTy} {bodTy} {bod}) eq = aTy , bodTy , bod , refl -- ok



progress : {m n : _} -> Emp |- m :: n -> m val ⊎ Σ PreSyntax \ m' -> m ~> m'
progress (Conv x x₁) = progress x
progress TyU = inj₁ vTyU
progress (Pi x x₁) = inj₁ vPi
progress Fun = inj₁ pFun
progress (App fDer aDer) with (progress fDer , progress aDer)
progress (App {f} {a} fDer aDer) | inj₂ (f' , f~>f') , _ = inj₂ (pApp f' a , appf f~>f')
progress (App {f} {a} fDer aDer) | inj₁ fval , inj₂ (a' , a~>a') = inj₂ (pApp f a' , appa fval a~>a')
progress (App fDer aDer) | inj₁ fval , inj₁ aval with canonical-form-pi fDer fval (refl-== (wf-ty fDer))
progress (App {_} {a} fDer aDer) | inj₁ fval , inj₁ aval | aTy' , bodTy' , bod , refl
  = inj₂ (((bod [ o (pFun aTy' bodTy' bod) ]) [ a ]) , app-red aval)

