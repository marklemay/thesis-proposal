module dependts where

open import Data.Nat
open import Data.Fin
-- open import Data.Vec   hiding (lookup ; [_])
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])


data PreSyntax {n : ℕ} : Set
data PreSyntax {n} where
  pVar : (i : Fin n) -> PreSyntax
  pTyU : PreSyntax
  pPi :  (aTy : PreSyntax {n}) -> (bodTy :  PreSyntax {suc n}) -> PreSyntax
  pFun : (aTy : PreSyntax {n}) -> (bodTy :  PreSyntax {suc n}) -- annotations
    -> (bod : PreSyntax {suc (suc n)}) -> PreSyntax
  pApp :  (f : PreSyntax {n}) -> (a : PreSyntax {n}) -> PreSyntax



-- degenerate context extention
extPreSyntax : {i j : ℕ}
  -> (ρ : (Fin i -> Fin j))
  -> Fin (suc i) -> (Fin (suc j))
extPreSyntax ρ 0F = 0F
extPreSyntax ρ (suc x) = suc (ρ x)

 
renamePreSyntax : {i j : ℕ}
  -> (ρ : (Fin i -> Fin j))
  -> (PreSyntax {i} -> PreSyntax {j})
renamePreSyntax ρ (pVar i) = pVar (ρ i)
renamePreSyntax ρ pTyU = pTyU
renamePreSyntax ρ (pPi aTy bodTy) = pPi (renamePreSyntax ρ aTy) (renamePreSyntax (extPreSyntax ρ) bodTy)
renamePreSyntax ρ (pFun aTy bodTy bod) = pFun (renamePreSyntax ρ aTy) (renamePreSyntax (extPreSyntax ρ) bodTy) ((renamePreSyntax (extPreSyntax (extPreSyntax ρ)) bod))
renamePreSyntax ρ (pApp f a) = pApp (renamePreSyntax ρ f) (renamePreSyntax ρ a)

o : {n : ℕ} -> PreSyntax {n} -> PreSyntax {suc n}
o = renamePreSyntax (raise 1)

{-
extsPreSyntax : ∀ {i j}
  → (σ : (Fin i → PreSyntax {j} ))
  → (PreSyntax {i}  → PreSyntax {suc j})
extsPreSyntax = {!!}

substPreSyntax : ∀ {i j}
  → (σ : (Fin i → PreSyntax {j} ))
  → (PreSyntax {i}  → PreSyntax {j})
substPreSyntax σ (pVar i) = σ i
substPreSyntax σ pTyU = pTyU
substPreSyntax σ (pPi  aTy bodTy) = pPi {!!} {!!}
substPreSyntax σ (pFun aTy bodTy bod) = pFun {!!} {!!} {!!}
substPreSyntax σ (pApp f a) = pApp {!!} {!!}
-}
postulate
  substPreSyntax : ∀ {i j}
    → (σ : (Fin i → PreSyntax {j} ))
    → (PreSyntax {i}  → PreSyntax {j})


_[_] :{n : ℕ} -> PreSyntax {suc n} -> PreSyntax {n} -> PreSyntax {n}
_[_] {n} inthis withThis = substPreSyntax {suc n} {n} σ inthis
  where
    σ : Fin (suc n) → PreSyntax {n}
    σ 0F = withThis
    σ (suc x) = pVar x


data PreCtx : ℕ -> Set where
  pEmp : PreCtx 0
  _,,_ : {n : ℕ} -> PreCtx n -> PreSyntax {n} -> PreCtx (suc n)


--prweak : {n : ℕ} -> Fin (suc n) -> PreCtx n
--prweak = {!!}
--prelookup : {n : ℕ} (Γ : Ctx n) -> (i : Fin n)  -> PreSyntax {n}

--Ctx' : {!!}
--Ctx' n = Vec (PreSyntax {n})

postulate
  Ctx  : ℕ -> Set
  Emp : Ctx 0
  extCtx : {n : ℕ} -> Ctx n -> PreSyntax {n} -> Ctx (suc n)
  lookup : {n : ℕ} (Γ : Ctx n) -> (i : Fin n)  -> PreSyntax {n}

 -- o : {n : ℕ} -> PreSyntax {n} -> PreSyntax {suc n}
 -- _[_] :{n : ℕ} -> PreSyntax {suc n} -> PreSyntax {n} -> PreSyntax {n}
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

data  _|-_~>*p_::_ {n : ℕ} (Γ : Ctx n) : PreSyntax {n} -> PreSyntax {n} -> PreSyntax {n} -> Set

-- definitional eq
data  _|-_==_::_ {n : ℕ} (Γ : Ctx n) : PreSyntax {n} -> PreSyntax {n} -> PreSyntax {n} -> Set  where
  join : {n m m' ty : _}
    -> Γ |- m ~>*p n :: ty
    -> Γ |- m' ~>*p n :: ty
    -> Γ |- m == m' :: ty
    

data _~>p_ {n : ℕ} : PreSyntax {n}  -> PreSyntax {n} -> Set  where
  par-red : {a a' aTy aTy' : _} -> {bodTy bodTy' : _} -> {bod bod' : _ }
    -> (a-a' : a ~>p a')
    -> (bod-bod' : bod ~>p bod')
    -> (aTy-aTy' : aTy ~>p aTy')
    -> (bodTy-bodty' : bodTy ~>p bodTy')
    -> (pApp (pFun aTy  bodTy bod)  a) ~>p ( bod' [ o (pFun aTy'  bodTy' bod') ] [ a' ]  )

  -- structural

  par-Var : {i : Fin n}
    -> (pVar i) ~>p pVar i
    
  par-TyU : (pTyU) ~>p pTyU
    
  par-Pi : {aTy aTy' : _} -> {bodTy bodTy' : _}
    -> aTy ~>p aTy' 
    -> bodTy ~>p bodTy'
    -> (pPi aTy bodTy) ~>p pPi aTy' bodTy'
    
  par-Fun :
    {aTy aTy' : _} -> {bodTy bodTy' : _} ->
    {bod bod' : _}
    -> bod ~>p bod'
    -> aTy ~>p aTy'
    -> bodTy ~>p bodTy'
    -> (pFun aTy bodTy bod) ~>p pFun aTy' bodTy' bod'
    
  par-App : {f f' a a' : _}
    -> f ~>p f'
    -> a ~>p a'
    -> (pApp f a) ~>p (pApp f' a')



-- very influenced by https://plfa.github.io/Confluence/#parallel-reduction-satisfies-the-diamond-property
-- the way this is presented, par-max may not be par, but instead withinexactly 2 par reductions away
par-max : {n : ℕ} -> PreSyntax {n} -> PreSyntax {n} 
par-max (pApp (pFun aTy bodTy bod) a) = (par-max bod) [ o (pFun (par-max aTy) (par-max bodTy) (par-max bod)) ] [ par-max a ]
par-max (pVar i) = pVar i
par-max pTyU = pTyU
par-max (pPi aTy bodTy) = pPi (par-max aTy) (par-max bodTy)
par-max (pFun aTy bodTy bod) = pFun (par-max aTy) (par-max bodTy) (par-max bod)
par-max (pApp f a) = pApp (par-max f) (par-max a)

postulate
  sub-par : {n : ℕ} {a a' : PreSyntax {suc n}} {b b' : PreSyntax {n}}
    -> a ~>p  a'
    -> b ~>p b'
    -> (a [ b ] ) ~>p  (a' [ b' ])

  o-par : {n : ℕ} {a a' : PreSyntax { n}} 
      -> a ~>p  a'
      -> o a ~>p  o a'

-- annoying name
par-triangle :  {n : ℕ} {a b : PreSyntax {n}}
   -> a ~>p b
   -> b ~>p (par-max a)
par-triangle (par-red par-arg par-bod par-aTy par-bodTy)
  = sub-par (sub-par (par-triangle par-bod) (o-par (par-triangle (par-Fun par-bod par-aTy par-bodTy)))) (par-triangle par-arg)
par-triangle (par-App  (par-Fun par-f par-f₁ par-f₂) par-a)
  = par-red (par-triangle par-a) (par-triangle par-f) (par-triangle par-f₁) (par-triangle par-f₂)
par-triangle par-Var = par-Var
par-triangle par-TyU = par-TyU
par-triangle (par-Pi par-aTy par-bodTy) = par-Pi (par-triangle par-aTy) (par-triangle par-bodTy)
par-triangle (par-Fun par-bod par-aTy par-bodT)
  = par-Fun (par-triangle par-bod) (par-triangle par-aTy) (par-triangle par-bodT)
 -- applications spelled out
par-triangle (par-App (par-red par-f par-f₁ par-f₂ par-f₃) par-a) = par-App (par-triangle (par-red par-f par-f₁ par-f₂ par-f₃)) (par-triangle par-a)
par-triangle (par-App par-Var par-a) = par-App par-Var (par-triangle par-a)
par-triangle (par-App par-TyU par-a) = par-App par-TyU (par-triangle par-a)
par-triangle (par-App (par-Pi par-f par-f₁) par-a) = par-App (par-Pi (par-triangle par-f) (par-triangle par-f₁)) (par-triangle par-a)
par-triangle (par-App  (par-App par-f par-f₁) par-a) = par-App (par-triangle (par-App par-f par-f₁)) (par-triangle par-a)



par-refll : {n : ℕ}  (a : PreSyntax {n}) -> a ~>p a
par-refll (pVar i) = par-Var
par-refll pTyU = par-TyU
par-refll (pPi a a₁) = par-Pi (par-refll a) (par-refll a₁)
par-refll (pFun a a₁ a₂) = par-Fun (par-refll a₂) (par-refll a) (par-refll a₁)
par-refll (pApp a a₁) = par-App (par-refll a) (par-refll a₁)


confulent-~> : {n : ℕ} {a b b' : PreSyntax {n}}
   -> a ~>p b
   -> a ~>p b'
   -> Σ _ \ v  -> b ~>p v  × b' ~>p v
confulent-~>  {_} {a} ab ab' = par-max a , par-triangle ab , par-triangle ab'


-- typed transitive reflective closer
data _|-_~>*p_::_ {n} Γ  where
  par-refl : {m n : _} -> Γ |- m :: n  
    -> Γ |- m ~>*p m :: n                        -- TODO this could be admissable
    
  par-step : {a b c n : _}
    -> Γ |- a ~>*p b :: n
    -> b ~>p c
    -> Γ |- a ~>*p c :: n

postulate
  preservation-~>* : {n : ℕ} {Γ : Ctx n} {a b c ty : _}
     -> Γ |- a ~>*p b :: ty
     -> Γ |- b :: ty

trans-~>* : {n : ℕ} {Γ : Ctx n} {a b c ty : _}
   -> Γ |- a ~>*p b :: ty
   -> Γ |- b ~>*p c :: ty
   -> Γ |- a ~>*p c :: ty
trans-~>* {n} {Γ} {a} {b} {.b} ab (par-refl x) = ab
trans-~>* {n} {Γ} {a} {b} {c} ab (par-step bc x) = par-step (trans-~>* ab bc) x

strip-~>* : {n : ℕ} {Γ : Ctx n} {a b d  ty : _}
   -> a ~>p b
   -> Γ |- a ~>*p d :: ty
   -> Σ _ \ v  ->  Γ |- b ~>*p v :: ty × d ~>p v
strip-~>* {n} {Γ} {a} {b} {.a} ab (par-refl aty) = b , ((par-refl (preservation-~>* {_} {_} {a} {b} {b} (par-step (par-refl aty) ab))) , ab) -- everything but preservation
strip-~>* {n} {Γ} {a} {b} {d} ab (par-step {_} {c} ac cd) with strip-~>* ab ac
strip-~>* {n} {Γ} {a} {b} {d} ab (par-step {.a} {c} ac cd) | v' , bv' , cv' with confulent-~> cv' cd
strip-~>* {n} {Γ} {a} {b} {d} ab (par-step {.a} {c} ac cd) | v' , bv' , cv' | v , v'v , dv = v , ((par-step bv' v'v) , dv)
{- TODO diagram -}

confulent-~>* : {n : ℕ} {Γ : Ctx n} {m a a'  ty : _}
   -> Γ |- m ~>*p a :: ty
   -> Γ |- m ~>*p a' :: ty
   -> Σ _ \ v  ->  Γ |- a ~>*p v :: ty × Γ |- a' ~>*p v :: ty
confulent-~>* {n} {Γ} {m} {.m} {a'} {ty} (par-refl x) r = a' , (r , (par-refl (preservation-~>* {n} {Γ} {m} {a'} {a'} r)))
confulent-~>* {n} {Γ} {m} {a} {.m} {ty} l (par-refl tyder) = a , (par-refl (preservation-~>* {n} {Γ} {m} {a} {a} l) , l)
confulent-~>* {n} {Γ} {m} {a} {a'} {ty} (par-step {_} {b} mb ba) (par-step {_} {b'} mb' b'a') with confulent-~>* mb mb'
confulent-~>* {n} {Γ} {m} {a} {a'} {ty} (par-step {.m} {b} mb ba) (par-step {.m} {b'} mb' b'a') | v' , bv' , b'v' with strip-~>* ba bv'
confulent-~>* {n} {Γ} {m} {a} {a'} {ty} (par-step {.m} {b} mb ba) (par-step {.m} {b'} mb' b'a') | v' , bv' , b'v' | c , ac , v'c with strip-~>* b'a' (par-step b'v' v'c)
confulent-~>* {n} {Γ} {m} {a} {a'} {ty} (par-step {.m} {b} mb ba) (par-step {.m} {b'} mb' b'a') | v' , bv' , b'v' | c , ac , v'c | v , a'v , cv = v , ((par-step ac cv) , a'v)
{- TODO diagram -}

stable-tyu :  {n : ℕ} {Γ : Ctx n}  {a  ty : _}
   -> Γ |- pTyU ~>*p a :: ty
   -> a ≡ pTyU
stable-tyu (par-refl x) = refl
stable-tyu (par-step rest step) with stable-tyu rest
stable-tyu (par-step rest par-TyU) | refl = refl


stable-pi :  {n : ℕ} {Γ : Ctx n}  {a aTy ty : _} {bodTy : _}
   -> Γ |- pPi aTy bodTy ~>*p a :: ty
   ->  Σ _ \ aTy'  -> Σ _ \ bodTy'  -> a ≡ pPi aTy' bodTy' 
stable-pi {n} {Γ}  {a} {aTy} {ty} {bodTy} (par-refl x) = aTy , bodTy , refl
stable-pi (par-step front step) with stable-pi front
stable-pi (par-step front (par-Pi step step₁)) | fst , xx = _ , _ , refl

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

postulate
  wf-ty : {n : ℕ} {Γ : Ctx n} {a ty : _} -- TODO: rename regularity
    -> Γ |- a :: ty
    -> Γ |- ty :: pTyU

trans-== : {n : ℕ} {Γ : Ctx n} {a b c ty : _}
    -> Γ |- a == b :: ty
    -> Γ |- b == c :: ty
    -> Γ |- a == c :: ty
trans-== (join {n} an bn) (join {m} bm cm) with confulent-~>* bn bm
trans-== (join {n} an bn) (join {m} bm cm) | o , mo , n~>o = join {_} {_} {o} (trans-~>*  an mo) (trans-~>*  cm n~>o)

refl-== : {n : ℕ} {Γ : Ctx n} {a ty : _}
    -> Γ |- a :: ty
    -> Γ |- a == a :: ty
refl-== x = join (par-refl x) (par-refl x)

tyu=/=pi : {n : ℕ} {Γ : Ctx n} {aty ty : _} {bodTy : _}
    -> ¬ Γ |- pTyU == pPi aty bodTy :: ty
tyu=/=pi (join {n} an bn) with stable-tyu an
tyu=/=pi (join {.pTyU} an bn) | refl with stable-pi bn
tyu=/=pi (join {.pTyU} an bn) | refl | ()


canonical-form-pi : {m pi aTy : _} -> {bodTy : _}
  -> Emp |- m :: pi -> m val
  -> Emp |- pi == pPi aTy bodTy :: pTyU
  ->  Σ _ \ aTy'  -> Σ _ \ bodTy'  ->  Σ _ \ bod  -> m ≡ pFun aTy' bodTy' bod
canonical-form-pi (Conv der x) vTyU eq = canonical-form-pi der vTyU (trans-==  x eq)
canonical-form-pi (Conv der x) vPi eq = canonical-form-pi  der vPi (trans-==  x eq)
canonical-form-pi TyU vTyU eq = ⊥-elim (tyu=/=pi eq) --!
canonical-form-pi (Pi der der₁) vPi eq = ⊥-elim (tyu=/=pi eq) --!
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

