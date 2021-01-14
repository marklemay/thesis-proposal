module ChurchRosser where

open import Data.String
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)

data Term : Set where
  Var : String -> Term
  App : Term -> Term -> Term
  Lam : String -> Term -> Term

naiveSubst : (replaceThis : String) -> (withThis : Term) -> (inThis : Term) -> Term
naiveSubst = {!!}

subst : (replaceThis : String) -> (withThis : Term) -> (inThis : Term) -> Term
subst = {!!}

-- beta reductions
data Step  : Term -> Term -> Set where
  ctx-App-l : {a a' b : Term} -> Step a a' -> Step (App a b)  (App a' b)
  ctx-App-r : {a b b' : Term} -> Step b b' -> Step (App a b)  (App a b')
  ctx-lamb : {x : String}{b b' : Term} -> Step b b' -> Step (Lam x b)  (Lam x b')
  beta : {x : String}{b c : Term} -> Step (App (Lam x b) c)  (subst x c b)

-- tranistive reflexive closure
data Step*  : Term -> Term -> Set where
  refl-step :  {a : Term} -> Step* a a
  trans-step :  {a b c : Term} -> Step a b -> Step* b c -> Step* a c 


data AlphaEquiv  : Term -> Term -> Set where
  -- ..

confluence : (a b c : Term) -> Step* a b  -> Step* a c -> Σ Term λ d → Σ Term λ d' → (Step* b d) ×  (Step* c d') × AlphaEquiv d d'
confluence = {!!}
