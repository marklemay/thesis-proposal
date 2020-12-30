module graph3 where

open import Data.Fin hiding  (_+_; _<_; _≤_; _≤?_; _-_; pred)
open import Data.Nat -- using (ℕ; zero; suc; _+_;  _*_; _^_; _∸_; _≤_; _≤?_)
open import Data.Bool hiding  (_<_; _≤_; _≤?_)
open import Data.List --  hiding (sum; map; allFin)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Relation.Binary.PropositionalEquality
{-
open import Relation.Nullary using (¬_)
open import Data.Nat.Properties
--open import Data.Vec hiding (_++_)
open import Data.List --  hiding (sum; map; allFin)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.All hiding (self)
open import Data.List.Relation.Unary.All.Properties
open import Data.Maybe  hiding (map)
open import Data.Sum  hiding (map)
open import Data.Empty
-}

record Graph {n : ℕ} : Set  where
  field
    edge : (from : Fin n) -> (to : Fin n) -> Bool
open Graph

disconnected : {n : ℕ} -> Graph {n}
edge disconnected _ _  = false

diag : {n : ℕ} -> Graph {n}
edge diag from to with Data.Fin._≟_ from to 
edge diag from to | yes p = true
edge diag from to | no ¬p = false

fromEdges : {n : ℕ} -> List ((Fin n) × (Fin n)) -> Graph {n}
fromEdges [] = diag
edge (fromEdges ((from' , to') ∷ ls)) from to with Data.Fin._≟_ from' from , Data.Fin._≟_ to' to
edge (fromEdges ((from' , to') ∷ ls)) from to | yes _ , yes _ = true
edge (fromEdges ((from' , to') ∷ ls)) from to | _ , _ = edge (fromEdges ls) from to

-- contrived example where deffinitional equality dos not hold
g1 : Graph {3}
edge g1 0F 0F = true
edge g1 0F 1F = true
edge g1 0F 2F = false

edge g1 1F 0F = false
edge g1 1F 1F = true
edge g1 1F 2F = true

edge g1 2F 0F = true
edge g1 2F 1F = false
edge g1 2F 2F = true

g2 : Graph {3}
g2 = fromEdges ((0F , 1F)  ∷  (1F , 2F)  ∷ (2F , 0F)  ∷  [])

_ : g1 ≡ g1
_ = refl {_} {_} {g1}

{-
_ : g1 ≡ g2
_ = refl {_} {_} {g1}
-}

-- becuase there is no automatic function extentionality, these graphs can't even be made propositionally equal



