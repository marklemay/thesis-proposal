module graph4 where

open import Data.Fin hiding  (_+_; _<_; _≤_; _≤?_; _-_; pred)
open import Data.Nat -- using (ℕ; zero; suc; _+_;  _*_; _^_; _∸_; _≤_; _≤?_)
open import Data.Bool hiding  (_<_; _≤_; _≤?_)
open import Data.List --  hiding (sum; map; allFin)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Relation.Binary.PropositionalEquality

open import Data.Vec hiding (_++_)
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


module forExamle where
  record GraphAL {n : ℕ} : Set  where
    field
      edge :  Vec (List (Fin n)) n
  open GraphAL


  disconnected : {n : ℕ} -> GraphAL {n}
  edge disconnected = Data.Vec.replicate []

  diag : {n : ℕ} -> GraphAL {n}
  edge diag = Data.Vec.tabulate (λ v → v ∷ [])

  -- bad equality
  g1 : GraphAL {3}
  edge g1 = ( (0F ∷ 1F ∷ 2F ∷ [])) ∷ (1F ∷ []) ∷ (2F ∷ []) ∷ []

  g2 : GraphAL {3}
  edge g2 = ( (0F ∷ 2F ∷ 1F ∷ [])) ∷ (1F ∷ []) ∷ (2F ∷ []) ∷ []


record Graph {n : ℕ} : Set  where
  field
    edge :  Vec (Vec Bool n) n
open Graph


disconnected : {n : ℕ} -> Graph {n}
edge disconnected = Data.Vec.replicate (Data.Vec.replicate false)

diag : {n : ℕ} -> Graph {n}
edge diag = Data.Vec.tabulate λ from → updateAt from (λ _ → true) (Data.Vec.replicate false)

update2  : {n : ℕ} -> (Fin n) -> (Fin n) -> Bool -> Vec (Vec Bool n) n -> Vec (Vec Bool n) n
update2 from to b = updateAt from (updateAt to (λ _ → b)) 

fromEdges : {n : ℕ} -> List ((Fin n) × (Fin n)) -> Graph {n}
fromEdges [] = diag
edge (fromEdges ((from , to) ∷ ls)) = update2 from to true (edge (fromEdges ls))

g1 : Graph {3}
g1 = fromEdges ((2F , 0F)  ∷  (1F , 2F)  ∷ (0F , 1F)  ∷  [])

g2 : Graph {3}
g2 = fromEdges ((0F , 1F)  ∷  (1F , 2F)  ∷ (2F , 0F)  ∷  [])

_ : g1 ≡ g2
_ = refl
