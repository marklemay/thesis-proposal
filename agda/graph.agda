module graph where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _≤_; _≤?_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding  (_+_; _<_; _≤_; _≤?_)
open import Data.Bool hiding  (_<_; _≤_; _≤?_)
open import Data.Vec hiding (_++_)
open import Data.List  hiding (sum; map; allFin)
open import Data.Maybe  hiding (map)
open import Data.Product hiding (map)


sumF : (n : ℕ) -> (fn : Fin n -> ℕ) -> ℕ
sumF n fn = sum (map fn (allFin n))

record Graph {n : ℕ} : Set where
  field
    edge : (from : Fin n) -> (to : Fin n) -> ℕ
open Graph

clique : (v : ℕ) -> (vol : ℕ) -> Graph {v}
edge (clique v vol) from to = vol  -- allows self flow

incoming-flow : {n : ℕ} -> (g : Graph {n}) -> (vert : Fin n) -> ℕ
incoming-flow {n} g vert = sumF n (λ inV → edge g inV vert)

outgoing-flow : {n : ℕ} -> (g : Graph {n}) -> (vert : Fin n) -> ℕ
outgoing-flow {n} g vert = sumF n (λ outV → edge g vert outV)

e1 = incoming-flow (clique 3 1) (# 0)

smallest : {A : Set} -> List (ℕ × A) -> Maybe (ℕ × A × List (ℕ × A) )
smallest {A} [] = nothing
smallest {A} ((n , a) ∷ x₁) = just (loop n a [] x₁)
  where
    loop :  ℕ -> A -> (before : List (ℕ × A)) -> (after : List (ℕ × A))  -> ℕ × A × List (ℕ × A)
    loop n a before [] = n , a , before
    loop n a before ((n' , a') ∷ after) with (n ≤? n')
    loop n a before ((n' , a') ∷ after) | Relation.Nullary.yes _ = loop n a ((n' , a') ∷ before) after
    loop n a before ((n' , a') ∷ after) | Relation.Nullary.no _ = loop n' a' ((n , a) ∷ before) after

outgoing-edges : {n : ℕ} -> Graph {n} -> (from : Fin n) -> List (ℕ × Fin n) 
outgoing-edges = ?

-- dijkstra's algorithm
sortest-path : {n : ℕ} -> Graph {n} -> (from : Fin n) -> (to : Fin n) -> Maybe (List (Fin n))
sortest-path {n} g from to = loop (Data.Vec.replicate nothing) (Data.List.map (λ x → (proj₁ x) , ([] , proj₂ x)) (outgoing-edges g from))
  where
    loop : Vec (Maybe (ℕ × List (Fin n))) n
      -> List (ℕ × List (Fin n) × Fin n) -- total cost and  from and  to,  pretend this is a priority queue, 
      -> Maybe (List (Fin n))
    loop v ls with smallest ls
    loop v ls | nothing = nothing
    loop v ls | just (n , (from , to) , ls') with Data.Vec.lookup v to
    loop v ls | just (n , (from , to) , ls') | just x = loop v ls'
    loop v ls | just (n , (from , to) , ls') | nothing = loop (Data.Vec.updateAt to (λ _ → just (n , from)) v) (Data.List.map (λ x → n + proj₁ x , to ∷ from , proj₂ x) (outgoing-edges g to) ++ ls')

    mapfst : {!!}
    mapfst = {!!}
  --  proj₁; snd to proj₂
