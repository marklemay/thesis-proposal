module graph where

-- googling seems to indicate that there is no formalization of maz-flow min-cut / Ford–Fulkerson in agda

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _≤_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding  (_+_; _<_; _≤_)
open import Data.Bool hiding  (_<_; _≤_)
open import Data.Vec

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


record ss {n : ℕ} : Set where
  field
     source : Fin n
     sink : Fin n
     pr : ¬ source ≡ sink
open ss

record Flow {n : ℕ} (full : Graph {n}) (s : ss {n}) (vol : ℕ) : Set where
  field
    flow : Graph{n}
    local-plow-ok : (node : Fin n)
      -> ¬ source s ≡ node -> ¬ sink s ≡ node
      -> incoming-flow flow node ≡ outgoing-flow flow node
    bounded : (from : Fin n) -> (to : Fin n) -> edge flow from to ≤ edge full from to
  
noFlow : {n : ℕ} (full : Graph {n}) -> (s : ss {n}) -> Flow full s 0
edge (Flow.flow (noFlow full s)) from to = 0
Flow.local-plow-ok (noFlow full s) node x x₁ = {!!} -- TODO: a suprisingly hard fact to prove
Flow.bounded (noFlow full s) from to = {!!} -- TODO: easy to prove

--open import Relation.Binary.Reasoning.PartialOrder -- a little too heavy

open import Data.Product -- using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
MaxFlow : {n : ℕ} (full : Graph {n}) -> (s : ss {n}) -> Set
MaxFlow g ss = Σ  ℕ λ n → Flow g ss n × ((n' : ℕ) -> n ≤ n' -> ¬ Flow g ss n')


open import Data.List
open import Data.Maybe

-- represent path as a flow
-- path : {n : ℕ} (full : Graph {n}) (s : ss {n}) -> 

remaining-flow : {n : ℕ} (full : Graph {n}) (s : ss {n}) -> (vol : ℕ) -> Flow full s vol -> Σ ℕ λ x → Flow full s x -- actually needs more constraints
remaining-flow = {!!}

-- no correctness proof

{-
get-path :  {n : ℕ} (full : Graph {n}) -> (start : Fin n) -> (end : Fin n) -> ℕ × List (Fin n)
get-path = {!!}

ford–fulkerson : {n : ℕ} (full : Graph {n}) -> (s : ss {n}) -> Graph {n}
ford–fulkerson = {!!}
-}
-- concrete attack. def min flow/max cut, implement ford f algorithm


{-

-- a naive directed multigraph

data Graph {n : ℕ} : Set where
  disconnected : Graph
  edge : (from : Fin n) -> (to : Fin n) -> Graph {n} -> Graph -- technically allows a multigraph

data Connected {n : ℕ} (g : Graph {n}) : Fin n -> Fin n -> Set where
  by-self : {x : Fin n} -> Connected g x x
  by-path : {x y : Fin n} -> Connected g x x
 
mVerts : {n m : ℕ} -> (Fin n -> Fin m) -> Graph {n} -> Graph {m}
mVerts m disconnected = disconnected
mVerts m (edge from to g) = edge (m from) (m to) (mVerts m g)

-- mVerts id = id, associative

diag : (n : ℕ) -> Graph {n}
diag 0F = disconnected
diag (suc n) = edge ( # 0 ) (# 0) (mVerts (raise 1F) (diag n))

-- g-from-func : {n : ℕ} -> (Fin n -> Fin n -> )

---clique

-}

  


