module graph2 where

open import Data.Nat -- using (ℕ; zero; suc; _+_;  _*_; _^_; _∸_; _≤_; _≤?_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding  (_+_; _<_; _≤_; _≤?_; _-_; pred)
open import Data.Bool hiding  (_<_; _≤_; _≤?_)
--open import Data.Vec hiding (_++_)
open import Data.List --  hiding (sum; map; allFin)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.All hiding (self)
open import Data.List.Relation.Unary.All.Properties
open import Data.Maybe  hiding (map)
open import Data.Product hiding (map)
open import Data.Sum  hiding (map)
open import Data.Bool using (Bool; true)
open import Relation.Nullary using (¬_)
open import Data.Empty


record Selection {A : Set} (a : A) (ls' : List A) (ls : List A) : Set where
  field
    a∈ls :  a ∈  ls
    ls'<ls :  {a' : A} -> (a' ∈  ls') -> a' ∈  ls
    ls<a+ls' :  {a' : A} -> (a' ∈  ls) -> a' ∈  ls' ⊎ a' ≡ a

-- in std lib somewhere?
_∈?_ : {n : ℕ} (v : Fin n) (ls : List (Fin n)) -> Relation.Nullary.Dec (v ∈  ls)
v ∈? ls = {!!}

-- possibly better as a permutation?

record Graph {n : ℕ} : Set  where
  field
 --   Edge : (from : Fin n) -> (to : Fin n) -> Set
    edge : (from : Fin n) -> (to : Fin n) -> Bool --  Relation.Nullary.Dec (Edge from to)
open Graph

module Paths {n :  ℕ} (g : Graph {n}) where
  V = Fin n
  edg = edge g

  Con : (x y : V) -> Set
  Con x y = T (edg x y)

  data Path : Fin n -> Fin n -> Set where
    self : (v :  Fin n) -> Path v v
    hop : {x y :  Fin n} -> Path x y -> (z : Fin n) -> T (edg y z) -> Path x z

  _+++_ : {x y z : Fin n} -> Path x y -> Path y z -> Path x z
  _+++_ = {!!}

  cost : {x y : Fin n} -> Path  x y -> ℕ
  cost (self _) = 0
  cost (hop p _  _) = 1 + cost p

  CheapestPath : {x y : Fin n} ->  Path x y -> Set
  CheapestPath {x} {y} p = (other : Path x y) -> cost p ≤ cost other

--  selfCheapest

  directC : (from : Fin n) -> (to : Fin n) -> ¬ from ≡ to -> (e : T (edg from to)) -> CheapestPath  (hop (self from) to e) 
  directC from .from x e (self .from) = ⊥-elim (x refl)
  directC from to x e (hop other .to x₁) = s≤s z≤n

  record Visited (start : V) (bound :  ℕ) : Set where
    constructor mkVisited
    field
      nodes : List V
      nodesAreBest : (to : V) -> to ∈ nodes -> Σ (Path start to) (λ p → cost p ≤ bound × CheapestPath p)
      otherNodesWorse : (to : V) -> ¬ to ∈ nodes -> (p : Path start to) -> bound ≤  cost p


  record Candidates (start : V) (bound :  ℕ) : Set where
    open Visited
    field
      vis : Visited start bound --or index by?
    
      candidates : List (ℕ × V × V) -- TODO: pehaps hold the full path? still pretend this is a priority queue
      wf : (c : ℕ) (from to : V) -> (c , from , to) ∈ candidates ->
        Σ (T (edg from to)) \ isE ->
        Σ  (from ∈ nodes vis) \ con ->
        c ≡ cost (hop (proj₁ (nodesAreBest vis from con)) to isE )   -- better with All
      
      complete : (c : ℕ)(from to : V) ->  from ∈ nodes vis -> T (edg from to) -> ¬ (c , from , to) ∈ candidates -> to ∈ nodes vis
    --   all other edges don't go anywhere intresting


  best : {start : V} {bound :  ℕ}
    -> (can : Candidates start bound)
    -> Visited start bound
    ⊎ (Σ (ℕ × V × V)  λ pair → Σ (List (ℕ × V × V)) λ rest  → Selection pair rest (Candidates.candidates can) -- more consice if Selection contained the data?
       × All (λ x → proj₁ pair  ≤ proj₁ x) rest ) 
  best = {!!}

  record Edges (from : V) : Set where
    field
      edges : List V
      connected : All (Con from) edges 
      complete : (to : V) -> Con from to -> to ∈ edges 

  getEdges : (from : V) -> Edges from
  getEdges = {!!}

  dstep : (start : V) (bound :  ℕ)
    -> Candidates start bound
    -> Visited start bound ⊎ Σ ℕ λ bound' → Candidates start bound' -- more conditions?
  dstep start bound can with best can
  dstep start bound can | inj₁ visited = inj₁ visited
  dstep start bound can | inj₂ (pair@(cost , from , to) , y) with to ∈? Visited.nodes (Candidates.vis can)
  -- throw away
  dstep start bound can | inj₂ ((cost , from , to) , rest , sel , restbound) | Relation.Nullary.yes p =
    inj₂ (cost ,
    record { vis = mkVisited (Visited.nodes (Candidates.vis can)) {!!} {!!} ; candidates = rest ; wf = {!!} ; complete = {!!} })
  dstep start bound can | inj₂ ((cost , from , to) , y) | Relation.Nullary.no ¬p with getEdges to
  dstep start bound can | inj₂ ((cost , from , to) , rest , sel , restbound) | Relation.Nullary.no ¬p | record { edges = tos ; connected = connected ; complete = complete } =
    let bestTo = ? in
    inj₂ (cost ,
      record { vis = mkVisited (to ∷ Visited.nodes (Candidates.vis can)) {!!} {!!} ; candidates = Data.List.map (λ dest → 1 + cost , (to , dest)) tos ++ rest ; wf = {!!} ; complete = {!!} }) 
{-

    -- don't need best explicitly if baking in a list imp

-}
{-

--cost satisfy a triange ineq

CheapestPath : {n : ℕ} {g : Graph {n}} -> (x y : Fin n) ->  Path {n} {g} x y -> Set
CheapestPath {n} {g} x y p = (other : Path {n} {g} x y) -> cost p ≤ cost other




outE : {n : ℕ} {g : Graph {n}} -> (from : Fin n) -> (Σ (List (Fin n))
  λ ls → (to : Fin n) -> (p : Path {n} {g} from to) -> Σ (Fin n) λ init → Σ (Path {n} {g} init to) λ rest → init ∈ ls  × (hop (self from) init {!!} +++ rest)  ≡ p )
 -- or the list is complete in the sense it contains every outgoing edge
outE = {!!}
-}
