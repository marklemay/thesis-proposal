module graph where

open import Data.Nat using (ℕ; zero; suc; _+_;  _*_; _^_; _∸_; _≤_; _≤?_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding  (_+_; _<_; _≤_; _≤?_; _-_; pred)
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
-- doesn't allow disconnrcted edges, only expensively connexted edges (some deffenitions bellow are very sensative to this)

--Path : {n : ℕ} -> Set -- TODO: at least 1 element?
--Path {n} = List (Fin n)

data Path {n :  ℕ} : Fin n -> Fin n -> Set where
  self : {v :  Fin n} -> Path v v
  hop : {x y :  Fin n} -> Path x y -> (z : Fin n) -> Path x z

-- ls-to-path : {n :  ℕ} : Fin n -> List (Fin n) ->

cost : {n : ℕ} -> {x y : Fin n} -> Path x y -> Graph {n} -> ℕ -- alternatively build cost into the calc
cost self g = 0
cost (hop {_} {from} p to) g = edge g from to + cost p g

CheapestPath : {n : ℕ} -> (x y : Fin n) ->  Path x y -> Graph {n} -> Set
CheapestPath x y p g = (other : Path x y) -> cost p g ≤ cost other g

selfbest :  {n : ℕ} -> (g : Graph {n}) -> {x : Fin n} -> CheapestPath x x (self {_} {x}) g 
selfbest  g {x} other =  _≤_.z≤n


--incbest :  {n : ℕ} -> (g : Graph {n}) -> {x : Fin n} -> CheapestPath x x (self {_} {x}) g 
--incfbest  g {x} other =  _≤_.z≤n



{-
cost : {n : ℕ} -> Path {n} -> Graph {n} -> ℕ
cost [] g = 0
cost (x ∷ []) g = 0
cost (to ∷ p@(from ∷ _)) g = edge g from to + cost p g
-}



allEdge : {n : ℕ} -> ℕ -> Graph {n}
edge (allEdge x) _ _ = x

addEdges : {n : ℕ} -> (Fin n -> Fin n -> Maybe  ℕ) -> Graph {n} -> Graph {n}
edge (addEdges f g) from to with f from to
edge (addEdges f g) from to | just x = x
edge (addEdges f g) from to | nothing = edge g from to 

diagEdges : {n : ℕ} -> ℕ -> (Fin n -> Fin n -> Maybe  ℕ)
diagEdges w from to  with Data.Fin._≟_ from to
diagEdges w from to | Relation.Nullary.yes p = just w
diagEdges w from to | Relation.Nullary.no ¬p = nothing

{-
0 -3> 8
|        |
1      3
v      v
1
|
1
v
2
.
.
.
7 -1>9
-}
ex1 : (Fin 10 -> Fin 10 -> Maybe  ℕ) 
ex1 0F 1F = just 1
ex1 1F 2F = just 1
ex1 2F 3F = just 1
ex1 3F 4F = just 1
ex1 4F 5F = just 1
ex1 5F 6F = just 1
ex1 6F 7F = just 1
ex1 7F 9F = just 1
ex1 0F 8F = just 3
ex1 8F 9F = just 3
ex1 _ _ = nothing

gex : Graph {10}
gex = addEdges (diagEdges 0) (addEdges ex1 (allEdge 9))

-- TODO: better ways to run these checks?
ee = edge  (allEdge {10} 9) 3F 3F

ee0 = edge  gex 3F 3F
ee1 = edge  gex 0F 9F
ee2 = edge  gex 0F 8F

epath : Path {10} 0F 9F
epath = hop (hop (hop self 0F) 8F) 9F

-- need some bounding lemas to be workable





ebest : CheapestPath 0F 9F epath gex
ebest other = {!!}


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
outgoing-edges {n} g from = Data.List.filter (λ x → 1 ≤? proj₁ x) (toList (map (λ to → (edge g from to) , to) (allFin n))) -- TODO: relax 0 ede weighting

-- dijkstra's algorithm
{-
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
-}

loop' : {n : ℕ} -> Graph {n} -> (from : Fin n) -> (to : Fin n) -> Vec (Maybe (ℕ × List (Fin n))) n -> List (ℕ × List (Fin n) × Fin n) -> Maybe ((Vec (Maybe (ℕ × List (Fin n))) n)  × List (Σ ℕ (λ _ → Σ (List (Fin n)) (λ _ → Fin n))) )
loop' {n} g from to v ls with smallest ls
loop' {n} g from to v ls | nothing = nothing
loop' {n} g _ _ v ls | just (cost , (from , to) , ls') with Data.Vec.lookup v to
loop' {n} g from to v ls | just (cost , (_ , _) , ls') | just x = loop' g from to v ls'
loop' {n} g from to v ls | just (cost , (path , to') , ls') | nothing = just ((updateAt to' (λ _ → just (cost , path) ) v) ,
  Data.List.map (λ x → (cost + proj₁ x) , (to' ∷ path , proj₂ x) ) (outgoing-edges g to' ) ++ ls' )

-- {!(Data.Vec.updateAt to' (λ _ → just (n , from')) v) (Data.List.map (λ x → n + proj₁ x , to' ∷ from' , proj₂ x) (outgoing-edges g to') ++ ls')!}
{-
loop' {n} g from to v ls | just (n , (from , to) , ls') with Data.Vec.lookup v to
loop' {n} g from to v ls | just (n , (from , to) , ls') | just x = loop' v ls'
loop' {n} g from to v ls | just (n , (from , to) , ls') | nothing = just (Data.Vec.updateAt to (λ _ → just (n , from)) v) (Data.List.map (λ x → n + proj₁ x , to ∷ from , proj₂ x) (outgoing-edges g to) ++ ls')
-}

{-
eee = sortest-path gex 0F 0F
eee1 = outgoing-edges gex  0F  -- (0 , 0F) ∷ (1 , 1F) ∷ (9 , 2F) ∷ (9 , 3F) ∷ (9 , 4F) ∷ (9 , 5F) ∷ (9 , 6F) ∷ (9 , 7F) ∷ (3 , 8F) ∷ (9 , 9F) ∷ []
eee2 = smallest eee1 
-}
{-
eeee1 : List (ℕ × List (Fin 10) × Fin 10)
eeee1 = (Data.List.map (λ x → (proj₁ x) , ([] , proj₂ x)) (outgoing-edges gex 0F))
-}
isJust : {A : Set} -> Maybe A -> A
isJust (just x) = x

pred : ℕ  -> ℕ
pred 0 = 0
pred (suc x) = x


step : ℕ -> Σ (Vec (Maybe (Σ ℕ (λ _ → List (Fin 10)))) 10)
              (λ _ → List (Σ ℕ (λ _ → Σ (List (Fin 10)) (λ _ → Fin 10))))
step 0 = isJust ( loop' gex 0F 9F (Data.Vec.updateAt 0F (λ _ → just (0 ,  []))  (Data.Vec.replicate nothing)) (Data.List.map (λ x → (proj₁ x) , (0F ∷ [] , proj₂ x)) (outgoing-edges gex 0F)))
step x = let (v , ls) = (step (pred x)) in isJust (loop' gex 0F 9F v ls)
