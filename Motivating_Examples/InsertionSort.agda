module InsertionSort where

open import Data.Nat
open import Data.List
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)


ee = 5 ≤? 7

ee2 = 7 ≤? 2

-- ee3 = <-cmp 3 5


min : ℕ -> ℕ -> ℕ × ℕ
min 0 y = ⟨ 0 , y ⟩
min x 0 = ⟨ 0 , x ⟩
min (suc x) (suc y) with min x y
min (suc x) (suc y) | ⟨ fst , snd ⟩ = ⟨ (suc fst) , (suc snd) ⟩

-- insert an element into a sorted list
insert : ℕ  -> List ℕ  -> List ℕ
insert x [] =  x ∷ []
insert x (head ∷ ls) with min x head
insert x (head ∷ ls) | ⟨ fst , snd ⟩ = fst  ∷  insert snd ls

sort : List ℕ  -> List ℕ
sort [] = []
sort (x ∷ ls) = insert x (sort ls)

ex = sort (6 ∷ 6 ∷ 2 ∷ 7 ∷ 0 ∷ 1 ∷ [])

data lBound (n :  ℕ)  : List  ℕ -> Set where
  nil-lBound : lBound n []
  cons-lBound : (m : ℕ) -> (rest : List ℕ)  -> n ≤ m -> lBound  n rest -> lBound n (m  ∷  rest)


data Sorted : (List ℕ) -> Set where
  nil-Sorted : Sorted []
  cons-Sorted : (m : ℕ) -> (rest : List ℕ)  -> (Sorted rest) -> lBound m rest -> Sorted (m  ∷ rest)




insert' : (n : ℕ) -> (ls : List ℕ) -> Sorted ls ->
  {- would expect to be able to return
  Σ ( List ℕ) Sorted
  -- but instead a stronger invairent is needed 
  -}
  Σ (List ℕ) (\ ls' -> (Sorted ls')  × ( (x : ℕ) -> x ≤ n -> lBound x ls -> lBound x ls'))
insert' = {!!}

sort' :  (ls : List ℕ) ->  Σ ( List ℕ) Sorted
sort' = {!!}
