module SmallExamples where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _≤_; _≤?_)
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Nullary hiding (Irrelevant)

module F where
  private
    ff : ℕ -> ℕ
    ff x = x + 0
  f = ff

module F' where
  f' : ℕ -> ℕ
  f' x =  x + 0

-- Agda does not hide module definitions
pr1 : F.f ≡ F'.f'
pr1 = refl

rep : (x : ℕ) → Vec ℕ x
rep x = replicate 0 

head' : (A : Set) → (n : ℕ )→ 1 ≤ n -> Vec A n → A
head' A .(suc _) (_≤_.s≤s pr) (x ∷ v) = x

module G (more : ℕ -> ℕ)  where
  g : ℕ -> ℕ
  g x = head' ℕ (more x) what (rep (more x))
    where
      postulate
        what : 1 ≤ more x

e1 = (G.g suc) 3 -- computation is blocked by the postulate

assumegte1 : (y :  ℕ) -> 1 ≤ y
assumegte1 y with 1 ≤? y
assumegte1 y | Relation.Nullary.Dec.yes p = p
assumegte1 y | Relation.Nullary.Dec.no ¬p = {!!}

module G' (more : ℕ -> ℕ)  where
  g : ℕ -> ℕ
  g x = head' ℕ (more x) what (rep (more x))
    where
      postulate
        what' : 1 ≤ more x
        
      what : 1 ≤ more x
      what with 1 ≤? more x
      what | yes p = p
      what | no ¬p = what'
      
e1' = (G'.g suc) 3
e1'' = (G'.g λ z → z) 0


-- often used as the argument for hetergoenous equility in ITTs or (less frequently) as an argument for ETTs

assoc-+ : (x y z : ℕ) -> x + (y + z) ≡ (x + y) + z
assoc-+ zero y z = refl
assoc-+ (suc x) y z = cong suc (assoc-+ x y z)

{-
assoc-++ : {A : Set} {x y z : ℕ} -> (vx : Vec A  x) -> (vy : Vec A y) -> (vz : Vec A z) -> vx ++ (vy ++ vz) ≡ (vx ++ vy) ++ vz
assoc-++ =  ?
{- error:
x + _n_76 != x of type ℕ
when checking that the inferred type of an application
  Vec A (x + _n_76 + _n_72)
matches the expected type
  Vec A (x + (y + z))
-}
-}

open import Relation.Binary.HeterogeneousEquality

mycong :  {A : Set} (f : {n : ℕ} -> Vec A n  ->  Vec A (suc n)) {x : ℕ} {y : ℕ} {vx : Vec A x}{vy : Vec A y} -> x ≡ y ->  (vx ≅ vy) -> f vx  ≅ f vy
mycong f refl refl = refl

assoc-++ : {A : Set} {x y z : ℕ} -> (vx : Vec A  x) -> (vy : Vec A y) -> (vz : Vec A z) -> vx ++ (vy ++ vz) ≅ (vx ++ vy) ++ vz
assoc-++ [] vy vz = refl
assoc-++ {_} {suc x} {y} {z} (xx ∷ vx) vy vz = mycong (λ bod → xx ∷ bod) (assoc-+ x y z) (assoc-++ vx vy vz)
-- sould be noted that heterogenous equality is not particularly easy to use.  took me about an hour to come up with that proof
