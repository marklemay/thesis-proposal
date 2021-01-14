module Arith where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)

postulate Solve : (a : Set) -> a

data Nat : Set where
  z : Nat
  s : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

add : Nat -> Nat -> Nat
add z y = y
add (s x) y = s (add x y)

mult : Nat -> Nat -> Nat
mult z y = z
mult (s x) y = add y (mult x y)

sub  :  (x : Nat) -> (y : Nat) ->  Σ Nat λ ans → add x ans ≡ y 
sub z y = ⟨ y , refl ⟩
sub (s x) (s y) with sub x y
sub (s x) (s .(add x fst)) | ⟨ fst , refl ⟩ = ⟨ fst , refl ⟩
sub (s x) z = {!!}

ex1 = sub 3 10

-- "correct by assumption"


--or as relations

data ADD : Nat -> Nat -> Nat -> Set where
  ADD-Base : (y : Nat) -> ADD z y y
  ADD-step : (a b c : Nat) -> ADD a b c -> ADD (s a) b (s c)

exADD : Σ Nat λ x → ADD 3 x 5
exADD = ⟨ 2 , ADD-step 2 2 4 (ADD-step 1 2 3 (ADD-step z 2 2 (ADD-Base 2)))
          ⟩ -- defualt agda is able  to solve

exADD' : Σ Nat λ x → ADD 10 x 15
exADD' = ⟨ 5 ,
           ADD-step 9 5 14
           (ADD-step 8 5 13
            (ADD-step 7 5 12
             (ADD-step 6 5 11
              (ADD-step 5 5 10
               (ADD-step 4 5 9
                (ADD-step 3 5 8
                 (ADD-step 2 5 7
                  (ADD-step 1 5 6 (ADD-step z 5 5 (ADD-Base 5))))))))))
           ⟩ -- defualt agda is able  to solve

exADD'1 : Σ Nat λ x → ADD 30 x 50
exADD'1 = {!!} -- defualt agda is unable to solve

add' : (x : Nat) -> (y : Nat) ->  Σ Nat λ ans → ADD x y ans
add' z y = ⟨ y , ADD-Base y ⟩
add' (s x) y with add' x y
add' (s x) y | ⟨ fst , snd ⟩ = ⟨ s fst , ADD-step x y fst snd ⟩

sub' :  (x : Nat) -> (y : Nat) ->  Σ Nat λ ans → ADD x ans y -- not total, but useful
sub' z y = ⟨ y , ADD-Base y ⟩
sub' (s x) (s y) with sub' x y
sub' (s x) (s y) | ⟨ fst , snd ⟩ = ⟨ fst , ADD-step x fst y snd ⟩
sub' (s x) z = {!!}

ex11 = sub' 3 10
