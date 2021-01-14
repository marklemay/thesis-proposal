module lambConf where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app)
open Eq.≡-Reasoning using (_≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.Fin
open import Data.Product 


-- taking heavy insterpation from https://plfa.github.io/Untyped/
-- Note that the presentation there postulates a number of properties

-- scoped term
data Exp (n : ℕ) : Set where
  Var : Fin n -> Exp n
  App : Exp n -> Exp n -> Exp n
  Lam : Exp (suc n) -> Exp n

ext : ∀ {x y} → (Fin x -> Fin y) 
  → Fin (suc x) → Fin (suc y)
ext ρ 0F = 0F
ext ρ (suc x) = suc (ρ x)
-- suprisinly not in std lib

rename :  ∀ {x y} → (Fin x -> Fin y)
  → Exp x -> Exp y
rename ρ (Var x) = Var (ρ x)
rename ρ (App f a) = App (rename ρ f) (rename ρ a)
rename ρ (Lam bod) = Lam (rename (ext ρ) bod) 

-- simultanous substitution
exts :  ∀ {x y} → (Fin x -> Exp y)
  → Fin (suc x) → Exp (suc y)
exts σ 0F = Var 0F
exts σ (suc x) = rename suc (σ x)

subst : ∀ {x y} → (Fin x -> Exp y)
  → Exp x → Exp y
subst σ (Var x) = σ x
subst σ (App f a) = App (subst σ f) (subst σ a)
subst σ (Lam bod) = Lam (subst (exts σ) bod)

-- would probly want to prove some properties of rename and subst such that it forms a category.  Since other functions at these tyoes are possible (and what will happen if agda autocompletes)

-- Though these facts are "unproductive" to prove
rename-id : ∀ {x} → Fin x -> Fin x
rename-id x = x

rename-id-ok : ∀ {x} → (e : Exp x) ->  rename rename-id e ≡ e
rename-id-ok {x} (Var x₁) = refl
rename-id-ok {x} (App f a) with (rename-id-ok f , rename-id-ok a)
rename-id-ok {x} (App f a) | fst , snd = {! !}
rename-id-ok {x} (Lam bod) = {!!}

-- rename-comp, rename-comp-ok

subst-id : ∀ {x} →  Fin x -> Exp x
subst-id x = Var x

--, subst-id-ok, subst-comp, subst-comp-ok, 

-- shorthand for single subst
subst-zero : ∀ {x} → (Exp x) →  Fin (suc x) → (Exp x) 
subst-zero x 0F = x
subst-zero x (suc y) = Var y

_[_] : ∀ {x}
        → Exp (suc x)
        → Exp x
        → Exp x
_[_]  N M =  subst (subst-zero  M) N



-- one-step reduction
infix 2 _—→_

data _—→_ {x : ℕ} : Exp x →  Exp x → Set where

  β :  {N : Exp (suc x) } {M : Exp x}
    → App (Lam N) M —→ N [ M ] -- note, this willcomputation apearing in a type index will cause no end of pain

  ζ : ∀ {N N′ : Exp (suc x) }
    → N —→ N′
    → Lam N —→ Lam N′
    
  ξ₁ :  {L L′ M : Exp x} → L —→ L′
    → App L  M —→ App L′ M

  ξ₂ : {L M′ M : Exp x} → M —→ M′
    → App L M —→ App L M′

infix  2 _—↠_
infixr 2 _—→⟨_⟩_ --  ? —→⟨ ? ⟩ ?
infix  3 _!

data _—↠_ {x : ℕ} : Exp x →  Exp x → Set where
  _! :  (M : Exp x)
    → M —↠ M
 
  _—→⟨_⟩_ :  (L : Exp x) {M N : Exp x} → L —→ M → M —↠ N
    → L —↠ N

--TODO —↠-trans https://plfa.github.io/Untyped/#multi-step-reduction-is-transitive

infixr 2 _—↠⟨_⟩_
_—↠⟨_⟩_ : ∀ {x} → (L : Exp x) {M N : Exp x} → L —↠ M → M —↠ N
    → L —↠ N
L —↠⟨ .L ! ⟩ MN = MN
L —↠⟨ .L —→⟨ x ⟩ LM ⟩ MN = L —→⟨ x ⟩ ({!?!} —↠⟨ LM ⟩ MN)


--TODO https://plfa.github.io/Untyped/#multi-step-reduction-is-a-congruence

appL-cong :  ∀{x} {L L' M : Exp x } → L —↠ L'
         → App L M —↠ App L' M
appL-cong {x} {.M₁} {.M₁} {M} (M₁ !) = App M₁ M !
appL-cong {x} {L} {L'} {M} (L —→⟨ x₁ ⟩ xx) = App L M —→⟨ ξ₁ x₁ ⟩ appL-cong xx

appR-cong :  ∀{x} {L M M' : Exp x } → M —↠ M'
         → App L M —↠ App L M'
appR-cong {x} {L} {M} {.M} (M !) = App L M !
appR-cong {x} {L} {.L₁} {M'} (L₁ —→⟨ x₁ ⟩ xx) = App L L₁ —→⟨ ξ₂ x₁ ⟩ appR-cong xx



abs-cong : ∀{x} {N N' : Exp (suc x) } → N —↠ N'
         → Lam N —↠ Lam N'
abs-cong (M !) = Lam M !
abs-cong (L —→⟨ x ⟩ x₁) = Lam L —→⟨ ζ x ⟩ abs-cong x₁ 


idTerm :  {x : ℕ} → Exp x 
idTerm =  Lam (Var (# 0)) 

churchTrueTerm :  {x : ℕ} → Exp x 
churchTrueTerm =  Lam (Lam (Var (# 1)) )

redex : {x : ℕ} -> (_—↠_) {x} (App churchTrueTerm idTerm) (Lam (Lam (Var 0F)))
redex = App (Lam (Lam (Var 1F))) (Lam (Var 0F)) —→⟨ β ⟩ Lam (Lam (Var 0F)) !



infix 2 _⇛_

data _⇛_ {x : ℕ} :  (Exp x) → (Exp x) → Set where

  pvar : {v : Fin x}
    → (Var v) ⇛ (Var v)

  pabs : {N N′ : Exp (suc x)} → N ⇛ N′
    → Lam N ⇛ Lam N′

  papp : {L L′ M M′ : Exp x} → L ⇛ L′ → M ⇛ M′
    → App L M ⇛ App L′ M′

  pbeta : {N N′  : Exp (suc x) }{ M M′ : Exp x} → N ⇛ N′ → M ⇛ M′
   → App (Lam N) M  ⇛  N′ [ M′ ]

par-refl : ∀{x}{M : Exp x} → M ⇛ M
par-refl {x} {Var x₁} = pvar
par-refl {x} {App M M₁} = papp par-refl par-refl
par-refl {x} {Lam M} = pabs par-refl


infix  2 _⇛*_
infixr 2 _⇛⟨_⟩_
infix  3 _!!

data _⇛*_ {x : ℕ} : (Exp x) → (Exp x) → Set where

  _!! : (M : Exp x)
    → M ⇛* M

  _⇛⟨_⟩_ : (L : Exp x) {M N : Exp x} → L ⇛ M → M ⇛* N
    → L ⇛* N
    
-- ? ⇛⟨ ? ⟩ ?

beta-par :  ∀{x}{M N : Exp x}  → M —→ N
  → M ⇛ N
beta-par {x} {App M M₁} (ξ₁ tt) = papp (beta-par tt) par-refl
beta-par {x} {App M M₁}  (ξ₂ tt) = papp par-refl (beta-par tt)
beta-par {x} {App (Lam N) M}  β = pbeta par-refl par-refl
beta-par {x} {Lam M}  (ζ tt) = pabs (beta-par tt)

betas-pars : ∀{x}{M N : Exp x} → M —↠ N
  → M ⇛* N
betas-pars (M !) = M !!
betas-pars (L —→⟨ x ⟩ M) = L ⇛⟨ beta-par x ⟩ betas-pars M

par-betas :  ∀{x}{M N : Exp x} → M ⇛ N
  → M —↠ N
par-betas {x} {(Var v)} pvar = Var v !
par-betas {x} {(Lam _N)}  (pabs xx) = abs-cong (par-betas xx)
par-betas {x} {(App L M)} (papp {_} {L'}{M}{M'} xx yy) =
  App L M —↠⟨ appL-cong (par-betas xx) ⟩
  App L' M —↠⟨ appR-cong (par-betas yy) ⟩ App L' M' !
par-betas {x} {(App (Lam N) M)}  (pbeta {_} {N'} {_} {M'} xx yy) =
  App (Lam N) M —↠⟨ appL-cong (abs-cong (par-betas xx)) ⟩
  App (Lam N') M —↠⟨ appR-cong (par-betas yy) ⟩
  App (Lam N') M' —→⟨ β ⟩
  subst (subst-zero M') N' ! 


pars-betas : ∀{x}{M N : Exp x} → M ⇛* N
  → M —↠ N
pars-betas (M !!) = M !
pars-betas (L ⇛⟨ x ⟩ N) = L —↠⟨ par-betas x  ⟩ pars-betas N

-- Substitution lemma for parallel reduction

Rename : ℕ → ℕ → Set
Rename Γ Δ = Fin Γ → Fin Δ

Subst : ℕ → ℕ → Set
Subst Γ Δ = Fin Γ → Exp Δ

par-subst : ∀{Γ Δ} → Subst Γ Δ → Subst Γ Δ → Set
par-subst {Γ}{Δ} σ σ′ = ∀{x : Fin Γ} → σ x ⇛ σ′ x

rename-subst-commute : ∀{Γ Δ}{N : Exp (suc Γ)}{M : Exp Γ}{ρ : Rename Γ Δ }
    → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute {Γ} {Δ} {N} {M} {ρ} = {!!} --plfa.part2.Substitution.rename-subst-commute

par-confluence : ∀{Γ} {L M₁ M₂ : Exp Γ} → L ⇛* M₁ → L ⇛* M₂
  → Σ (Exp Γ)  λ N → (M₁ ⇛* N) × (M₂ ⇛* N) 
par-confluence = {!!}

-- ? —↠⟨ ? ⟩ ?
confluence : ∀{Γ} {L M₁ M₂ : Exp Γ} → L —↠ M₁ → L —↠ M₂
  → Σ (Exp  Γ) λ N → (M₁ —↠ N)  ×  (M₂ —↠ N) -- [ N ∈ Γ ⊢ A ] (M₁ —↠ N) × (M₂ —↠ N)
confluence L↠M₁ L↠M₂ with par-confluence (betas-pars L↠M₁) (betas-pars L↠M₂)
... | xx = {!!}

