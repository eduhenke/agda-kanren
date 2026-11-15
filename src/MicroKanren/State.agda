{-# OPTIONS --safe --guardedness #-}

-- Search states, scope extensions and answers.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality as Eq
  using (refl; sym; _≡_; cong; cong₂; trans)
open import Relation.Binary.Definitions using (DecidableEquality)

module MicroKanren.State (A : Set) (A⟨_≟_⟩ : DecidableEquality A) where

open import Unification.Properties A A⟨_≟_⟩ hiding (_∧_; _∈_)

private variable
  l m n c c′ c″ k : ℕ
  R S : Set
  θ : Subst c m
  t u : Term c

record State (c : ℕ) : Set where
  constructor mkState
  field
    {vars} : ℕ
    σ : AList c vars

data _⊑_ : ℕ → ℕ → Set where
  id   : n ⊑ n
  keep : m ⊑ n → suc m ⊑ suc n
  skip : m ⊑ n → m ⊑ suc n

infixr 9 _∙_

ren : m ⊑ n → Fin m → Fin n
_∙_ : l ⊑ m → m ⊑ n → l ⊑ n

ren id       x       = x
ren (keep p) zero    = zero
ren (keep p) (suc x) = suc (ren p x)
ren (skip p) x       = suc (ren p x)

rename : (Fin m → Fin n) → Term m → Term n
rename f (var x)      = var (f x)
rename f (val a)      = val a
rename f ⟨ t₁ , t₂ ⟩ = ⟨ rename f t₁ , rename f t₂ ⟩

p      ∙ id     = p
p      ∙ skip q = skip (p ∙ q)
id     ∙ keep q = keep q
keep p ∙ keep q = keep (p ∙ q)
skip p ∙ keep q = skip (p ∙ q)

ren-∙ : ∀ (p : l ⊑ m) (q : m ⊑ n) x → ren (p ∙ q) x ≡ ren q (ren p x)
ren-∙ p        id       x       = refl
ren-∙ p        (skip q) x       = cong suc (ren-∙ p q x)
ren-∙ id       (keep q) x       = refl
ren-∙ (keep p) (keep q) zero    = refl
ren-∙ (keep p) (keep q) (suc x) = cong suc (ren-∙ p q x)
ren-∙ (skip p) (keep q) x       = cong suc (ren-∙ p q x)

wk : m ⊑ n → Term m → Term n
↑  : Term c → Term (suc c)

wk id         t = t
wk p@(keep _) t = rename (ren p) t
wk p@(skip _) t = rename (ren p) t

wk-var : ∀ (p : m ⊑ n) x → wk p (var x) ≡ var (ren p x)
wk-var id       x = refl
wk-var (keep p) x = refl
wk-var (skip p) x = refl

wk-val : ∀ (p : m ⊑ n) a → wk p (val a) ≡ val a
wk-val id       a = refl
wk-val (keep p) a = refl
wk-val (skip p) a = refl

↑ = wk (skip id)

record Answer (c : ℕ) : Set where
  constructor answer
  field
    {scope′} : ℕ
    ext      : c ⊑ scope′
    state    : State scope′

open Answer public

extend : c ⊑ c′ → Answer c′ → Answer c
extend p (answer q s) = answer (p ∙ q) s
