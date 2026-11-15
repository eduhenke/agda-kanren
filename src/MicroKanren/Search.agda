{-# OPTIONS --safe --guardedness #-}

-- Running a tree: one step, the stream of answers, and reading answers back.

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality as Eq
  using (refl; sym; _≡_; cong; cong₂; trans)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Product using (∃; _,_; Σ-syntax; proj₁; _×_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Vec using (Vec; []; _∷_; tabulate)

module MicroKanren.Search (A : Set) (A⟨_≟_⟩ : DecidableEquality A) where

open import Unification.Properties A A⟨_≟_⟩ hiding (_∧_; _∈_)
open import MicroKanren.State A A⟨_≟_⟩
open import MicroKanren.Stream
open import MicroKanren.Goal A A⟨_≟_⟩
open import MicroKanren.Tree A A⟨_≟_⟩

private variable
  l m n c c′ c″ k : ℕ
  R S : Set
  θ : Subst c m
  t u : Term c

data Prefix (c : ℕ) : Set where
  finished : List (Answer c) → Prefix c
  paused   : List (Answer c) → Tree c → Prefix c

prepend : List (Answer c) → Prefix c → Prefix c
prepend as (finished bs) = finished (as ++ bs)
prepend as (paused bs t) = paused (as ++ bs) t

bindTree : List (Answer c) → (Answer c → Tree c) → Tree c → Tree c
bindTree []       k e = e
bindTree (a ∷ as) k e = choice (k a) (bindTree as k e)

laterBind : Tree c → (Answer c → Tree c) → ∞Tree c
laterBind x k .force = bind x k

mutual
  next : Tree c → Prefix c
  next fail      = finished []
  next (leaf a)  = finished (a ∷ [])
  next (delay t) = paused [] (t .force)

  next (choice x y) with next x
  ... | finished as  = prepend as (next y)
  ... | paused as x′ = paused as (choice y x′)

  next (within q x) with next x
  ... | finished as  = finished (map (extend q) as)
  ... | paused as x′ = paused (map (extend q) as) (within q x′)

  next (bind x k) with next x
  ... | finished as  = nextBind as k fail (finished [])
  ... | paused as x′ = nextBind as k (delay (laterBind x′ k)) (paused [] (bind x′ k))

  nextBind : List (Answer c) → (Answer c → Tree c) → Tree c → Prefix c → Prefix c
  nextBind []       k e em = em
  nextBind (a ∷ as) k e em with next (k a)
  ... | finished bs = prepend bs (nextBind as k e em)
  ... | paused bs t = paused bs (choice (bindTree as k e) t)

mutual
  search : Tree c → Stream (Answer c)
  search t .step = stepOf (next t)

  resume : Prefix c → Stream (Answer c)
  resume mv .step = stepOf mv

  stepOf : Prefix c → Step (Answer c)
  stepOf (finished [])       = fail
  stepOf (finished (a ∷ as)) = yield a (resume (finished as))
  stepOf (paused [] t)       = later (search t)
  stepOf (paused (a ∷ as) t) = yield a (resume (paused as t))

-- The step of a bind is the step of its tree of choices.
bindTree-next : ∀ as (k : Answer c → Tree c) e → nextBind as k e (next e) ≡ next (bindTree as k e)
bindTree-next []       k e = refl
bindTree-next (a ∷ as) k e with next (k a)
... | finished bs = cong (prepend bs) (bindTree-next as k e)
... | paused bs t = refl

tree : Goal c → Tree c
tree g = ⟦ g ⟧ id (mkState ε)

run : Goal c → Stream (Answer c)
run g = search (tree g)

reify : Answer c → Term c → ∃ Term
reify (answer q (mkState {k} σ)) t = k , apply (sub σ) (wk q t)

Solution : ℕ → Set
Solution c = ∃ λ k → Vec (Term k) c

solution : Answer c → Solution c
solution (answer q (mkState {k} σ)) = k , tabulate (λ x → apply (sub σ) (wk q (var x)))
