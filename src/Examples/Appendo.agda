{-# OPTIONS --safe --guardedness #-}

-- List concatenation as a relation, run in several directions.

module Examples.Appendo where

open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Vec using ([]; _∷_)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)

open import Unification.Properties ℕ _≟_ hiding (_∧_; _∈_)
open import MicroKanren ℕ _≟_
open import MicroKanren.Binders ℕ _≟_ using (↑³; fresh₃)
open import MicroKanren.Finite ℕ _≟_ using (ends-complete)

private variable
  c : ℕ

nil : Term c
nil = val 0

appendo : Term c → Term c → Term c → Goal c
appendo l r out =
    (l ≐ nil ∧ r ≐ out)
  ∨ fresh₃ λ a d res →
      ↑³ l ≐ ⟨ a , d ⟩ ∧ ↑³ out ≐ ⟨ a , res ⟩
    ∧ delay λ where .force → appendo d (↑³ r) res

split-goal : Goal 2
split-goal = appendo (var 0F) (var 1F) ⟨ val 1 , ⟨ val 2 , nil ⟩ ⟩

splits : Run (next (tree split-goal))
splits = (0 , nil ∷ ⟨ val 1 , ⟨ val 2 , nil ⟩ ⟩ ∷ []) ∷ []
       ⟶ (0 , ⟨ val 1 , nil ⟩ ∷ ⟨ val 2 , nil ⟩ ∷ []) ∷ []
       ⟶ (0 , ⟨ val 1 , ⟨ val 2 , nil ⟩ ⟩ ∷ nil ∷ []) ∷ []
       ∎

forward-goal : Goal 1
forward-goal = appendo ⟨ val 1 , ⟨ val 2 , nil ⟩ ⟩ ⟨ val 1 , ⟨ val 2 , nil ⟩ ⟩ (var 0F)

forward : Run (next (tree forward-goal))
forward = [] ⟶ []
        ⟶ (0 , ⟨ val 1 , ⟨ val 2 , ⟨ val 1 , ⟨ val 2 , nil ⟩ ⟩ ⟩ ⟩ ∷ []) ∷ [] ∎

open-goal : Goal 3
open-goal = appendo (var 0F) (var 1F) (var 2F)

partial : Run (next (tree open-goal))
partial = (1 , nil ∷ var 0F ∷ var 0F ∷ []) ∷ []
        ⟶ (2 , ⟨ var 1F , nil ⟩ ∷ var 0F ∷ ⟨ var 1F , var 0F ⟩ ∷ []) ∷ []
        ⟶ (3 , ⟨ var 2F , ⟨ var 1F , nil ⟩ ⟩ ∷ var 0F
             ∷ ⟨ var 2F , ⟨ var 1F , var 0F ⟩ ⟩ ∷ []) ∷ []
        ⋯

half-goal : Goal 1
half-goal = appendo (var 0F) (var 0F) ⟨ val 1 , ⟨ val 1 , ⟨ val 1 , nil ⟩ ⟩ ⟩

no-half : Run (next (tree half-goal))
no-half = [] ⟶ [] ⟶ [] ⟶ [] ∎

no-half-proof : ∀ {m} (θ : Subst 1 m) → ¬ (θ ⊨ half-goal)
no-half-proof θ sat with ends-complete no-half θ sat
... | ()
