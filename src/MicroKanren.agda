{-# OPTIONS --safe --guardedness #-}

-- microKanren: goals, the interleaving search, and its correctness.

open import Relation.Binary.Definitions using (DecidableEquality)

module MicroKanren (A : Set) (A⟨_≟_⟩ : DecidableEquality A) where

open import MicroKanren.State A A⟨_≟_⟩ public
open import MicroKanren.Stream public
open import MicroKanren.Goal A A⟨_≟_⟩ public
open import MicroKanren.Tree A A⟨_≟_⟩ public
open import MicroKanren.Search A A⟨_≟_⟩ public
open import MicroKanren.Trace A A⟨_≟_⟩ public
open import MicroKanren.Semantics A A⟨_≟_⟩ public
open import MicroKanren.Correctness A A⟨_≟_⟩ public
open import MicroKanren.Equations A A⟨_≟_⟩ public
