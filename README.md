# agda-kanren

A formalization of microKanren in Agda. Unification and the interleaving
search are implemented as total functions and proved correct. Every module
type-checks under `--safe`; the modules that use coinduction also use
`--guardedness`.

This is the code of the MSc dissertation *A Mechanized Formalization of
microKanren in Agda* (Eduardo Henke, advised by Rodrigo Ribeiro, Universidade
Federal de Ouro Preto, 2026). The tag `thesis` marks the version the
dissertation describes. An earlier account appeared at SBLP 2026
([doi:10.5753/sblp.2026.27723](https://doi.org/10.5753/sblp.2026.27723)).

## What is proved

| Result | Name | Module |
|---|---|---|
| `mgu` returns a most general unifier exactly when a unifier exists | `mgu-correct` | `Unification.Properties` |
| Every answer of the search satisfies the goal | `sound` | `MicroKanren.Correctness` |
| Every solution of a goal is an instance of some answer | `complete` | `MicroKanren.Correctness` |
| The search satisfies the equations of microKanren's stream operations | `fail≈`, `leaf≈`, `choice≈`, `within≈`, `delay≈`, `bind≈` | `MicroKanren.Equations` |
| The equation of `bind` has a single solution | `bind-unique` | `MicroKanren.Equations` |
| A run that ends lists every answer | `ends-complete` | `MicroKanren.Finite` |

Unification is McBride's structurally recursive algorithm: terms are indexed
by the number of variables in scope, and binding a variable moves the problem
to a smaller scope. The search runs on a tree that each goal denotes, and its
answers come out in the order of microKanren's `mplus` and `bind`.

## Layout

```
src/
  Unification/
    Term.agda           terms indexed by scope
    Substitution.agda   association lists, amgu, mgu
    Properties.agda     the specification and the correctness theorem
  MicroKanren.agda      re-exports the modules below
  MicroKanren/
    State.agda          search states and answers
    Stream.agda         streams with mature and immature steps
    Goal.agda           the goal language
    Tree.agda           search trees and the tree of a goal
    Search.agda         one step of a tree, and the stream of a search
    Trace.agda          runs written out step by step
    Semantics.agda      when a substitution satisfies a goal
    Correctness.agda    soundness and completeness
    Equations.agda      the equations of mplus and bind
    Finite.agda         searches that end
    Binders.agda        helpers for introducing several variables
  Examples/
    Appendo.agda        list concatenation, run in several directions
    Typing.agda         typing for the simply typed λ-calculus: checking, inference, synthesis
  Everything.agda       imports every module
```

## Example

List concatenation as a relation, from `Examples.Appendo`:

```agda
appendo : Term c → Term c → Term c → Goal c
appendo l r out =
    (l ≐ nil ∧ r ≐ out)
  ∨ fresh₃ λ a d res →
      ↑³ l ≐ ⟨ a , d ⟩ ∧ ↑³ out ≐ ⟨ a , res ⟩
    ∧ delay λ where .force → appendo d (↑³ r) res
```

Asking for every way to split the list `(1 2)` gives three answers, one per
step of the search. The type checker accepts the run only if each step
produces exactly the answers written:

```agda
split-goal : Goal 2
split-goal = appendo (var 0F) (var 1F) ⟨ val 1 , ⟨ val 2 , nil ⟩ ⟩

splits : Run (next (tree split-goal))
splits = (0 , nil ∷ ⟨ val 1 , ⟨ val 2 , nil ⟩ ⟩ ∷ []) ∷ []
       ⟶ (0 , ⟨ val 1 , nil ⟩ ∷ ⟨ val 2 , nil ⟩ ∷ []) ∷ []
       ⟶ (0 , ⟨ val 1 , ⟨ val 2 , nil ⟩ ⟩ ∷ nil ∷ []) ∷ []
       ∎
```

A run that ends with no answers is a refutation: with `ends-complete`, it
proves that the goal has no solution.

## Building

Tested with Agda 2.8.0 and the standard library 2.3.

```
agda src/Everything.agda
```

## License

MIT
