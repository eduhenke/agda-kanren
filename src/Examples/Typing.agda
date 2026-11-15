{-# OPTIONS --safe --guardedness #-}

-- One typing relation for the simply typed λ-calculus, run in several
-- directions: type checking, type inference, and program synthesis,
-- which is proof search for implicational logic.

module Examples.Typing where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Product using (∃; Σ-syntax; _,_; _×_; proj₁)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Examples.Typing.Encoding
open import Unification.Properties Sym _≟ˢ_ hiding (_∧_; _∈_)
open import MicroKanren            Sym _≟ˢ_
open import MicroKanren.Finite    Sym _≟ˢ_ using (collect; collect-complete)
open import MicroKanren.Binders    Sym _≟ˢ_

private variable
  c m : ℕ
  R : Set

------------------------------------------------------------------------
-- The typing relation, as a goal

-- A goal with no solutions.
never : Goal c
never = val base ≐ val appˢ

-- varo i Γ e τ: e is one of the variables i, i+1, … of Γ, with type τ.
varo : ℕ → List (Term c) → Term c → Term c → Goal c
varo i []      e τ = never
varo i (a ∷ Γ) e τ = e ≐ VAR ⌜ i ⌝ᴺ ∧ τ ≐ a ∨ varo (suc i) Γ e τ

-- typed Γ e τ: e has type τ in Γ. The context is known data; the term
-- may not be, so the rules that recurse on it do so under a suspension.
typed : List (Term c) → Term c → Term c → Goal c
typed Γ e τ =
    varo 0 Γ e τ
  ∨ (fresh₃ λ a b body →
       ↑³ e ≐ LAM body ∧ ↑³ τ ≐ ⟨ a , b ⟩
     ∧ delay λ where .force → typed (a ∷ ↑³ˢ Γ) body b)
  ∨ (fresh₃ λ a f x →
       ↑³ e ≐ APP f x
     ∧ delay λ where .force → typed (↑³ˢ Γ) f ⟨ a , ↑³ τ ⟩ ∧ typed (↑³ˢ Γ) x a)

------------------------------------------------------------------------
-- The typing rules

infix 4 _⊢_∶_

_!_ : List (Term m) → ℕ → Maybe (Term m)
[]      ! i     = nothing
(a ∷ Γ) ! zero  = just a
(a ∷ Γ) ! suc i = Γ ! i

data _⊢_∶_ {m : ℕ} : List (Term m) → Term m → Term m → Set where
  ⊢var : ∀ {Γ} {e τ : Term m} (i : ℕ)
       → e ≡ VAR ⌜ i ⌝ᴺ → Γ ! i ≡ just τ → Γ ⊢ e ∶ τ
  ⊢lam : ∀ {Γ} {e τ a b body : Term m}
       → e ≡ LAM body → τ ≡ ⟨ a , b ⟩ → (a ∷ Γ) ⊢ body ∶ b → Γ ⊢ e ∶ τ
  ⊢app : ∀ {Γ} {e τ a f x : Term m}
       → e ≡ APP f x → Γ ⊢ f ∶ ⟨ a , τ ⟩ → Γ ⊢ x ∶ a → Γ ⊢ e ∶ τ

------------------------------------------------------------------------
-- The goal means typing: a substitution satisfies typed Γ e τ exactly
-- when it turns Γ, e, and τ into a derivable typing.

⊨⇒⊢ : ∀ (Γ : List (Term c)) e τ (θ : Subst c m)
  → θ ⊨ typed Γ e τ → map (apply θ) Γ ⊢ apply θ e ∶ apply θ τ

⊢⇒⊨ : ∀ (Γ : List (Term c)) e τ (θ : Subst c m)
  → map (apply θ) Γ ⊢ apply θ e ∶ apply θ τ → θ ⊨ typed Γ e τ

castT : ∀ {Γ Γ′ : List (Term m)} {e e′ τ τ′ : Term m}
  → Γ ≡ Γ′ → e ≡ e′ → τ ≡ τ′ → Γ ⊢ e ∶ τ → Γ′ ⊢ e′ ∶ τ′
castT refl refl refl d = d

-- A variable goal holds exactly when the context has that entry.
⊨⇒! : ∀ i (Γ : List (Term c)) e τ (θ : Subst c m) → θ ⊨ varo i Γ e τ
  → Σ[ j ∈ ℕ ] (apply θ e ≡ VAR ⌜ j + i ⌝ᴺ) × (map (apply θ) Γ ! j ≡ just (apply θ τ))
⊨⇒! i []      e τ θ (⊨≐ ())
⊨⇒! i (a ∷ Γ) e τ θ (⊨∨₁ (⊨∧ (⊨≐ ee) (⊨≐ eτ))) =
  0 , trans ee (cong VAR (apply-⌜⌝ᴺ θ i)) , cong just (sym eτ)
⊨⇒! i (a ∷ Γ) e τ θ (⊨∨₂ r) with ⊨⇒! (suc i) Γ e τ θ r
... | j , ee , l = suc j , trans ee (cong (λ w → VAR ⌜ w ⌝ᴺ) (+-suc j i)) , l

!⇒⊨ : ∀ i (Γ : List (Term c)) e τ (θ : Subst c m) j
  → apply θ e ≡ VAR ⌜ j + i ⌝ᴺ → map (apply θ) Γ ! j ≡ just (apply θ τ)
  → θ ⊨ varo i Γ e τ
!⇒⊨ i (a ∷ Γ) e τ θ zero    ee l =
  ⊨∨₁ (⊨∧ (⊨≐ (trans ee (cong VAR (sym (apply-⌜⌝ᴺ θ i))))) (⊨≐ (sym (just-injective l))))
!⇒⊨ i (a ∷ Γ) e τ θ (suc j) ee l =
  ⊨∨₂ (!⇒⊨ (suc i) Γ e τ θ j (trans ee (cong (λ w → VAR ⌜ w ⌝ᴺ) (sym (+-suc j i)))) l)

⊨⇒⊢ Γ e τ θ (⊨∨₁ v) with ⊨⇒! 0 Γ e τ θ v
... | j , ee , l = ⊢var j (trans ee (cong (λ w → VAR ⌜ w ⌝ᴺ) (+-identityʳ j))) l
⊨⇒⊢ Γ e τ θ
  (⊨∨₂ (⊨∨₁ (⊨fresh a (⊨fresh b (⊨fresh body (⊨∧ (⊨≐ ee) (⊨∧ (⊨≐ eτ) (⊨delay d)))))))) =
  ⊢lam (trans (sym (apply-↑³ θ₃ e)) ee) (trans (sym (apply-↑³ θ₃ τ)) eτ)
       (castT (cong (a ∷_) (apply-↑³ˢ θ₃ Γ)) refl refl
              (⊨⇒⊢ (var 2F ∷ ↑³ˢ Γ) (var 0F) (var 1F) θ₃ d))
  where θ₃ = body ▹ (b ▹ (a ▹ θ))
⊨⇒⊢ Γ e τ θ
  (⊨∨₂ (⊨∨₂ (⊨fresh a (⊨fresh f (⊨fresh x (⊨∧ (⊨≐ ee) (⊨delay (⊨∧ df dx)))))))) =
  ⊢app (trans (sym (apply-↑³ θ₃ e)) ee)
       (castT (apply-↑³ˢ θ₃ Γ) refl (cong (⟨_,_⟩ a) (apply-↑³ θ₃ τ))
              (⊨⇒⊢ (↑³ˢ Γ) (var 1F) ⟨ var 2F , ↑³ τ ⟩ θ₃ df))
       (castT (apply-↑³ˢ θ₃ Γ) refl refl (⊨⇒⊢ (↑³ˢ Γ) (var 0F) (var 2F) θ₃ dx))
  where θ₃ = x ▹ (f ▹ (a ▹ θ))

-- Recursion on the derivation, with its indices related by equations.
⊢⇒⊨′ : ∀ (Γ : List (Term c)) e τ (θ : Subst c m) {Δ u σ}
  → Δ ⊢ u ∶ σ → map (apply θ) Γ ≡ Δ → apply θ e ≡ u → apply θ τ ≡ σ
  → θ ⊨ typed Γ e τ
⊢⇒⊨′ Γ e τ θ (⊢var i ee l) refl refl refl =
  ⊨∨₁ (!⇒⊨ 0 Γ e τ θ i (trans ee (cong (λ w → VAR ⌜ w ⌝ᴺ) (sym (+-identityʳ i)))) l)
⊢⇒⊨′ Γ e τ θ (⊢lam {a = a} {b} {body} ee eτ d) refl refl refl =
  ⊨∨₂ (⊨∨₁ (⊨fresh a (⊨fresh b (⊨fresh body
    (⊨∧ (⊨≐ (trans (apply-↑³ θ₃ e) ee))
        (⊨∧ (⊨≐ (trans (apply-↑³ θ₃ τ) eτ))
            (⊨delay (⊢⇒⊨′ (var 2F ∷ ↑³ˢ Γ) (var 0F) (var 1F) θ₃ d
                       (cong (a ∷_) (apply-↑³ˢ θ₃ Γ)) refl refl))))))))
  where θ₃ = body ▹ (b ▹ (a ▹ θ))
⊢⇒⊨′ Γ e τ θ (⊢app {a = a} {f} {x} ee df dx) refl refl refl =
  ⊨∨₂ (⊨∨₂ (⊨fresh a (⊨fresh f (⊨fresh x
    (⊨∧ (⊨≐ (trans (apply-↑³ θ₃ e) ee))
        (⊨delay
          (⊨∧ (⊢⇒⊨′ (↑³ˢ Γ) (var 1F) ⟨ var 2F , ↑³ τ ⟩ θ₃ df
                    (apply-↑³ˢ θ₃ Γ) refl (cong (⟨_,_⟩ a) (apply-↑³ θ₃ τ)))
              (⊢⇒⊨′ (↑³ˢ Γ) (var 0F) (var 2F) θ₃ dx (apply-↑³ˢ θ₃ Γ) refl refl))))))))
  where θ₃ = x ▹ (f ▹ (a ▹ θ))

⊢⇒⊨ Γ e τ θ d = ⊢⇒⊨′ Γ e τ θ d refl refl refl

------------------------------------------------------------------------
-- Every query mode is correct, from the library's theorems

-- Every answer is a typing.
typing-sound : ∀ (Γ : List (Term c)) e τ {a} → a ∈ run (typed Γ e τ)
  → let θ = answerSub a in map (apply θ) Γ ⊢ apply θ e ∶ apply θ τ
typing-sound Γ e τ {a} mem =
  ⊨⇒⊢ Γ e τ (answerSub a) (sound (typed Γ e τ) mem)

-- Every typing is an instance of an answer: answers are principal.
typing-complete : ∀ (Γ : List (Term c)) e τ (θ : Subst c m)
  → map (apply θ) Γ ⊢ apply θ e ∶ apply θ τ
  → Σ[ a ∈ Answer c ] (a ∈ run (typed Γ e τ)) × θ ≤ answerSub a
typing-complete Γ e τ θ d =
  complete (typed Γ e τ) θ (⊢⇒⊨ Γ e τ θ d)

------------------------------------------------------------------------
-- Runs

-- Answers read back as types or terms; nothing if part stays unknown.
readTy : ∃ Term → Maybe (∃ Ty)
readTy (k , t) = Maybe.map (k ,_) ⌞ t ⌟ᵀ

readExp : ∃ Term → Maybe Exp
readExp (_ , t) = ⌞ t ⌟

I′ K′ : Exp
I′ = lam (var 0)
K′ = lam (lam (var 1))

-- Inference: the search for the type of K ends with its principal type
-- α → β → α, over two type variables ...
K-goal : Goal 1
K-goal = typed [] ⌜ K′ ⌝ (var 0F)

K-type : Maybe.map (map (λ a → readTy (reify a (var 0F)))) (collect 200 (run K-goal))
       ≡ just (just (2 , tv 1F ⇒ tv 0F ⇒ tv 1F) ∷ [])
K-type = refl

-- ... and every type of K is an instance of it.
K-principal : ∀ {m as} → collect 200 (run K-goal) ≡ just as
  → ∀ (θ : Subst 1 m) → [] ⊢ ⌜ K′ ⌝ ∶ θ 0F → Any (λ a → θ ≤ answerSub a) as
K-principal eq θ d = collect-complete 200 K-goal eq θ (⊢⇒⊨ [] ⌜ K′ ⌝ (var 0F) θ d)

-- Checking: the search for a typing of I at P ⇒ Q ends with no answers,
-- so there is none.
infix 4 ⊢₀_∶_

⊢₀_∶_ : Exp → Ty 0 → Set
⊢₀ e ∶ T = [] ⊢ ⌜ e ⌝ ∶ ⌜ T ⌝ᵀ

I-goal : Goal 0
I-goal = typed [] ⌜ I′ ⌝ ⌜ P ⇒ Q ⌝ᵀ

I-rejects : ¬ (⊢₀ I′ ∶ P ⇒ Q)
I-rejects d with collect-complete 200 I-goal refl (λ ()) (⊢⇒⊨ [] ⌜ I′ ⌝ ⌜ P ⇒ Q ⌝ᵀ (λ ()) d)
... | ()

-- Synthesis, read as proof search: the first proof of P ⇒ Q ⇒ P is K;
-- the next ones are K with β-redexes inside.
proofs : map (λ a → readExp (reify a (var 0F)))
             (take 3 400 (run {c = 1} (typed [] (var 0F) (↑ ⌜ P ⇒ Q ⇒ P ⌝ᵀ))))
       ≡ just K′
       ∷ just (lam (lam (app I′ (var 1))))
       ∷ just (lam (lam (app (lam (var 2)) (var 0))))
       ∷ []
proofs = refl
