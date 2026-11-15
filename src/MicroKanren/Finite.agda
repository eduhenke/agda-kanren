{-# OPTIONS --safe --guardedness #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module MicroKanren.Finite (A : Set) (A⟨_≟_⟩ : DecidableEquality A) where

open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero)
open import Data.Fin.Patterns
open import Data.Bool using (Bool; true; false; T) renaming (_∧_ to _∧ᵇ_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; _×_; proj₁)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Unification.Properties A A⟨_≟_⟩ hiding (_∧_; _∈_)
open import MicroKanren A A⟨_≟_⟩

private variable
  m c c′ : ℕ
  R S : Set

data Finiteˢ {R : Set} : Step R → Set where
  fail  : Finiteˢ fail
  yield : ∀ {r xs} → Finiteˢ (xs .step) → Finiteˢ (yield r xs)
  later : ∀ {xs}   → Finiteˢ (xs .step) → Finiteˢ (later xs)

Finite : Stream R → Set
Finite xs = Finiteˢ (xs .step)

finite-answers : (xs : Stream R) → Finite xs → List R

finite-answers-sound : ∀ (xs : Stream R) (f : Finite xs)
  → All (_∈ xs) (finite-answers xs f)

finite-answers-complete : ∀ (xs : Stream R) (f : Finite xs)
  → ∀ {r} → r ∈ xs → Any (r ≡_) (finite-answers xs f)

finite-answersˢ : (st : Step R) → Finiteˢ st → List R
finite-answersˢ fail         fail     = []
finite-answersˢ (yield r xs) (yield f) = r ∷ finite-answersˢ (xs .step) f
finite-answersˢ (later xs)   (later f) = finite-answersˢ (xs .step) f

finite-answers xs = finite-answersˢ (xs .step)

finite-answersˢ-sound : ∀ (st : Step R) (f : Finiteˢ st) → All (λ r → r ∈ˢ st) (finite-answersˢ st f)
finite-answersˢ-sound fail         fail     = []
finite-answersˢ-sound (yield r xs) (yield f) = here ∷ All.map there (finite-answersˢ-sound (xs .step) f)
finite-answersˢ-sound (later xs)   (later f) = All.map later (finite-answersˢ-sound (xs .step) f)

finite-answers-sound xs = finite-answersˢ-sound (xs .step)

finite-answersˢ-complete : ∀ (st : Step R) (f : Finiteˢ st)
  → ∀ {r} → r ∈ˢ st → Any (r ≡_) (finite-answersˢ st f)
finite-answersˢ-complete (yield _ _)  (yield f) here      = Any.here refl
finite-answersˢ-complete (yield _ xs) (yield f) (there m) = Any.there (finite-answersˢ-complete (xs .step) f m)
finite-answersˢ-complete (later xs)   (later f) (later m)  = finite-answersˢ-complete (xs .step) f m

finite-answers-complete xs = finite-answersˢ-complete (xs .step)

finite-finished : ∀ (as : List (Answer c)) → Finiteˢ (stepOf (finished as))
finite-finished []       = fail
finite-finished (a ∷ as) = yield (finite-finished as)

finite-prepend : ∀ as (mv : Prefix c) → Finiteˢ (stepOf mv) → Finiteˢ (stepOf (prepend as mv))
finite-prepend []       (finished bs) f = f
finite-prepend []       (paused bs t) f = f
finite-prepend (a ∷ as) (finished bs) f = yield (finite-prepend as (finished bs) f)
finite-prepend (a ∷ as) (paused bs t) f = yield (finite-prepend as (paused bs t) f)

finite-choice    : ∀ (x y : Tree c)
  → Finite (search x) → Finite (search y) → Finite (search (choice x y))
finite-choice-paused : ∀ as (x′ y : Tree c)
  → Finiteˢ (stepOf (paused as x′)) → Finite (search y) → Finiteˢ (stepOf (paused as (choice y x′)))

finite-choice x y fx fy with next x | fx
... | finished as  | _ = finite-prepend as (next y) fy
... | paused as x′ | f = finite-choice-paused as x′ y f fy

finite-choice-paused []       x′ y (later f) fy = later (finite-choice y x′ fy f)
finite-choice-paused (a ∷ as) x′ y (yield f) fy = yield (finite-choice-paused as x′ y f fy)

finite-within    : ∀ (q : c ⊑ c′) (x : Tree c′)
  → Finite (search x) → Finite (search (within q x))
finite-within-paused : ∀ (q : c ⊑ c′) as (x′ : Tree c′)
  → Finiteˢ (stepOf (paused as x′)) → Finiteˢ (stepOf (paused (map (extend q) as) (within q x′)))

finite-within q x fx with next x | fx
... | finished as  | _ = finite-finished (map (extend q) as)
... | paused as x′ | f = finite-within-paused q as x′ f

finite-within-paused q []       x′ (later f) = later (finite-within q x′ f)
finite-within-paused q (a ∷ as) x′ (yield f) = yield (finite-within-paused q as x′ f)

finite-bindTree : ∀ as (k : Answer c → Tree c) e
  → (∀ a → Finite (search (k a))) → Finite (search e) → Finite (search (bindTree as k e))
finite-bindTree []       k e fk fe = fe
finite-bindTree (a ∷ as) k e fk fe =
  finite-choice (k a) (bindTree as k e) (fk a) (finite-bindTree as k e fk fe)

-- A bind steps as its tree of choices does.
finite-nextBind : ∀ as (k : Answer c → Tree c) e
  → (∀ a → Finite (search (k a))) → Finite (search e)
  → Finiteˢ (stepOf (nextBind as k e (next e)))
finite-nextBind as k e fk fe =
  subst (λ mv → Finiteˢ (stepOf mv)) (sym (bindTree-next as k e)) (finite-bindTree as k e fk fe)

finite-bind    : ∀ (x : Tree c) (k : Answer c → Tree c)
  → Finite (search x) → (∀ a → Finite (search (k a)))
  → Finite (search (bind x k))
finite-bind-paused : ∀ as (x′ : Tree c) (k : Answer c → Tree c)
  → Finiteˢ (stepOf (paused as x′)) → (∀ a → Finite (search (k a)))
  → Finite (search (bind x′ k))

finite-bind x k fx fk with next x | fx
... | finished as  | _ = finite-nextBind as k fail fk fail
... | paused as x′ | f = finite-nextBind as k (delay (laterBind x′ k)) fk
                       (later (finite-bind-paused as x′ k f fk))

finite-bind-paused []       x′ k (later f) fk = finite-bind x′ k f fk
finite-bind-paused (a ∷ as) x′ k (yield f) fk = finite-bind-paused as x′ k f fk

-- Splitting a boolean conjunction.
split : ∀ x y → T (x ∧ᵇ y) → T x × T y
split true  y t = tt , t
split false y ()

finite? : Goal c → Bool
finite? (t ≐ u)   = true
finite? (fresh f) = finite? (f (var 0F))
finite? (g₁ ∨ g₂) = finite? g₁ ∧ᵇ finite? g₂
finite? (g₁ ∧ g₂) = finite? g₁ ∧ᵇ finite? g₂
finite? (delay g) = false

suspension-free : ∀ (g : Goal c) → T (finite? g) → Finite (run g)

takeAll : ∀ (g : Goal c) {fin : T (finite? g)} → List (Answer c)

takeAll-complete : ∀ (g : Goal c) {fin : T (finite? g)} (θ : Subst c m) → θ ⊨ g
  → Any (λ a → θ ≤ answerSub a) (takeAll g {fin})

finite : ∀ (g : Goal c) → T (finite? g)
  → ∀ (p : c ⊑ c′) (s : State c′) → Finite (search (⟦ g ⟧ p s))

finite (t ≐ u) _ p (mkState σ) with amgu (wk p t) (wk p u) (_ , σ)
... | nothing = fail
... | just _  = yield fail
finite (fresh f) fin p (mkState σ) =
  finite-within (skip id) (⟦ f (var zero) ⟧ (keep p) (mkState (liftAList σ)))
            (finite (f (var zero)) fin (keep p) (mkState (liftAList σ)))
finite (g₁ ∨ g₂) fin p s with split (finite? g₁) (finite? g₂) fin
... | f₁ , f₂ = finite-choice (⟦ g₁ ⟧ p s) (⟦ g₂ ⟧ p s) (finite g₁ f₁ p s) (finite g₂ f₂ p s)
finite (g₁ ∧ g₂) fin p s with split (finite? g₁) (finite? g₂) fin
... | f₁ , f₂ =
  finite-bind (⟦ g₁ ⟧ p s) (after g₂ p) (finite g₁ f₁ p s) λ where
    (answer q s′) → finite-within q (⟦ g₂ ⟧ (p ∙ q) s′) (finite g₂ f₂ (p ∙ q) s′)
finite (delay g) () p s

suspension-free g fin = finite g fin id (mkState ε)

takeAll g {fin} = finite-answers (run g) (suspension-free g fin)

takeAll-sound : ∀ (g : Goal c) {fin : T (finite? g)}
  → All (λ a → answerSub a ⊨ g) (takeAll g {fin})
takeAll-sound g {fin} =
  All.map (sound g) (finite-answers-sound (run g) (suspension-free g fin))

takeAll-complete g {fin} θ sat with complete g θ sat
... | a , mem , le =
  Any.map (λ { refl → le }) (finite-answers-complete (run g) (suspension-free g fin) mem)

collectS : ℕ → Step R → Maybe (List R)
collectS zero    _            = nothing
collectS (suc n) fail         = just []
collectS (suc n) (yield r xs) = Maybe.map (r ∷_) (collectS n (xs .step))
collectS (suc n) (later xs)   = collectS n (xs .step)

collect : ℕ → Stream R → Maybe (List R)
collect n xs = collectS n (xs .step)

collectS-sound : ∀ n (st : Step R) {rs} → collectS n st ≡ just rs
  → All (λ r → r ∈ˢ st) rs
collectS-sound (suc n) fail         refl = []
collectS-sound (suc n) (yield r xs) eq with collectS n (xs .step) in e
collectS-sound (suc n) (yield r xs) refl | just rs =
  here ∷ All.map there (collectS-sound n (xs .step) e)
collectS-sound (suc n) (later xs)   eq = All.map later (collectS-sound n (xs .step) eq)

collectS-complete : ∀ n (st : Step R) {rs} → collectS n st ≡ just rs
  → ∀ {r} → r ∈ˢ st → Any (r ≡_) rs
collectS-complete (suc n) (yield r xs) eq here with collectS n (xs .step)
collectS-complete (suc n) (yield r xs) refl here | just rs = Any.here refl
collectS-complete (suc n) (yield r xs) eq (there m) with collectS n (xs .step) in e
collectS-complete (suc n) (yield r xs) refl (there m) | just rs =
  Any.there (collectS-complete n (xs .step) e m)
collectS-complete (suc n) (later xs) eq (later m) = collectS-complete n (xs .step) eq m

collect-sound : ∀ fuel (g : Goal c) {as} → collect fuel (run g) ≡ just as
  → All (λ a → answerSub a ⊨ g) as
collect-sound fuel g eq = All.map (sound g) (collectS-sound fuel _ eq)

collect-complete : ∀ fuel (g : Goal c) {as} → collect fuel (run g) ≡ just as
  → ∀ (θ : Subst c m) → θ ⊨ g → Any (λ a → θ ≤ answerSub a) as
collect-complete fuel g eq θ sat with complete g θ sat
... | a , mem , le = Any.map (λ { refl → le }) (collectS-complete fuel _ eq mem)

Ends : ∀ {p : Prefix c} → Run p → Set
Ends (_ ⟶ r) = Ends r
Ends (_ ∎)   = ⊤
Ends (_ ⋯)   = ⊥

ends-finite : ∀ (g : Goal c) (r : Run (next (tree g))) → Ends r → Finite (run g)

finite-run : ∀ (g : Goal c) → Finite (run g) → Σ (Run (next (tree g))) Ends

finite-paused : ∀ as (t : Tree c) → Finiteˢ (stepOf (next t)) → Finiteˢ (stepOf (paused as t))
finite-paused []       t f = later f
finite-paused (a ∷ as) t f = yield (finite-paused as t f)

ends-finiteˢ : ∀ {p : Prefix c} (r : Run p) → Ends r → Finiteˢ (stepOf p)
ends-finiteˢ {p = finished as} (_ ∎)   _ = finite-finished as
ends-finiteˢ {p = paused as t} (_ ⟶ r) e = finite-paused as t (ends-finiteˢ r e)
ends-finiteˢ {p = paused _ _}  (_∎ _ {{()}})
ends-finiteˢ {p = finished _}  (_⟶_ _ {{()}} _)
ends-finiteˢ (_ ⋯) ()

ends-finite g r e = ends-finiteˢ r e

finite-runˢ : ∀ (p : Prefix c) → Finiteˢ (stepOf p) → Σ (Run p) Ends
finite-run-paused : ∀ as (t : Tree c) → Finiteˢ (stepOf (paused as t)) → Σ (Run (next t)) Ends

finite-runˢ (finished as) f = (map solution as ∎) , tt
finite-runˢ (paused as t) f with finite-run-paused as t f
... | r , e = (map solution as ⟶ r) , e

finite-run-paused []       t (later f) = finite-runˢ (next t) f
finite-run-paused (a ∷ as) t (yield f) = finite-run-paused as t f

finite-run g f = finite-runˢ (next (tree g)) f

answers : ∀ {p : Prefix c} → Run p → List (Answer c)
answers {p = paused as _} (_ ⟶ r) = as ++ answers r
answers {p = paused as _} (_ ⋯)   = as
answers {p = finished as} (_ ∎)   = as

answers {p = finished _} (_⟶_ _ {{()}} _)
answers {p = finished _} (_⋯ _ {{()}})
answers {p = paused _ _} (_∎ _ {{()}})

ends-complete : ∀ {g : Goal c} (r : Run (next (tree g))) {{_ : Ends r}} (θ : Subst c m)
  → θ ⊨ g → Any (λ a → θ ≤ answerSub a) (answers r)

run-mem : ∀ {p : Prefix c} (r : Run p) → Ends r → ∀ {a} → a ∈ˢ stepOf p → a ∈ˡ answers r
run-mem {p = finished as} (_ ∎) _ mem = finished-inv as mem
run-mem {p = paused _ _}  (_∎ _ {{()}})
run-mem {p = finished _}  (_⟶_ _ {{()}} _)
run-mem (_ ⋯) ()
run-mem {p = paused as t} (_ ⟶ r) e mem with stepOf-sound (paused as t) mem
... | inj₁ i = ∈-++⁺ˡ i
... | inj₂ j = ∈-++⁺ʳ as (run-mem r e (search-complete j))

ends-complete {g = g} r {{e}} θ sat with complete g θ sat
... | a , mem , le = Any.map (λ { refl → le }) (run-mem r e mem)
