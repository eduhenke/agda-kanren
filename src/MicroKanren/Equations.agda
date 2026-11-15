{-# OPTIONS --safe --guardedness #-}

-- The search satisfies the equations of microKanren's stream operations.

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality as Eq
  using (refl; sym; _≡_; cong; cong₂; trans)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.List using (List; []; _∷_; _++_; map)

module MicroKanren.Equations (A : Set) (A⟨_≟_⟩ : DecidableEquality A) where

open import Unification.Properties A A⟨_≟_⟩ hiding (_∧_; _∈_)
open import MicroKanren.State A A⟨_≟_⟩
open import MicroKanren.Stream
open import MicroKanren.Goal A A⟨_≟_⟩
open import MicroKanren.Tree A A⟨_≟_⟩
open import MicroKanren.Search A A⟨_≟_⟩

private variable
  l m n c c′ c″ k : ℕ
  R S : Set
  θ : Subst c m
  t u : Term c

private variable
  g g₁ g₂ : Goal c

mzero : Stream R
mzero .step = fail

unit : R → Stream R
unit r .step = yield r mzero

mapStream : (R → S) → Stream R → Stream S
mapStream f xs .step with xs .step
... | fail        = fail
... | yield r xs′ = yield (f r) (mapStream f xs′)
... | later xs′   = later (mapStream f xs′)

mplus : Stream R → Stream R → Stream R
mplus xs ys .step with xs .step
... | fail        = ys .step
... | yield r xs′ = yield r (mplus xs′ ys)
... | later xs′   = later (mplus ys xs′)

infix 4 _≈_ _≈ˢ_

mutual
  record _≈_ (xs ys : Stream R) : Set where
    coinductive
    field ≈step : xs .step ≈ˢ ys .step

  data _≈ˢ_ {R : Set} : Step R → Step R → Set where
    fail  : fail ≈ˢ fail
    yield : ∀ {a xs ys} → xs ≈ ys → yield a xs ≈ˢ yield a ys
    later : ∀ {xs ys} → xs ≈ ys → later xs ≈ˢ later ys

immature : Stream R → Stream R
immature xs .step = later xs

open _≈_ public

≈-refl : ∀ (xs : Stream R) → xs ≈ xs
≈ˢ-refl : ∀ (s : Step R) → s ≈ˢ s
≈-refl xs .≈step = ≈ˢ-refl (xs .step)
≈ˢ-refl fail          = fail
≈ˢ-refl (yield a xs) = yield (≈-refl xs)
≈ˢ-refl (later xs)   = later (≈-refl xs)

mutual
  record Bind (xs : Stream R) (f : R → Stream R) (zs : Stream R) : Set where
    coinductive
    field unfold : Bindˢ f (xs .step) (zs .step)

  data Bindˢ (f : R → Stream R) : Step R → Step R → Set where
    fail  : Bindˢ f fail fail
    later : ∀ {xs zs} → Bind xs f zs → Bindˢ f (later xs) (later zs)
    yield : ∀ {a xs s r}
          → Bind xs f r → s ≈ˢ mplus (f a) r .step
          → Bindˢ f (yield a xs) s

open Bind public

fail≈   : search {c} fail ≈ mzero
leaf≈   : ∀ (a : Answer c) → search (leaf a) ≈ unit a
choice≈ : ∀ (x y : Tree c) → search (choice x y) ≈ mplus (search x) (search y)
within≈ : ∀ (q : c ⊑ c′) (x : Tree c′)
        → search (within q x) ≈ mapStream (extend q) (search x)
delay≈  : ∀ (t : ∞Tree c)
        → search (delay t) ≈ immature (search (t .force))
bind≈   : ∀ (x : Tree c) (k : Answer c → Tree c)
        → Bind (search x) (λ a → search (k a))
               (search (bind x k))

fail≈ .≈step = fail

finished[]≈ : resume {c} (finished []) ≈ mzero
finished[]≈ .≈step = fail

leaf≈ a .≈step = yield finished[]≈

delay≈ t .≈step = later (≈-refl _)

-- A mature prefix, then the rest of the right-hand side.
choice≈-finished : ∀ as (mv : Prefix c) (ys : Stream (Answer c)) → ys .step ≡ stepOf mv
  → resume (prepend as mv) ≈ mplus (resume (finished as)) ys
choice≈-finished []       (finished bs) ys eq .≈step rewrite eq = ≈ˢ-refl _
choice≈-finished []       (paused bs t) ys eq .≈step rewrite eq = ≈ˢ-refl _
choice≈-finished (b ∷ as) (finished bs) ys eq .≈step = yield (choice≈-finished as (finished bs) ys eq)
choice≈-finished (b ∷ as) (paused bs t) ys eq .≈step = yield (choice≈-finished as (paused bs t) ys eq)

choice≈-paused : ∀ as (x′ y : Tree c) → resume (paused as (choice y x′)) ≈ mplus (resume (paused as x′)) (search y)

choice≈ x y .≈step with next x
... | finished []        with next y in eq
...   | finished bs = ≈ˢ-refl _
...   | paused bs t = ≈ˢ-refl _
choice≈ x y .≈step | finished (b ∷ as) with next y in eq
...   | finished bs = yield (choice≈-finished as (finished bs) (search y) (cong stepOf eq))
...   | paused bs t = yield (choice≈-finished as (paused bs t) (search y) (cong stepOf eq))
choice≈ x y .≈step | paused []       x′ = later (choice≈ y x′)
choice≈ x y .≈step | paused (b ∷ as) x′ = yield (choice≈-paused as x′ y)

choice≈-paused []       x′ y .≈step = later (choice≈ y x′)
choice≈-paused (b ∷ as) x′ y .≈step = yield (choice≈-paused as x′ y)

within≈-finished : ∀ (q : c ⊑ c′) as → resume (finished (map (extend q) as)) ≈ mapStream (extend q) (resume (finished as))
within≈-finished q []       .≈step = fail
within≈-finished q (b ∷ as) .≈step = yield (within≈-finished q as)

within≈-paused : ∀ (q : c ⊑ c′) as (x′ : Tree c′)
  → resume (paused (map (extend q) as) (within q x′)) ≈ mapStream (extend q) (resume (paused as x′))

within≈ q x .≈step with next x
... | finished []        = fail
... | finished (b ∷ as)  = yield (within≈-finished q as)
... | paused []       x′ = later (within≈ q x′)
... | paused (b ∷ as) x′ = yield (within≈-paused q as x′)

within≈-paused q []       x′ .≈step = later (within≈ q x′)
within≈-paused q (b ∷ as) x′ .≈step = yield (within≈-paused q as x′)

-- Bind, answer by answer.
isb-finished : ∀ as (k : Answer c → Tree c)
  → Bind (resume (finished as)) (λ a → search (k a)) (search (bindTree as k fail))
bs-finished  : ∀ as (k : Answer c → Tree c)
  → Bindˢ (λ a → search (k a)) (stepOf (finished as)) (stepOf (nextBind as k fail (finished [])))
isb-paused   : ∀ as (x′ : Tree c) (k : Answer c → Tree c)
  → Bind (resume (paused as x′)) (λ a → search (k a)) (search (bindTree as k (delay (laterBind x′ k))))
bs-paused    : ∀ as (x′ : Tree c) (k : Answer c → Tree c)
  → Bindˢ (λ a → search (k a)) (stepOf (paused as x′))
          (stepOf (nextBind as k (delay (laterBind x′ k)) (paused [] (bind x′ k))))

-- The first answer's search, then the rest: mplus of the two.
cons≈ : ∀ a as (k : Answer c → Tree c) e
  → stepOf (nextBind (a ∷ as) k e (next e)) ≈ˢ mplus (search (k a)) (search (bindTree as k e)) .step
cons≈ a as k e rewrite bindTree-next (a ∷ as) k e = choice≈ (k a) (bindTree as k e) .≈step

isb-finished as k .unfold rewrite sym (bindTree-next as k fail) = bs-finished as k
bs-finished []       k = fail
bs-finished (a ∷ as) k = yield (isb-finished as k) (cons≈ a as k fail)

isb-paused as x′ k .unfold rewrite sym (bindTree-next as k (delay (laterBind x′ k))) = bs-paused as x′ k
bs-paused []       x′ k = later (bind≈ x′ k)
bs-paused (a ∷ as) x′ k = yield (isb-paused as x′ k) (cons≈ a as k (delay (laterBind x′ k)))

bind≈ x k .unfold with next x
... | finished as  = bs-finished as k
... | paused as x′ = bs-paused as x′ k

unique     : ∀ (x : Tree c) (f : Answer c → Stream (Answer c)) {zs zs′}
           → Bind (search x) f zs → Bind (search x) f zs′ → zs ≈ zs′
bind-unique : ∀ (x : Tree c) (k : Answer c → Tree c) {zs}
           → Bind (search x) (λ a → search (k a)) zs → zs ≈ search (bind x k)

-- Bisimilarity is approached through agreement up to every depth.
data StepEq {R : Set} : ℕ → Step R → Step R → Set where
  stop  : ∀ {s t} → StepEq zero s t
  fail  : StepEq (suc n) fail fail
  yield : ∀ {a xs ys} → StepEq n (xs .step) (ys .step) → StepEq (suc n) (yield a xs) (yield a ys)
  later : ∀ {xs ys}   → StepEq n (xs .step) (ys .step) → StepEq (suc n) (later xs) (later ys)

_≈⟨_⟩_ : Stream R → ℕ → Stream R → Set
xs ≈⟨ n ⟩ ys = StepEq n (xs .step) (ys .step)

down : ∀ {s t : Step R} → StepEq (suc n) s t → StepEq n s t
down {n = zero}  _         = stop
down {n = suc n} fail      = fail
down {n = suc n} (yield e) = yield (down e)
down {n = suc n} (later e) = later (down e)

reflₙ : ∀ n (s : Step R) → StepEq n s s
reflₙ zero    s            = stop
reflₙ (suc n) fail         = fail
reflₙ (suc n) (yield a xs) = yield (reflₙ n (xs .step))
reflₙ (suc n) (later xs)   = later (reflₙ n (xs .step))

symₙ : ∀ {s t : Step R} → StepEq n s t → StepEq n t s
symₙ stop      = stop
symₙ fail      = fail
symₙ (yield e) = yield (symₙ e)
symₙ (later e) = later (symₙ e)

transₙ : ∀ {s t u : Step R} → StepEq n s t → StepEq n t u → StepEq n s u
transₙ stop      _         = stop
transₙ fail      fail      = fail
transₙ (yield e) (yield f) = yield (transₙ e f)
transₙ (later e) (later f) = later (transₙ e f)

≈ˢ⇒ₙ : ∀ {s t : Step R} → s ≈ˢ t → ∀ n → StepEq n s t
≈ˢ⇒ₙ e         zero    = stop
≈ˢ⇒ₙ fail      (suc n) = fail
≈ˢ⇒ₙ (yield e) (suc n) = yield (≈ˢ⇒ₙ (e .≈step) n)
≈ˢ⇒ₙ (later e) (suc n) = later (≈ˢ⇒ₙ (e .≈step) n)

lim  : ∀ {xs ys : Stream R} → (∀ n → xs ≈⟨ n ⟩ ys) → xs ≈ ys
limS : ∀ {s t : Step R} → (∀ n → StepEq n s t) → s ≈ˢ t
lim h .≈step = limS h

tailʸ : ∀ {a} {xs ys : Stream R} → StepEq (suc n) (yield a xs) (yield a ys) → xs ≈⟨ n ⟩ ys
tailʸ (yield e) = e

tailˡ : ∀ {xs ys : Stream R} → StepEq (suc n) (later xs) (later ys) → xs ≈⟨ n ⟩ ys
tailˡ (later e) = e

limS {s = fail}       {fail}       h = fail
limS {s = fail}       {yield _ _}  h with h 1
... | ()
limS {s = fail}       {later _}    h with h 1
... | ()
limS {s = yield _ _}  {fail}       h with h 1
... | ()
limS {s = yield a xs} {yield b ys} h with h 1
... | yield _ = yield (lim λ n → tailʸ (h (suc n)))
limS {s = yield _ _}  {later _}    h with h 1
... | ()
limS {s = later _}    {fail}       h with h 1
... | ()
limS {s = later _}    {yield _ _}  h with h 1
... | ()
limS {s = later xs}   {later ys}   h = later (lim λ n → tailˡ (h (suc n)))

mplus-congₙ : ∀ n (xs xs′ ys ys′ : Stream R)
  → xs ≈⟨ n ⟩ xs′ → ys ≈⟨ n ⟩ ys′ → mplus xs ys ≈⟨ n ⟩ mplus xs′ ys′
mplus-congₙ zero xs xs′ ys ys′ _ _ = stop
mplus-congₙ (suc n) xs xs′ ys ys′ e₁ e₂ with xs .step | xs′ .step | e₁
... | fail        | fail         | fail     = e₂
... | yield a x₁  | yield .a x₁′ | yield e  = yield (mplus-congₙ n x₁ x₁′ ys ys′ e (down e₂))
... | later x₁    | later x₁′    | later e  = later (mplus-congₙ n ys ys′ x₁ x₁′ (down e₂) e)

-- One answer of xs: both candidates are mplus of f a and something
-- satisfying the specification for the rest.
via-mplus : ∀ n (f : Answer c → Stream (Answer c)) a (r r′ : Stream (Answer c)) {s s′}
  → s ≈ˢ mplus (f a) r .step → s′ ≈ˢ mplus (f a) r′ .step
  → r ≈⟨ n ⟩ r′ → StepEq n s s′
via-mplus n f a r r′ e e′ rr =
  transₙ (≈ˢ⇒ₙ e n)
    (transₙ (mplus-congₙ n (f a) (f a) r r′ (reflₙ n _) rr) (symₙ (≈ˢ⇒ₙ e′ n)))

uniqueₙ : ∀ n (x : Tree c) (f : Answer c → Stream (Answer c)) {zs zs′}
  → Bind (search x) f zs → Bind (search x) f zs′ → zs ≈⟨ n ⟩ zs′

uniq-finished : ∀ n as (f : Answer c → Stream (Answer c)) {s s′}
  → Bindˢ f (stepOf (finished as)) s → Bindˢ f (stepOf (finished as)) s′ → StepEq n s s′
uniq-finished zero    as       f _    _     = stop
uniq-finished (suc n) []       f fail fail  = fail
uniq-finished n       (a ∷ as) f (yield {r = r} b₁ e) (yield {r = r′} b₁′ e′) =
  via-mplus n f a r r′ e e′ (uniq-finished n as f (b₁ .unfold) (b₁′ .unfold))

uniq-paused : ∀ n as (x′ : Tree c) (f : Answer c → Stream (Answer c)) {s s′}
  → Bindˢ f (stepOf (paused as x′)) s → Bindˢ f (stepOf (paused as x′)) s′ → StepEq n s s′
uniq-paused zero    as       x′ f _ _ = stop
uniq-paused (suc n) []       x′ f (later b₁) (later b₁′) = later (uniqueₙ n x′ f b₁ b₁′)
uniq-paused n       (a ∷ as) x′ f (yield {r = r} b₁ e) (yield {r = r′} b₁′ e′) =
  via-mplus n f a r r′ e e′ (uniq-paused n as x′ f (b₁ .unfold) (b₁′ .unfold))

-- The search of x and resume (next x) have the same steps.
here-step : ∀ (x : Tree c) (f : Answer c → Stream (Answer c)) {zs}
  → Bind (search x) f zs → Bind (resume (next x)) f zs
here-step x f b .unfold = b .unfold

dispatch : ∀ n (mv : Prefix c) (f : Answer c → Stream (Answer c)) {zs zs′}
  → Bind (resume mv) f zs → Bind (resume mv) f zs′ → zs ≈⟨ n ⟩ zs′
dispatch n (finished as)  f b b′ = uniq-finished n as f (b .unfold) (b′ .unfold)
dispatch n (paused as x′) f b b′ = uniq-paused n as x′ f (b .unfold) (b′ .unfold)

uniqueₙ n x f b b′ = dispatch n (next x) f (here-step x f b) (here-step x f b′)

unique x f b b′ = lim λ n → uniqueₙ n x f b b′

bind-unique x k b = unique x _ b (bind≈ x k)
