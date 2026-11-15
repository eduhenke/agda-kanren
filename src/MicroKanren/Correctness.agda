{-# OPTIONS --safe --guardedness #-}

-- Soundness and completeness of the search.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality as Eq
  using (refl; sym; _≡_; cong; cong₂; trans)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Product using (∃; _,_; Σ-syntax; proj₁; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.Maybe using (nothing; just)

module MicroKanren.Correctness (A : Set) (A⟨_≟_⟩ : DecidableEquality A) where

open import Unification.Properties A A⟨_≟_⟩ hiding (_∧_; _∈_)
open import MicroKanren.State A A⟨_≟_⟩
open import MicroKanren.Stream
open import MicroKanren.Goal A A⟨_≟_⟩
open import MicroKanren.Tree A A⟨_≟_⟩
open import MicroKanren.Search A A⟨_≟_⟩
open import MicroKanren.Semantics A A⟨_≟_⟩

private variable
  l m n c c′ c″ k : ℕ
  R S : Set
  θ : Subst c m
  t u : Term c

private variable
  g g₁ g₂ : Goal c

answerSub : (a : Answer c) → Subst c (State.vars (state a))
answerSub (answer q (mkState σ)) x = sub σ (ren q x)

sound : ∀ (g : Goal c) {a} → a ∈ run g → answerSub a ⊨ g

complete : ∀ (g : Goal c) {m} (θ : Subst c m) → θ ⊨ g
  → Σ[ a ∈ Answer c ] (a ∈ run g) × θ ≤ answerSub a

data _∈ᵗ_ : ∀ {c} → Answer c → Tree c → Set where
  ∈-leaf   : ∀ {a : Answer c} → a ∈ᵗ leaf a
  ∈-left   : ∀ {a : Answer c} {x y} → a ∈ᵗ x → a ∈ᵗ choice x y
  ∈-right  : ∀ {a : Answer c} {x y} → a ∈ᵗ y → a ∈ᵗ choice x y
  ∈-bind   : ∀ {a b : Answer c} {x k} → a ∈ᵗ x → b ∈ᵗ k a → b ∈ᵗ bind x k
  ∈-within : ∀ {q : c ⊑ c′} {a x} → a ∈ᵗ x → extend q a ∈ᵗ within q x
  ∈-delay  : ∀ {a : Answer c} {t} → a ∈ᵗ t .force → a ∈ᵗ delay t

------------------------------------------------------------------------
-- Membership in moves

infix 4 _∈ᵐ_

_∈ᵐ_ : Answer c → Prefix c → Set
a ∈ᵐ finished as = a ∈ˡ as
a ∈ᵐ paused as t = a ∈ˡ as ⊎ a ∈ᵗ t

prepend⁻ : ∀ as (mv : Prefix c) {a} → a ∈ᵐ prepend as mv → a ∈ˡ as ⊎ a ∈ᵐ mv
prepend⁻ as (finished bs) m = ∈-++⁻ as m
prepend⁻ as (paused bs t) (inj₁ m) with ∈-++⁻ as m
... | inj₁ i = inj₁ i
... | inj₂ j = inj₂ (inj₁ j)
prepend⁻ as (paused bs t) (inj₂ m) = inj₂ (inj₂ m)

bindTree⁻ : ∀ as (k : Answer c → Tree c) e {b} → b ∈ᵗ bindTree as k e
  → (Σ[ a ∈ Answer c ] a ∈ˡ as × b ∈ᵗ k a) ⊎ b ∈ᵗ e
bindTree⁻ []       k e m       = inj₂ m
bindTree⁻ (a ∷ as) k e (∈-left m) = inj₁ (a , here refl , m)
bindTree⁻ (a ∷ as) k e (∈-right m) with bindTree⁻ as k e m
... | inj₁ (a′ , i , m′) = inj₁ (a′ , there i , m′)
... | inj₂ m′            = inj₂ m′

------------------------------------------------------------------------
-- Running is sound: a step finds only answers of the tree.

next-sound     : ∀ (x : Tree c) {a} → a ∈ᵐ next x → a ∈ᵗ x
nextBind-sound : ∀ as (k : Answer c → Tree c) e em
  → (∀ {b} → b ∈ᵐ em → b ∈ᵗ e)
  → ∀ {b} → b ∈ᵐ nextBind as k e em → b ∈ᵗ bindTree as k e

next-sound fail     ()
next-sound (leaf a) (here refl) = ∈-leaf
next-sound (choice x y) m with next x | next-sound x
... | finished as  | sx with prepend⁻ as (next y) m
...   | inj₁ i = ∈-left (sx i)
...   | inj₂ j = ∈-right (next-sound y j)
next-sound (choice x y) (inj₁ i)       | paused as x′ | sx = ∈-left (sx (inj₁ i))
next-sound (choice x y) (inj₂ (∈-left j)) | paused as x′ | sx = ∈-right j
next-sound (choice x y) (inj₂ (∈-right j)) | paused as x′ | sx = ∈-left (sx (inj₂ j))
next-sound (bind x k) m with next x | next-sound x
... | finished as | sx with bindTree⁻ as k fail (nextBind-sound as k fail (finished []) (λ ()) m)
...   | inj₁ (a , i , j) = ∈-bind (sx i) j
...   | inj₂ ()
next-sound (bind x k) m | paused as x′ | sx
  with bindTree⁻ as k (delay (laterBind x′ k))
         (nextBind-sound as k (delay (laterBind x′ k)) (paused [] (bind x′ k)) em-ok m)
  where
    em-ok : ∀ {b} → b ∈ᵐ paused [] (bind x′ k) → b ∈ᵗ delay (laterBind x′ k)
    em-ok (inj₂ j) = ∈-delay j
... | inj₁ (a , i , j)          = ∈-bind (sx (inj₁ i)) j
... | inj₂ (∈-delay (∈-bind j₁ j₂)) = ∈-bind (sx (inj₂ j₁)) j₂
next-sound (within q x) m with next x | next-sound x
... | finished as | sx with ∈-map⁻ (extend q) m
...   | a , i , refl = ∈-within (sx i)
next-sound (within q x) (inj₁ i) | paused as x′ | sx with ∈-map⁻ (extend q) i
... | a , i′ , refl = ∈-within (sx (inj₁ i′))
next-sound (within q x) (inj₂ (∈-within j)) | paused as x′ | sx = ∈-within (sx (inj₂ j))
next-sound (delay t) (inj₂ j) = ∈-delay j

nextBind-sound []       k e em ok m = ok m
nextBind-sound (a ∷ as) k e em ok m with next (k a) | next-sound (k a)
... | finished bs | sk with prepend⁻ bs (nextBind as k e em) m
...   | inj₁ i = ∈-left (sk i)
...   | inj₂ j = ∈-right (nextBind-sound as k e em ok j)
nextBind-sound (a ∷ as) k e em ok (inj₁ i)       | paused bs t | sk = ∈-left (sk (inj₁ i))
nextBind-sound (a ∷ as) k e em ok (inj₂ (∈-left j)) | paused bs t | sk = ∈-right j
nextBind-sound (a ∷ as) k e em ok (inj₂ (∈-right j)) | paused bs t | sk = ∈-left (sk (inj₂ j))

search-sound : ∀ (x : Tree c) {a} → a ∈ search x → a ∈ᵗ x
stepOf-sound : ∀ (mv : Prefix c) {a} → a ∈ˢ stepOf mv → a ∈ᵐ mv

search-sound x mem = next-sound x (stepOf-sound (next x) mem)

stepOf-sound (finished [])       ()
stepOf-sound (finished (b ∷ bs)) here      = here refl
stepOf-sound (finished (b ∷ bs)) (there m) = there (stepOf-sound (finished bs) m)
stepOf-sound (paused [] t)       (later m)  = inj₂ (search-sound t m)
stepOf-sound (paused (b ∷ bs) t) here      = inj₁ (here refl)
stepOf-sound (paused (b ∷ bs) t) (there m) with stepOf-sound (paused bs t) m
... | inj₁ i = inj₁ (there i)
... | inj₂ j = inj₂ j

------------------------------------------------------------------------
-- Running is complete: no answer of the tree is missed.

finished-inv : ∀ as {a : Answer c} → a ∈ˢ stepOf (finished as) → a ∈ˡ as
finished-inv (b ∷ bs) here      = here refl
finished-inv (b ∷ bs) (there m) = there (finished-inv bs m)

finished-mem : ∀ {as} {a : Answer c} → a ∈ˡ as → a ∈ˢ stepOf (finished as)
finished-mem (here refl) = here
finished-mem (there i)   = there (finished-mem i)

paused-skip : ∀ as (t : Tree c) {a} → a ∈ search t → a ∈ˢ stepOf (paused as t)
paused-skip []       t m = later m
paused-skip (b ∷ bs) t m = there (paused-skip bs t m)

prepend-l : ∀ as (mv : Prefix c) {a} → a ∈ˡ as → a ∈ˢ stepOf (prepend as mv)
prepend-l (b ∷ as) (finished bs) (here refl) = here
prepend-l (b ∷ as) (finished bs) (there i)   = there (prepend-l as (finished bs) i)
prepend-l (b ∷ as) (paused bs t) (here refl) = here
prepend-l (b ∷ as) (paused bs t) (there i)   = there (prepend-l as (paused bs t) i)

prepend-r : ∀ as (mv : Prefix c) {a} → a ∈ˢ stepOf mv → a ∈ˢ stepOf (prepend as mv)
prepend-r []       (finished bs) m = m
prepend-r []       (paused bs t) m = m
prepend-r (b ∷ as) (finished bs) m = there (prepend-r as (finished bs) m)
prepend-r (b ∷ as) (paused bs t) m = there (prepend-r as (paused bs t) m)

-- Fairness of mplus: a choice loses no answer of either side.
choice⁺ˡ    : ∀ (x y : Tree c) {a} → a ∈ search x → a ∈ search (choice x y)
choice⁺ʳ    : ∀ (x y : Tree c) {a} → a ∈ search y → a ∈ search (choice x y)
choice⁺ˡ-paused : ∀ as (x′ y : Tree c) {a}
  → a ∈ˢ stepOf (paused as x′) → a ∈ˢ stepOf (paused as (choice y x′))

choice⁺ˡ x y mem with next x
... | finished as  = prepend-l as (next y) (finished-inv as mem)
... | paused as x′ = choice⁺ˡ-paused as x′ y mem

choice⁺ˡ-paused []       x′ y (later m)  = later (choice⁺ʳ y x′ m)
choice⁺ˡ-paused (b ∷ bs) x′ y here      = here
choice⁺ˡ-paused (b ∷ bs) x′ y (there m) = there (choice⁺ˡ-paused bs x′ y m)

choice⁺ʳ x y mem with next x
... | finished as  = prepend-r as (next y) mem
... | paused as x′ = paused-skip as (choice y x′) (choice⁺ˡ y x′ mem)

within⁺    : ∀ (q : c ⊑ c′) (x : Tree c′) {a} → a ∈ search x → extend q a ∈ search (within q x)
within⁺-paused : ∀ (q : c ⊑ c′) as (x′ : Tree c′) {a}
  → a ∈ˢ stepOf (paused as x′) → extend q a ∈ˢ stepOf (paused (map (extend q) as) (within q x′))

within⁺ q x mem with next x
... | finished as  = finished-mem (∈-map⁺ (extend q) (finished-inv as mem))
... | paused as x′ = within⁺-paused q as x′ mem

within⁺-paused q []       x′ (later m)  = later (within⁺ q x′ m)
within⁺-paused q (b ∷ bs) x′ here      = here
within⁺-paused q (b ∷ bs) x′ (there m) = there (within⁺-paused q bs x′ m)

nextBind⁺ : ∀ as (k : Answer c → Tree c) e {b}
  → b ∈ search (bindTree as k e) → b ∈ˢ stepOf (nextBind as k e (next e))
nextBind⁺ as k e {b} m rewrite bindTree-next as k e = m

bindTree⁺ˡ : ∀ as (k : Answer c → Tree c) e {a b}
  → a ∈ˡ as → b ∈ search (k a) → b ∈ search (bindTree as k e)
bindTree⁺ˡ (a ∷ as) k e (here refl) m = choice⁺ˡ (k a) (bindTree as k e) m
bindTree⁺ˡ (a ∷ as) k e (there i)   m = choice⁺ʳ (k a) (bindTree as k e) (bindTree⁺ˡ as k e i m)

bindTree⁺ʳ : ∀ as (k : Answer c → Tree c) e {b}
  → b ∈ search e → b ∈ search (bindTree as k e)
bindTree⁺ʳ []       k e m = m
bindTree⁺ʳ (a ∷ as) k e m = choice⁺ʳ (k a) (bindTree as k e) (bindTree⁺ʳ as k e m)

bind⁺    : ∀ (x : Tree c) (k : Answer c → Tree c) {a b}
  → a ∈ search x → b ∈ search (k a) → b ∈ search (bind x k)
bind⁺-paused : ∀ as {as₂} (x′ : Tree c) (k : Answer c → Tree c)
  → (∀ {z} → z ∈ˡ as₂ → z ∈ˡ as)
  → ∀ {a b} → a ∈ˢ stepOf (paused as₂ x′) → b ∈ search (k a)
  → b ∈ˢ stepOf (nextBind as k (delay (laterBind x′ k)) (paused [] (bind x′ k)))

bind⁺ x k memx memk with next x
... | finished as  = nextBind⁺ as k fail (bindTree⁺ˡ as k fail (finished-inv as memx) memk)
... | paused as x′ = bind⁺-paused as x′ k (λ i → i) memx memk

bind⁺-paused as {[]} x′ k emb (later mm) memk =
  nextBind⁺ as k (delay (laterBind x′ k))
      (bindTree⁺ʳ as k (delay (laterBind x′ k)) (later (bind⁺ x′ k mm memk)))
bind⁺-paused as {a′ ∷ as₂} x′ k emb here memk =
  nextBind⁺ as k (delay (laterBind x′ k)) (bindTree⁺ˡ as k (delay (laterBind x′ k)) (emb (here refl)) memk)
bind⁺-paused as {a′ ∷ as₂} x′ k emb (there m) memk =
  bind⁺-paused as {as₂} x′ k (λ i → emb (there i)) m memk

search-complete : ∀ {x : Tree c} {a} → a ∈ᵗ x → a ∈ search x
search-complete ∈-leaf                    = here
search-complete (∈-left {x = x} {y} m)      = choice⁺ˡ x y (search-complete m)
search-complete (∈-right {x = x} {y} m)      = choice⁺ʳ x y (search-complete m)
search-complete (∈-bind {x = x} {k} m₁ m₂) = bind⁺ x k (search-complete m₁) (search-complete m₂)
search-complete (∈-within {q = q} {x = x} m)  = within⁺ q x (search-complete m)
search-complete (∈-delay m)                = later (search-complete m)

------------------------------------------------------------------------
-- The denotation is sound: every answer in a goal's tree is a solution.

denote-sound : ∀ (g : Goal c) (p : c ⊑ c′) (σ : AList c′ k) {b}
  → b ∈ᵗ ⟦ g ⟧ p (mkState σ)
  → (λ x → answerSub b (ren p x)) ⊨ g × answerSub b ≤ sub σ
denote-sound (t ≐ u) p σ mem
  with amgu (wk p t) (wk p u) (_ , σ) | amgu-correct (wk p t) (wk p u) σ | mem
... | nothing        | not-unifies _ | ()
... | just (k′ , σ′) | unifies τ (unif , _) | ∈-leaf =
      ⊨≐ (trans (sym (apply-wk (sub σ′) p t))
                (trans unif′ (apply-wk (sub σ′) p u)))
    , sub τ , (λ x → sym (pw x))
  where
    pw : ∀ x → (sub τ ◇ sub σ) x ≡ sub σ′ x
    pw x = sym (sub-++-◇ τ σ x)

    unif′ : Unifies (wk p t) (wk p u) (sub σ′)
    unif′ = Unifies-cong (wk p t) (wk p u) (sub τ ◇ sub σ) (sub σ′) pw unif
denote-sound (fresh f) p σ (∈-within {a = answer q′ (mkState σ′)} m)
  with denote-sound (f (var zero)) (keep p) (liftAList σ) m
... | s , (h , e) =
    ⊨fresh (sub σ′ (ren q′ zero)) (⊨-cong pw s)
  , ( (λ z → h (suc z))
    , λ x → trans (cong (sub σ′) (ren-∙ (skip id) q′ x))
            (trans (e (suc x))
            (trans (cong (apply h) (sub-liftAList-old σ x))
                   (apply-weaken (sub σ x) h))) )
  where
    pw : ∀ z → sub σ′ (ren q′ (ren (keep p) z))
             ≡ (sub σ′ (ren q′ zero) ▹ (λ y → sub σ′ (ren (skip id ∙ q′) (ren p y)))) z
    pw zero    = refl
    pw (suc y) = cong (sub σ′) (sym (ren-∙ (skip id) q′ (ren p y)))
denote-sound (g₁ ∨ g₂) p σ (∈-left m) with denote-sound g₁ p σ m
... | s , le = ⊨∨₁ s , le
denote-sound (g₁ ∨ g₂) p σ (∈-right m) with denote-sound g₂ p σ m
... | s , le = ⊨∨₂ s , le
denote-sound (g₁ ∧ g₂) p σ
  (∈-bind {a = answer q₁ (mkState σ₁)} m₁ (∈-within {a = answer q₂ (mkState σ₂)} m₂))
  with denote-sound g₁ p σ m₁ | denote-sound g₂ (p ∙ q₁) σ₁ m₂
... | s₁ , (h₁ , e₁) | s₂ , (h₂ , e₂) =
    ⊨∧ (⊨-inst h₂ inst s₁) (⊨-cong pw₂ s₂)
  , ( h₂ ◇ h₁
    , λ x → trans (cong (sub σ₂) (ren-∙ q₁ q₂ x))
            (trans (e₂ (ren q₁ x))
            (trans (cong (apply h₂) (e₁ x))
                   (apply-assoc (sub σ x) h₁ h₂))) )
  where
    inst : ∀ x → sub σ₂ (ren (q₁ ∙ q₂) (ren p x))
               ≡ (h₂ ◇ (λ y → sub σ₁ (ren q₁ (ren p y)))) x
    inst x = trans (cong (sub σ₂) (ren-∙ q₁ q₂ (ren p x))) (e₂ (ren q₁ (ren p x)))

    pw₂ : ∀ y → sub σ₂ (ren q₂ (ren (p ∙ q₁) y)) ≡ sub σ₂ (ren (q₁ ∙ q₂) (ren p y))
    pw₂ y = cong (sub σ₂) (trans (cong (ren q₂) (ren-∙ p q₁ y))
                                 (sym (ren-∙ q₁ q₂ (ren p y))))
denote-sound (delay g) p σ (∈-delay m) with denote-sound (g .force) p σ m
... | s , le = ⊨delay s , le

------------------------------------------------------------------------
-- The denotation is complete: every solution is covered by an answer.

≐-unif : ∀ (t u : Term c) (p : c ⊑ c′) (σ : AList c′ k)
           (θ : Subst c′ m) {θ′ : Subst c m} f
  → (∀ x → θ x ≡ (f ◇ sub σ) x) → (∀ x → θ′ x ≡ θ (ren p x))
  → Unifies t u θ′ → Unifies (wk p t) (wk p u) (f ◇ sub σ)
≐-unif t u p σ θ f e pw sat =
  Unifies-cong (wk p t) (wk p u) θ (f ◇ sub σ) e
    (trans (apply-wk θ p t)
    (trans (Unifies-cong t u _ (λ x → θ (ren p x)) pw sat)
           (sym (apply-wk θ p u))))

denote-complete : ∀ {g : Goal c} (p : c ⊑ c′) (σ : AList c′ k)
                    (θ : Subst c′ m) {θ′ : Subst c m}
  → θ ≤ sub σ → (∀ x → θ′ x ≡ θ (ren p x)) → θ′ ⊨ g
  → Σ[ a ∈ Answer c′ ] (a ∈ᵗ ⟦ g ⟧ p (mkState σ)) × θ ≤ answerSub a

denote-complete p σ θ (f , e) pw (⊨≐ {t = t} {u} sat)
  with amgu (wk p t) (wk p u) (_ , σ) | amgu-correct (wk p t) (wk p u) σ
... | nothing       | not-unifies ¬un = ⊥-elim (¬un f (≐-unif t u p σ θ f e pw sat))
... | just (_ , σ′) | unifies τ (_ , max)
    with max f (≐-unif t u p σ θ f e pw sat)
...   | h , fh =
      answer id (mkState σ′)
    , ∈-leaf
    , ( h
      , λ x → trans (e x)
              (trans (apply-cong (sub σ x) f (h ◇ sub τ) fh)
              (trans (sym (apply-assoc (sub σ x) (sub τ) h))
                     (cong (apply h) (sym (sub-++-◇ τ σ x))))) )

denote-complete p σ θ {θ′} (f₀ , e) pw (⊨fresh t sat)
  with denote-complete (keep p) (liftAList σ) (t ▹ θ) le″ pw′ sat
  where
    le″ : (t ▹ θ) ≤ sub (liftAList σ)
    le″ = (t ▹ f₀) , λ where
      zero    → sym (cong (apply (t ▹ f₀)) (sub-liftAList-new σ))
      (suc y) → trans (e y) (sym (trans (cong (apply (t ▹ f₀)) (sub-liftAList-old σ y))
                                        (apply-weaken (sub σ y) (t ▹ f₀))))

    pw′ : ∀ z → (t ▹ θ′) z ≡ (t ▹ θ) (ren (keep p) z)
    pw′ zero    = refl
    pw′ (suc y) = pw y
... | answer q′ (mkState σ′) , mem , (h , e′) =
      answer (skip id ∙ q′) (mkState σ′)
    , ∈-within mem
    , ( h
      , λ x → trans (e′ (suc x))
                    (cong (λ y → apply h (sub σ′ y)) (sym (ren-∙ (skip id) q′ x))) )

denote-complete p σ θ le pw (⊨∨₁ sat) with denote-complete p σ θ le pw sat
... | a , mem , le′ = a , ∈-left mem , le′
denote-complete p σ θ le pw (⊨∨₂ sat) with denote-complete p σ θ le pw sat
... | a , mem , le′ = a , ∈-right mem , le′

denote-complete p σ θ {θ′} le pw (⊨∧ sat₁ sat₂)
  with denote-complete p σ θ le pw sat₁
... | answer q₁ (mkState σ₁) , mem₁ , (f₁ , e₁)
    with denote-complete (p ∙ q₁) σ₁ (f₁ ◇ sub σ₁) (f₁ , λ _ → refl) pw₂ sat₂
  where
    pw₂ : ∀ x → θ′ x ≡ (f₁ ◇ sub σ₁) (ren (p ∙ q₁) x)
    pw₂ x = trans (pw x)
            (trans (e₁ (ren p x))
                   (cong (λ y → apply f₁ (sub σ₁ y)) (sym (ren-∙ p q₁ x))))
...   | answer q₂ (mkState σ₂) , mem₂ , (f₂ , e₂) =
        answer (q₁ ∙ q₂) (mkState σ₂)
      , ∈-bind mem₁ (∈-within mem₂)
      , ( f₂
        , λ x → trans (e₁ x)
                (trans (e₂ (ren q₁ x))
                       (cong (λ y → apply f₂ (sub σ₂ y)) (sym (ren-∙ q₁ q₂ x)))) )

denote-complete p σ θ le pw (⊨delay sat) with denote-complete p σ θ le pw sat
... | a , mem , le′ = a , ∈-delay mem , le′

------------------------------------------------------------------------
-- Together: the search finds exactly the solutions, along any extension
-- and from any state.

sound-along : ∀ (g : Goal c) (p : c ⊑ c′) (σ : AList c′ k) {a}
  → a ∈ search (⟦ g ⟧ p (mkState σ))
  → (λ x → answerSub a (ren p x)) ⊨ g × answerSub a ≤ sub σ
sound-along g p σ mem = denote-sound g p σ (search-sound (⟦ g ⟧ p (mkState σ)) mem)

complete-along : ∀ (g : Goal c) (p : c ⊑ c′) (σ : AList c′ k) {m}
                   (θ : Subst c′ m)
  → θ ≤ sub σ → (λ x → θ (ren p x)) ⊨ g
  → Σ[ a ∈ Answer c′ ] (a ∈ search (⟦ g ⟧ p (mkState σ))) × θ ≤ answerSub a
complete-along g p σ θ le sat with denote-complete p σ θ le (λ _ → refl) sat
... | a , mem , le′ = a , search-complete mem , le′

-- At the start of a search.
sound g mem = proj₁ (sound-along g id ε mem)

complete g θ sat = complete-along g id ε θ (θ , λ _ → refl) sat
