{-# OPTIONS --safe --without-K #-}

-- A universe that is a retract of one of its own types is inconsistent.
--
-- This is Girard's paradox in Hurkens' form, for a universe given by codes and a decoding,
-- closed under dependent products and under nothing else.  Propositions are codes, a proof
-- is an element of the decoding, and only beta steps at the top of a term are used, so no
-- function extensionality is needed.
--
-- The paper uses it to show what the lowering rule cannot live with: a clock quantifier that
-- keeps the level and commutes with later, over a universe that does not mention the clock.
-- Module Clocks below derives the retract from those three assumptions.

module Collapse where

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

subst-dep : {A : Set} (P : A → Set) (g : (x : A) → P x) {x y : A} (e : x ≡ y) →
            subst P e (g x) ≡ g y
subst-dep P g refl = refl

module Paradox
  (U   : Set)                          -- the codes of the universe
  (El  : U → Set)                      -- decoding
  (Pi  : (a : U) → (El a → U) → U)     -- closure under dependent products
  (lam : {a : U} {b : El a → U} → ((x : El a) → El (b x)) → El (Pi a b))
  (app : {a : U} {b : El a → U} → El (Pi a b) → (x : El a) → El (b x))
  (beta : {a : U} {b : El a → U} (f : (x : El a) → El (b x)) (x : El a) →
          app {a} {b} (lam f) x ≡ f x)
  (c   : U)                            -- a code whose elements name all codes
  (enc : U → El c)
  (dec : El c → U)
  (dec-enc : (a : U) → dec (enc a) ≡ a)
  (B   : U)                            -- any code at all
  where

  infixr 5 _⇒_

  _⇒_ : U → U → U
  a ⇒ b = Pi a (λ _ → b)

  -- Predicates on a, with codes as truth values.
  ℘ : U → U
  ℘ a = a ⇒ c

  mem : {a : U} → El a → El (℘ a) → U
  mem x p = dec (app p x)

  setOf : {a : U} → (El a → U) → El (℘ a)
  setOf φ = lam (λ x → enc (φ x))

  mem-setOf : {a : U} (φ : El a → U) (x : El a) → mem x (setOf φ) ≡ φ x
  mem-setOf φ x = trans (cong dec (beta (λ y → enc (φ y)) x)) (dec-enc (φ x))

  inS : {a : U} (φ : El a → U) (x : El a) → El (φ x) → El (mem x (setOf φ))
  inS φ x = subst El (sym (mem-setOf φ x))

  outS : {a : U} (φ : El a → U) (x : El a) → El (mem x (setOf φ)) → El (φ x)
  outS φ x = subst El (mem-setOf φ x)

  -- Products over all codes, through the code c.
  PiU : (U → U) → U
  PiU F = Pi c (λ z → F (dec z))

  lamU : {F : U → U} → ((X : U) → El (F X)) → El (PiU F)
  lamU g = lam (λ z → g (dec z))

  appU : {F : U → U} → El (PiU F) → (X : U) → El (F X)
  appU {F} g X = subst (λ Y → El (F Y)) (dec-enc X) (app g (enc X))

  betaU : {F : U → U} (g : (X : U) → El (F X)) (X : U) → appU {F} (lamU g) X ≡ g X
  betaU {F} g X =
    trans (cong (subst (λ Y → El (F Y)) (dec-enc X)) (beta (λ z → g (dec z)) (enc X)))
          (subst-dep (λ Y → El (F Y)) g (dec-enc X))

  -- Hurkens' construction.
  F : U → U
  F X = (℘ (℘ X) ⇒ X) ⇒ ℘ (℘ X)

  V : U
  V = PiU F

  use : El V → (X : U) → El (℘ (℘ X) ⇒ X) → El (℘ (℘ X))
  use x X f = app (appU {F} x X) f

  G : El (℘ (℘ V)) → (X : U) → El (℘ (℘ X) ⇒ X) → El (℘ (℘ X))
  G T X f = setOf (λ p → mem (setOf (λ x → mem (app f (use x X f)) p)) T)

  τ : El (℘ (℘ V)) → El V
  τ T = lamU {F} (λ X → lam (G T X))

  τi : El (℘ (℘ V) ⇒ V)
  τi = lam τ

  σ : El V → El (℘ (℘ V))
  σ x = use x V τi

  -- The set { y | τ (σ y) ∈ p }.
  Q : El (℘ V) → El (℘ V)
  Q p = setOf (λ y → mem (app τi (σ y)) p)

  σ-τ : (s : El (℘ V)) (S : El (℘ (℘ V))) → mem s (σ (app τi S)) ≡ mem (Q s) S
  σ-τ s S =
    trans (cong (λ t → mem s (σ t)) (beta τ S))
   (trans (cong (λ g → mem s (app g τi)) (betaU {F} (λ X → lam (G S X)) V))
   (trans (cong (mem s) (beta (G S V) τi))
          (mem-setOf (λ p → mem (Q p) S) s)))

  to : (s : El (℘ V)) (S : El (℘ (℘ V))) → El (mem s (σ (app τi S))) → El (mem (Q s) S)
  to s S = subst El (σ-τ s S)

  from : (s : El (℘ V)) (S : El (℘ (℘ V))) → El (mem (Q s) S) → El (mem s (σ (app τi S)))
  from s S = subst El (sym (σ-τ s S))

  -- "p is inductive": every x with p ∈ σ x is in p.
  ind : El (℘ V) → U
  ind p = Pi V (λ x → mem p (σ x) ⇒ mem x p)

  ω : El (℘ (℘ V))
  ω = setOf ind

  δ : El (℘ (℘ V)) → U
  δ S = Pi (℘ V) (λ p → mem p S ⇒ mem (app τi S) p)

  lemma : El (δ ω)
  lemma = lam (λ p → lam (λ d →
    app (app (outS ind p d) (app τi ω))
        (from p ω (inS ind (Q p) (lam (λ x → lam (λ h →
          inS (λ y → mem (app τi (σ y)) p) x
              (app (app (outS ind p d) (app τi (σ x))) (from p (σ x) h)))))))))

  no : El V → U
  no y = δ (σ y) ⇒ B

  P : El (℘ V)
  P = setOf no

  P-ind : El (ind P)
  P-ind = lam (λ x → lam (λ e → inS no x (lam (λ f →
    app (outS no (app τi (σ x)) (app (app f P) e))
        (lam (λ q → lam (λ h →
          outS (λ y → mem (app τi (σ y)) q) (app τi (σ x))
               (app (app f (Q q)) (to q (σ x) h)))))))))

  paradox : El B
  paradox =
    app (outS no (app τi ω) (app (app lemma P) (inS ind P P-ind)))
        (lam (λ q → lam (λ h →
          outS (λ y → mem (app τi (σ y)) q) (app τi ω)
               (app (app lemma (Q q)) (to q ω h)))))

-- What the lowering rule cannot live with.  Take two universes with the small one coded in
-- the large one, and an operation `low` from large codes to small codes whose decoding has
-- the decoding of its argument as a retract.  With clocks, `low a` is ∀κ. later a: lowering
-- makes later a small, a quantifier that keeps the level keeps it small, and force together
-- with clock irrelevance make it equivalent to a.  Then the small universe is a retract of
-- one of its own types, and every small type is inhabited.
module Clocks
  (U₀  : Set) (El₀ : U₀ → Set)
  (Pi₀ : (a : U₀) → (El₀ a → U₀) → U₀)
  (lam : {a : U₀} {b : El₀ a → U₀} → ((x : El₀ a) → El₀ (b x)) → El₀ (Pi₀ a b))
  (app : {a : U₀} {b : El₀ a → U₀} → El₀ (Pi₀ a b) → (x : El₀ a) → El₀ (b x))
  (beta : {a : U₀} {b : El₀ a → U₀} (f : (x : El₀ a) → El₀ (b x)) (x : El₀ a) →
          app {a} {b} (lam f) x ≡ f x)
  (U₁  : Set) (El₁ : U₁ → Set)
  (u   : U₁)                                    -- the code of the small universe
  (enc₁ : U₀ → El₁ u) (dec₁ : El₁ u → U₀)
  (dec-enc₁ : (a : U₀) → dec₁ (enc₁ a) ≡ a)
  (low : U₁ → U₀)
  (into : (a : U₁) → El₁ a → El₀ (low a))
  (back : (a : U₁) → El₀ (low a) → El₁ a)
  (back-into : (a : U₁) (x : El₁ a) → back a (into a x) ≡ x)
  (B : U₀)
  where

  collapse : El₀ B
  collapse =
    Paradox.paradox U₀ El₀ Pi₀ lam app beta
      (low u)
      (λ a → into u (enc₁ a))
      (λ z → dec₁ (back u z))
      (λ a → trans (cong dec₁ (back-into u (enc₁ a))) (dec-enc₁ a))
      B
