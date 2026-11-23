{-# OPTIONS --safe --without-K #-}

-- The stratified construction of worlds, written out stage by stage.
--
-- A world of depth n+1 maps locations to predicates of depth n, and a predicate of depth n
-- speaks about worlds of depth up to n.  In a predicative theory a predicate on a type lives
-- one universe level above the type, so each stage costs one level: worlds of depth n live at
-- level n.  This is the diagonal, read off the classical construction.
--
-- The file also records the levels of three operations on predicates: the quantifier over
-- the predicates of the stage before stays at the level of its stage; the quantifier over the
-- predicates of the same stage needs one level more; and the predicate "this location holds
-- that predicate" stays at the level of its stage.

module Stratified where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

record ⊤ : Set where
  constructor tt

record _×_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B
open _×_ public

infixr 5 _∷_

data List {a : Level} (A : Set a) : Set a where
  []  : List A
  _∷_ : A → List A → List A

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

data Maybe {a : Level} (A : Set a) : Set a where
  nothing : Maybe A
  just    : A → Maybe A

lookup : ∀ {a} {A : Set a} → List A → ℕ → Maybe A
lookup []       _       = nothing
lookup (x ∷ xs) zero    = just x
lookup (x ∷ xs) (suc k) = lookup xs k

infix 4 _≡_

data _≡_ {a : Level} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

-- The level of stage n.
lv : ℕ → Level
lv zero    = lzero
lv (suc n) = lsuc (lv n)

module Worlds (Val : Set) where

  mutual
    -- Worlds of depth n live at level n.
    World : (n : ℕ) → Set (lv n)
    World zero    = List ⊤
    World (suc n) = List (Pred n)

    -- Predicates of depth n: one predicate for every depth up to n.  They live one level up.
    Pred : (n : ℕ) → Set (lv (suc n))
    Pred zero    = World zero → Val → Set
    Pred (suc n) = Pred n × (World (suc n) → Val → Set (lv (suc n)))

  -- Forgetting the last stage.
  cutP : (n : ℕ) → Pred (suc n) → Pred n
  cutP n = fst

  cutW : (n : ℕ) → World (suc n) → World n
  cutW zero    w = map (λ _ → tt) w
  cutW (suc n) w = map (cutP n) w

  -- A predicate on the worlds of one depth.
  Sem : (n : ℕ) → Set (lv (suc n))
  Sem n = World n → Val → Set (lv n)

  -- Quantifying over the predicates of the stage before keeps the level of the stage.
  allLater : (n : ℕ) → (Pred n → Sem (suc n)) → Sem (suc n)
  allLater n F w v = (S : Pred n) → F S w v

  -- Quantifying over the predicates of the same stage needs one level more.
  allNow : (n : ℕ) → (Pred (suc n) → Sem (suc n)) → World (suc n) → Val → Set (lv (suc (suc n)))
  allNow n F w v = (S : Pred (suc n)) → F S w v

  -- "Location k of the world holds the predicate S" keeps the level of the stage.
  holds : (n : ℕ) → ℕ → Pred n → World (suc n) → Set (lv (suc n))
  holds n k S w = lookup w k ≡ just S
