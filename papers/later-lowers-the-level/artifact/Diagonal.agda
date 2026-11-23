{-# OPTIONS --safe --without-K #-}

-- Diagonal presheaves on the natural numbers.
--
-- A presheaf here has one set for every stage n, and a restriction map from stage n+1 to
-- stage n.  It is "diagonal over the level l" when the set at stage n lives n universe levels
-- above l.  This file shows, with nothing but Agda's own universes:
--
--   * later lowers the level: the later of a presheaf over (lsuc l) is a presheaf over l;
--   * the usual later, guarded fixed points, and dependent products stay at their level;
--   * the universe of presheaves over l is a presheaf over (lsuc l), so its later is a
--     presheaf over l again;
--   * later, as a map on codes, sends the later of the universe over (lsuc l) to the
--     universe over l, and decoding commutes with it.
--
-- Agda checks universe levels, has no impredicative sort, and runs with --safe, so that the
-- file type-checks is the claim that the sizes are as stated.

module Diagonal where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)

------------------------------------------------------------------------
-- A small prelude

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

record ⊤ {l : Level} : Set l where
  constructor tt

record Σ {a b : Level} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

infixr 4 _,_

record Lift {a : Level} (b : Level) (A : Set a) : Set (a ⊔ b) where
  constructor lift
  field
    lower : A
open Lift public

infix 4 _≡_

data _≡_ {a : Level} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀ {a b} {A : Set a} (P : A → Set b) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

------------------------------------------------------------------------
-- Levels along the diagonal

-- The level of stage n over the base level l.  The definition accumulates in the second
-- argument, so that
--
--     at (suc n) l  =  at n (lsuc l)
--
-- holds by computation.  This equation is what makes later lower the level.
at : ℕ → Level → Level
at zero    l = l
at (suc n) l = at n (lsuc l)

-- A set at stage n over l, seen as a set at stage n over (lsuc l).
Up : ∀ n l → Set (at n l) → Set (at n (lsuc l))
Up zero    l X = Lift (lsuc l) X
Up (suc n) l X = Up n (lsuc l) X

up : ∀ n l {X : Set (at n l)} → X → Up n l X
up zero    l x = lift x
up (suc n) l x = up n (lsuc l) x

down : ∀ n l {X : Set (at n l)} → Up n l X → X
down zero    l x = lower x
down (suc n) l x = down n (lsuc l) x

down-up : ∀ n l {X : Set (at n l)} (x : X) → down n l (up n l x) ≡ x
down-up zero    l x = refl
down-up (suc n) l x = down-up n (lsuc l) x

up-down : ∀ n l {X : Set (at n l)} (x : Up n l X) → up n l (down n l x) ≡ x
up-down zero    l x = refl
up-down (suc n) l x = up-down n (lsuc l) x

-- The sets of stage n over l form a set of stage n over (lsuc l).
SetAt : ∀ n l → Set (at n (lsuc l))
SetAt zero    l = Set l
SetAt (suc n) l = SetAt n (lsuc l)

El : ∀ n l → SetAt n l → Set (at n l)
El zero    l X = X
El (suc n) l X = El n (lsuc l) X

------------------------------------------------------------------------
-- Diagonal presheaves, their elements and maps

record Psh (l : Level) : Setω where
  field
    Obj : (n : ℕ) → Set (at n l)
    res : (n : ℕ) → Obj (suc n) → Obj n
open Psh public

record Elt {l : Level} (A : Psh l) : Setω where
  field
    el  : (n : ℕ) → Obj A n
    nat : (n : ℕ) → res A n (el (suc n)) ≡ el n
open Elt public

record _⇒_ {l k : Level} (A : Psh l) (B : Psh k) : Setω where
  field
    fun : (n : ℕ) → Obj A n → Obj B n
    com : (n : ℕ) (x : Obj A (suc n)) → res B n (fun (suc n) x) ≡ fun n (res A n x)
open _⇒_ public

------------------------------------------------------------------------
-- Later lowers the level

-- The later of a presheaf over (lsuc l) is a presheaf over l.  Stage n+1 of the result is
-- stage n of the argument; the two have the same level because at (suc n) l = at n (lsuc l).
later : ∀ {l} → Psh (lsuc l) → Psh l
Obj (later {l} A) zero    = ⊤ {l}
Obj (later A) (suc n) = Obj A n
res (later A) zero    _ = tt
res (later A) (suc n) = res A n

-- Every presheaf over l is one over (lsuc l).
raise : ∀ {l} → Psh l → Psh (lsuc l)
Obj (raise {l} A) n   = Up n l (Obj A n)
res (raise {l} A) n x = up n l (res A n (down (suc n) l x))

-- The usual later, which keeps the level, is the lowering one after raising.
later0 : ∀ {l} → Psh l → Psh l
later0 A = later (raise A)

next : ∀ {l} {A : Psh l} → A ⇒ later0 A
fun next zero    _ = tt
fun (next {l} {A}) (suc n) x = up n l (res A n x)
com next zero    x = refl
com (next {l} {A}) (suc n) x =
  cong (λ z → up n l (res A n z)) (down-up (suc n) l (res A (suc n) x))

-- Guarded fixed points.
module Fix {l : Level} {A : Psh l} (f : later0 A ⇒ A) where

  pt : (n : ℕ) → Obj A n
  pt zero    = fun f zero tt
  pt (suc n) = fun f (suc n) (up n l (pt n))

  ok : (n : ℕ) → res A n (pt (suc n)) ≡ pt n
  ok zero    = com f zero (up zero l (pt zero))
  ok (suc n) =
    trans (com f (suc n) (up (suc n) l (pt (suc n))))
          (cong (λ z → fun f (suc n) (up n l z))
                (trans (cong (res A n) (down-up (suc n) l (pt (suc n)))) (ok n)))

  fix : Elt A
  el  fix = pt
  nat fix = ok

  -- The fixed point equation at every stage: fix = f (next fix).
  unfold : (n : ℕ) → pt (suc n) ≡ fun f (suc n) (fun (next {A = A}) (suc n) (pt (suc n)))
  unfold n = cong (λ z → fun f (suc n) (up n l z)) (sym (ok n))

open Fix public using (fix)

------------------------------------------------------------------------
-- Dependent products stay at their level

record Fam {l : Level} (A : Psh l) (k : Level) : Setω where
  field
    FObj : (n : ℕ) → Obj A n → Set (at n k)
    fres : (n : ℕ) (a : Obj A (suc n)) → FObj (suc n) a → FObj n (res A n a)
open Fam public

module Pi {l : Level} (A : Psh l) (B : Fam A l) where

  mutual
    -- The elements at stage n: one dependent function for every stage up to n, each
    -- restricting to the one before.
    St : (n : ℕ) → Set (at n l)
    St zero    = (a : Obj A zero) → FObj B zero a
    St (suc n) =
      Σ (Up n l (St n)) (λ g →
      Σ ((a : Obj A (suc n)) → FObj B (suc n) a) (λ f →
        (a : Obj A (suc n)) → Up n l (fres B n a (f a) ≡ top n (down n l g) (res A n a))))

    top : (n : ℕ) → St n → (a : Obj A n) → FObj B n a
    top zero    g = g
    top (suc n) g = fst (snd g)

  Prod : Psh l
  Obj Prod     = St
  res Prod n g = down n l (fst g)

  -- Application commutes with restriction.
  top-res : (n : ℕ) (g : St (suc n)) (a : Obj A (suc n)) →
            fres B n a (top (suc n) g a) ≡ top n (res Prod n g) (res A n a)
  top-res n g a = down n l (snd (snd g) a)

open Pi public using (Prod)

------------------------------------------------------------------------
-- The universe sits one level up, and its later comes back down

mutual
  -- A chain of length n over l: sets X₀ ← X₁ ← … ← Xₙ with Xₖ at stage k over l.
  -- These are the presheaves on the stages up to n, and so the elements at stage n of the
  -- universe of presheaves over l.
  Chain : (l : Level) (n : ℕ) → Set (at n (lsuc l))
  Chain l zero    = Set l
  Chain l (suc n) =
    Σ (Up n (lsuc l) (Chain l n)) (λ c →
    Σ (SetAt (suc n) l) (λ X →
      Up n (lsuc l) (El (suc n) l X → Up n l (ctop l n (down n (lsuc l) c)))))

  -- The last set of a chain.
  ctop : (l : Level) (n : ℕ) → Chain l n → Set (at n l)
  ctop l zero    X = X
  ctop l (suc n) c = El (suc n) l (fst (snd c))

-- The universe of presheaves over l is a presheaf over (lsuc l).
Univ : (l : Level) → Psh (lsuc l)
Obj (Univ l)     = Chain l
res (Univ l) n c = down n (lsuc l) (fst c)

-- Decoding: the family of elements over the universe.
Els : (l : Level) → Fam (Univ l) l
FObj (Els l) n c   = ctop l n c
fres (Els l) n c x = down n l (down n (lsuc l) (snd (snd c)) x)

-- The later of the universe over l is a presheaf over l: a guarded "type in type".
laterUniv : (l : Level) → Psh l
laterUniv l = later (Univ l)

------------------------------------------------------------------------
-- Later on codes: from the later of the universe over (lsuc l) to the universe over l

mutual
  shift : (l : Level) (n : ℕ) → Chain (lsuc l) n → Chain l (suc n)
  shift l zero    X = lift (⊤ {l}) , X , lift (λ _ → lift tt)
  shift l (suc n) (c , X , r) =
      up (suc n) (lsuc l) (shift l n (down n (lsuc (lsuc l)) c))
    , X
    , up (suc n) (lsuc l) (λ x → up (suc n) l
        (subst (λ T → T)
               (trans (sym (shift-top l n (down n (lsuc (lsuc l)) c)))
                      (cong (ctop l (suc n))
                            (sym (down-up (suc n) (lsuc l)
                                          (shift l n (down n (lsuc (lsuc l)) c))))))
               (down n (lsuc l) (down n (lsuc (lsuc l)) r x))))

  -- Decoding commutes with the shift: the last set of the shifted chain is the last set of
  -- the chain.
  shift-top : (l : Level) (n : ℕ) (d : Chain (lsuc l) n) →
              ctop l (suc n) (shift l n d) ≡ ctop (lsuc l) n d
  shift-top l zero    X           = refl
  shift-top l (suc n) (c , X , r) = refl

laterCode : (l : Level) → later (Univ (lsuc l)) ⇒ Univ l
fun (laterCode l) zero    _ = ⊤ {l}
fun (laterCode l) (suc n) d = shift l n d
com (laterCode l) zero    X = refl
com (laterCode l) (suc n) (c , X , r) =
  down-up (suc n) (lsuc l) (shift l n (down n (lsuc (lsuc l)) c))

------------------------------------------------------------------------
-- The equation for worlds stays at one level

infixr 5 _∷_

data List {a : Level} (A : Set a) : Set a where
  []  : List A
  _∷_ : A → List A → List A

mapL : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
mapL f []       = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

-- Lists, stage by stage.
Lst : ∀ {l} → Psh l → Psh l
Obj (Lst A) n = List (Obj A n)
res (Lst A) n = mapL (res A n)

-- A set as a constant presheaf.
Kobj : ∀ {l} → Set l → (n : ℕ) → Set (at n l)
Kobj     X zero    = X
Kobj {l} X (suc n) = Up n l (Kobj X n)

Kp : ∀ {l} → Set l → Psh l
Obj (Kp X)     = Kobj X
res (Kp {l} X) n = down n l

-- A presheaf as a family that does not depend on its base.
kfam : ∀ {l k} {A : Psh l} → Psh k → Fam A k
FObj (kfam B) n _ = Obj B n
fres (kfam B) n _ = res B n

-- Functions from a presheaf over l into a presheaf over (lsuc l).
Exp : ∀ {l} → Psh l → Psh (lsuc l) → Psh (lsuc l)
Exp A B = Prod (raise A) (kfam B)

-- The right-hand side of the equation for worlds,
--
--     W  =  List (later (W → Val → U)),
--
-- maps presheaves over l to presheaves over l.  The predicates W → Val → U form a presheaf
-- over (lsuc l); the lowering later brings them back to l.  With the level-keeping later0
-- in place of later the right-hand side is a presheaf over (lsuc l), and the equation cannot be
-- stated at any level.
WorldF : ∀ {l} → Set l → Psh l → Psh l
WorldF {l} Val W = Lst (later (Exp W (Exp (Kp Val) (Univ l))))
