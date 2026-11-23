{-# OPTIONS --safe --without-K #-}

-- Agda must reject this file.
--
-- It states the right-hand side of the equation for worlds with the later that keeps the
-- level.  The result is a presheaf over (lsuc l), not over l, so the definition does not
-- have the type claimed for it.  Compare WorldF in Diagonal.agda, which uses the lowering
-- later and is accepted.

module RejectedKeep where

open import Diagonal

WorldKeep : ∀ {l} → Set l → Psh l → Psh l
WorldKeep {l} Val W = Lst (later0 (Exp W (Exp (Kp Val) (Univ l))))
