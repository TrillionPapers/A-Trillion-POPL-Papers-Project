{-# OPTIONS --safe --without-K #-}

-- Agda must reject this file.
--
-- It claims that a product over the predicates of a stage is a predicate at the level of
-- the same stage.  It is one level higher.  Compare allNow in Stratified.agda, which is
-- accepted at that higher level, and allLater, which quantifies over the stage before.

module RejectedNow where

open import Stratified

module Test (Val : Set) where
  open Worlds Val

  allSame : (n : ℕ) → (Pred (suc n) → Sem (suc n)) → Sem (suc n)
  allSame n F w v = (S : Pred (suc n)) → F S w v
