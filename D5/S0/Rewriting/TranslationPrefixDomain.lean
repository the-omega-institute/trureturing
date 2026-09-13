/- GID: D5/S0/Rewriting/TranslationPrefixDomain
   generality: G
   mirror-B: D5/B/S0/Rewriting/TranslationPrefixDomain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Guarded integer translation words succeed exactly when every prefix stays in the capacity box and return the total displacement. -/

import D5.S0.Automata.TypedPartialDFAOOverBase
import Mathlib.Data.List.Infix
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Lean.Elab.Tactic.LibrarySearch

set_option autoImplicit false

namespace D5.S0.Rewriting.TranslationPrefixDomain

open D5.S0.Automata.TypedPartialDFAOOverBase

variable {P : Type*} [Fintype P]

/-- Evaluate integer translation vectors from left to right, checking the initial state
and each successor against the coordinate capacities, and stopping at the first failure. -/
def eval (A : P → ℕ) (word : List (P → ℤ)) (x : P → ℤ) : Option (P → ℤ) :=
  if ∀ p, 0 ≤ x p ∧ x p ≤ (A p : ℤ) then
    runTransition (fun z a =>
      if ∀ p, 0 ≤ (z + a) p ∧ (z + a) p ≤ (A p : ℤ) then some (z + a) else none)
      x word
  else none

/-- A word succeeds at an endpoint exactly when every prefix, including the empty prefix,
stays in the capacity box and the endpoint is the initial state plus the total displacement. -/
theorem eval_eq_some_iff (A : P → ℕ) (word : List (P → ℤ)) (x y : P → ℤ) :
    eval A word x = some y ↔
      (∀ pref ∈ word.inits, ∀ p, 0 ≤ x p + pref.sum p ∧
        x p + pref.sum p ≤ (A p : ℤ)) ∧ y = x + word.sum := by
  induction word generalizing x with
  | nil =>
      by_cases hx : ∀ p, 0 ≤ x p ∧ x p ≤ (A p : ℤ)
      · simp [eval, runTransition, hx, eq_comm]
      · simp [eval, hx]
  | cons a word ih =>
      by_cases hx : ∀ p, 0 ≤ x p ∧ x p ≤ (A p : ℤ)
      · have shift :
            (∀ pref ∈ (a :: word).inits, ∀ p, 0 ≤ x p + pref.sum p ∧
              x p + pref.sum p ≤ (A p : ℤ)) ↔
            (∀ pref ∈ word.inits, ∀ p, 0 ≤ (x + a) p + pref.sum p ∧
              (x + a) p + pref.sum p ≤ (A p : ℤ)) := by
          simp [hx, add_assoc]
        rw [shift]
        by_cases ha : ∀ p, 0 ≤ x p + a p ∧ x p + a p ≤ (A p : ℤ)
        · simpa [eval, runTransition, hx, ha, add_assoc] using ih (x + a)
        · have invalid : ¬ (∀ pref ∈ word.inits, ∀ p,
                0 ≤ (x + a) p + pref.sum p ∧
                (x + a) p + pref.sum p ≤ (A p : ℤ)) := by
            intro hall
            apply ha
            simpa using hall [] (by simp)
          have hnone : eval A (a :: word) x = none := by
            simp [eval, runTransition, hx, ha]
          rw [hnone]
          exact iff_of_false (by simp) (fun h => invalid h.1)
      · simp [eval, hx]

end D5.S0.Rewriting.TranslationPrefixDomain
