/- GID: D5/S1/Digit/Infinite/WindowSuccessorGraph
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/WindowSuccessorGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite legal digit windows have an increment cycle with one additional reset edge and exact successor locality. -/

import D5.S1.Digit.Infinite.MultiplierObstruction
import D5.S1.Digit.Infinite.InfiniteSuccessorFibres
import D5.S1.Digit.Carry.SuccessorShortest
import Mathlib.Data.Set.Card

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.WindowSuccessorGraph

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.InfiniteSuccessorFibres
open D5.S1.Digit.Infinite.MultiplierObstruction
open D5.S1.Digit.GoldenBase4AutomataOracle
open D5.S1.Digit

/-- Binary words of length L with no adjacent occupied positions. -/
def X (L : ℕ) := {p : Fin L → Bool // ∀ (j : ℕ) (h : j + 1 < L),
  ¬ (p ⟨j, by omega⟩ = true ∧ p ⟨j + 1, h⟩ = true)}

/-- Truncation of an infinite legal digit stream to its first L positions. -/
def P (L : ℕ) (x : LegalDigits) : X L :=
  ⟨fun i => x.val i, fun j _ => x.property j⟩

/-- The sum of a word's occupied Fibonacci weights. -/
def V {L : ℕ} (p : X L) : ℕ :=
  ∑ i : Fin L, Nat.fib (i.val + 2) * (if p.val i then 1 else 0)

/-- The number of legal binary words of length L. -/
def G (L : ℕ) : ℕ := Nat.fib (L + 2)

/-- The value of the branching window for positive L. -/
def beta (L : ℕ) : ℕ := Nat.fib (L + 1) - 1

/-- The adjacent-zero successor as a self-map of legal digit streams. -/
noncomputable def T (x : LegalDigits) : LegalDigits := ⟨next x.val, next_fibres.1 x⟩

/-- Pairs of windows observed before and after one successor step. -/
def R (L : ℕ) (p q : X L) : Prop := ∃ x, P L x = p ∧ P L (T x) = q

set_option maxHeartbeats 800000 in
/-- In Fibonacci coordinates the window graph is the increment cycle with one additional reset.
Every edge occurs on a natural digit row. Successor windows depend uniquely on one extra digit,
and cannot depend on the original window alone. Iterating h times requires only h extra digits. -/
theorem window_successor_graph (L : ℕ) (hL : 1 ≤ L) :
    (∀ s t : ℕ, (∃ x : LegalDigits, V (P L x) = s ∧ V (P L (T x)) = t) ↔
      ((s < G L - 1 ∧ t = s + 1) ∨ (s = G L - 1 ∧ t = 0) ∨
        (s = beta L ∧ t = 0))) ∧
    (∀ p q : X L, R L p q → ∃ n : ℕ,
      P L (zRow n) = p ∧ P L (T (zRow n)) = q) ∧
    (∃! g : X (L+1) → X L, ∀ x, P L (T x) = g (P (L+1) x)) ∧
    (¬ ∃ f : X L → X L, ∀ n : ℕ, P L (T (zRow n)) = f (P L (zRow n))) ∧
    (∀ s < G L,
      Set.ncard {t : ℕ | ∃ x : LegalDigits, V (P L x) = s ∧ V (P L (T x)) = t} =
        (if s = beta L then 2 else 1)) ∧
    (∀ t < G L,
      Set.ncard {s : ℕ | ∃ x : LegalDigits, V (P L x) = s ∧ V (P L (T x)) = t} =
        (if t = 0 then 2 else 1)) ∧
    (∀ h : ℕ, ∀ x y : LegalDigits, P (L+h) x = P (L+h) y →
      P L (T^[h] x) = P L (T^[h] y)) := by
  classical
  sorry

end D5.S1.Digit.Infinite.WindowSuccessorGraph
