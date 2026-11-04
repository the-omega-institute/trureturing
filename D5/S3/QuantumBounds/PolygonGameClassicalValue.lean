/- GID: D5/S3/QuantumBounds/PolygonGameClassicalValue
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/PolygonGameClassicalValue
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The odd polygon game's classical value is one minus its Fibonacci loss fraction. -/

import D5.S1.Words.AdmissibleWords.AdmissibleCount
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-! The uniform-input polygon game, with arbitrary local deterministic response tables. -/

noncomputable section

open scoped BigOperators Classical

namespace D5.S3.QuantumBounds.PolygonGameClassicalValue

/-- Edge `i` joins player `i` to `finRotate P i`. -/
def IsMatching (P : ℕ) (M : Finset (Fin P)) : Prop :=
  ∀ i ∈ M, finRotate P i ∉ M

/-- The input is true exactly at endpoints of matching edges. -/
def matchingInput (P : ℕ) (M : Finset (Fin P)) : Fin P → Bool :=
  fun i => decide (i ∈ M ∨ (finRotate P).symm i ∈ M)

/-- Even local triples, even middle parity, and the source matching rule. -/
def wins (P : ℕ) (s : Fin P → Bool → Bool × Bool × Bool) (x : Fin P → Bool) : Prop :=
  (∀ i, ((s i (x i)).1.toNat + (s i (x i)).2.1.toNat +
    (s i (x i)).2.2.toNat : ZMod 2) = 0) ∧
  (∑ i, ((s i (x i)).2.1.toNat : ZMod 2)) = 0 ∧
  ∀ M : Finset (Fin P), IsMatching P M → matchingInput P M = x →
    (∑ i ∈ M, ((s i true).1.toNat + (s (finRotate P i) true).2.2.toNat : ZMod 2)) +
      (∑ i ∈ Finset.univ.filter (fun i => matchingInput P M i = false),
        ((s i false).1.toNat : ZMod 2)) = (M.card : ZMod 2)

/-- Shared randomness is a probability weight on all local deterministic response tables. -/
def winProbability (P : ℕ) (μ : (Fin P → Bool → Bool × Bool × Bool) → ℝ) : ℝ := by
  classical
  exact ∑ s, μ s * ((Finset.univ.filter (wins P s)).card : ℝ) / 2 ^ P

/-- The classical upper bound and deterministic attainment, for every odd polygon. -/
def claim : Prop := by
  classical
  exact ∀ P : ℕ, Odd P → 3 ≤ P →
    (∀ μ : (Fin P → Bool → Bool × Bool × Bool) → ℝ,
      (∀ s, 0 ≤ μ s) → ∑ s, μ s = 1 →
      winProbability P μ ≤ 1 - (Nat.fib (P - 1) : ℝ) / 2 ^ P) ∧
    ∃ s : Fin P → Bool → Bool × Bool × Bool,
      ((Finset.univ.filter (wins P s)).card : ℝ) / 2 ^ P =
        1 - (Nat.fib (P - 1) : ℝ) / 2 ^ P

private def locallyLegal (P : ℕ) (s : Fin P → Bool → Bool × Bool × Bool) : Prop :=
  ∀ i x, ((s i x).1.toNat + (s i x).2.1.toNat + (s i x).2.2.toNat : ZMod 2) = 0

private def fixedMiddle (P : ℕ) (s : Fin P → Bool → Bool × Bool × Bool) : Prop :=
  ∀ i, (s i false).2.1 = (s i true).2.1

private def baseline (P : ℕ) (s : Fin P → Bool → Bool × Bool × Bool) : ZMod 2 :=
  ∑ i, ((s i false).1.toNat : ZMod 2)

private def edgeCharge (P : ℕ) (s : Fin P → Bool → Bool × Bool × Bool) (i : Fin P) :
    ZMod 2 :=
  1 + ((s i false).1.toNat : ZMod 2) + (s i true).1.toNat +
    (s (finRotate P i) false).1.toNat + (s (finRotate P i) true).1.toNat +
    (s (finRotate P i) false).2.1.toNat

private def avoiding (P : ℕ) (j : Fin P) : Finset (Finset (Fin P)) := by
  classical
  exact Finset.univ.filter (fun N => IsMatching P N ∧
    (finRotate P).symm j ∉ N ∧ j ∉ N ∧ finRotate P j ∉ N)

private def attainingStrategy (P : ℕ) : Fin P → Bool → Bool × Bool × Bool :=
  fun i x => if i.val + 1 < P then (true, true, false)
    else if x then (true, false, true) else (false, false, false)

private lemma fibonacci_le_half (P : ℕ) (hP : 3 ≤ P) : Nat.fib (P - 1) ≤ 2 ^ (P - 1) := by
  sorry

private lemma local_violation_half (P : ℕ) (hP : 3 ≤ P)
    (s : Fin P → Bool → Bool × Bool × Bool) (h : ¬ locallyLegal P s) :
    2 ^ (P - 1) ≤ (Finset.univ.filter (fun x => ¬ wins P s x)).card := by
  classical
  sorry

private lemma varying_middle_half (P : ℕ) (hP : 3 ≤ P)
    (s : Fin P → Bool → Bool × Bool × Bool) (h : ¬ fixedMiddle P s) :
    2 ^ (P - 1) ≤ (Finset.univ.filter (fun x => ¬ wins P s x)).card := by
  classical
  sorry

private lemma odd_middle_all (P : ℕ) (s : Fin P → Bool → Bool × Bool × Bool)
    (hfixed : fixedMiddle P s)
    (hodd : (∑ i, ((s i false).2.1.toNat : ZMod 2)) ≠ 0) :
    (Finset.univ.filter (fun x => ¬ wins P s x)).card = 2 ^ P := by
  classical
  sorry

private lemma affine_matching_rule (P : ℕ) (s : Fin P → Bool → Bool × Bool × Bool)
    (hlegal : locallyLegal P s) (hfixed : fixedMiddle P s)
    (M : Finset (Fin P)) (hM : IsMatching P M) :
    ((∑ i ∈ M, ((s i true).1.toNat + (s (finRotate P i) true).2.2.toNat : ZMod 2)) +
      (∑ i ∈ Finset.univ.filter (fun i => matchingInput P M i = false),
        ((s i false).1.toNat : ZMod 2)) = (M.card : ZMod 2)) ↔
      baseline P s + ∑ i ∈ M, edgeCharge P s i = 0 := by
  classical
  sorry

private lemma marked_edge (P : ℕ) (hodd : Odd P)
    (s : Fin P → Bool → Bool × Bool × Bool)
    (heven : (∑ i, ((s i false).2.1.toNat : ZMod 2)) = 0) :
    ∃ j : Fin P, edgeCharge P s j = 1 := by
  sorry

private lemma matching_input_injective (P : ℕ) (hodd : Odd P) (hP : 3 ≤ P)
    (M N : Finset (Fin P)) (hM : IsMatching P M) (hN : IsMatching P N)
    (hinput : matchingInput P M = matchingInput P N) : M = N := by
  sorry

private lemma insert_avoiding (P : ℕ) (hP : 3 ≤ P) (j : Fin P)
    (N : Finset (Fin P)) (hN : N ∈ avoiding P j) :
    IsMatching P N ∧ IsMatching P (insert j N) ∧ j ∉ N ∧
      matchingInput P N j = false ∧ matchingInput P (insert j N) j = true := by
  sorry

private lemma avoiding_count (P : ℕ) (hP : 3 ≤ P) (j : Fin P) :
    (avoiding P j).card = Nat.fib (P - 1) := by
  sorry

private lemma pairing_losses (P : ℕ) (hodd : Odd P) (hP : 3 ≤ P)
    (s : Fin P → Bool → Bool × Bool × Bool)
    (hlegal : locallyLegal P s) (hfixed : fixedMiddle P s)
    (j : Fin P) (hj : edgeCharge P s j = 1) :
    (avoiding P j).card ≤ (Finset.univ.filter (fun x => ¬ wins P s x)).card := by
  classical
  sorry

private lemma deterministic_losses (P : ℕ) (hodd : Odd P) (hP : 3 ≤ P)
    (s : Fin P → Bool → Bool × Bool × Bool) :
    Nat.fib (P - 1) ≤ (Finset.univ.filter (fun x => ¬ wins P s x)).card := by
  classical
  by_cases hlegal : locallyLegal P s
  · by_cases hfixed : fixedMiddle P s
    · by_cases heven : (∑ i, ((s i false).2.1.toNat : ZMod 2)) = 0
      · obtain ⟨j, hj⟩ := marked_edge P hodd s heven
        rw [← avoiding_count P hP j]
        exact pairing_losses P hodd hP s hlegal hfixed j hj
      · rw [odd_middle_all P s hfixed heven]
        exact (fibonacci_le_half P hP).trans (Nat.pow_le_pow_right (by decide) (by omega))
    · exact (fibonacci_le_half P hP).trans (varying_middle_half P hP s hfixed)
  · exact (fibonacci_le_half P hP).trans (local_violation_half P hP s hlegal)

private lemma deterministic_bound (P : ℕ) (hodd : Odd P) (hP : 3 ≤ P)
    (s : Fin P → Bool → Bool × Bool × Bool) :
    ((Finset.univ.filter (wins P s)).card : ℝ) / 2 ^ P ≤
      1 - (Nat.fib (P - 1) : ℝ) / 2 ^ P := by
  classical
  have hloss := deterministic_losses P hodd hP s
  sorry

private lemma attaining_charges (P : ℕ) (hodd : Odd P) (hP : 3 ≤ P) :
    locallyLegal P (attainingStrategy P) ∧ fixedMiddle P (attainingStrategy P) ∧
    (∑ i, ((attainingStrategy P i false).2.1.toNat : ZMod 2)) = 0 ∧
    baseline P (attainingStrategy P) = 0 ∧
    ∃ j : Fin P, ∀ i, edgeCharge P (attainingStrategy P) i = if i = j then 1 else 0 := by
  sorry

private lemma attaining_losses (P : ℕ) (hodd : Odd P) (hP : 3 ≤ P) :
    (Finset.univ.filter (fun x => ¬ wins P (attainingStrategy P) x)).card ≤
      Nat.fib (P - 1) := by
  classical
  have hcharges := attaining_charges P hodd hP
  sorry

private lemma attainment (P : ℕ) (hodd : Odd P) (hP : 3 ≤ P) :
    ((Finset.univ.filter (wins P (attainingStrategy P))).card : ℝ) / 2 ^ P =
      1 - (Nat.fib (P - 1) : ℝ) / 2 ^ P := by
  classical
  have hlower := deterministic_losses P hodd hP (attainingStrategy P)
  have hupper := attaining_losses P hodd hP
  sorry

private lemma mixture_bound (P : ℕ) (hodd : Odd P) (hP : 3 ≤ P)
    (μ : (Fin P → Bool → Bool × Bool × Bool) → ℝ)
    (hpos : ∀ s, 0 ≤ μ s) (hnorm : ∑ s, μ s = 1) :
    winProbability P μ ≤ 1 - (Nat.fib (P - 1) : ℝ) / 2 ^ P := by
  classical
  have hbound := deterministic_bound P hodd hP
  sorry

theorem result : claim := by
  classical
  intro P hodd hP
  exact ⟨fun μ hpos hnorm => mixture_bound P hodd hP μ hpos hnorm,
    ⟨attainingStrategy P, attainment P hodd hP⟩⟩

end D5.S3.QuantumBounds.PolygonGameClassicalValue
