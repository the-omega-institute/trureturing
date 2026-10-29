/- GID: D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/PureState/OverlapIntervalPropagationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.claim; result=D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.result; claim=D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.claim
   digest: Five pure-state overlaps force a sixth beyond three-state interval propagation. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Notation
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Nlinarith

/-! The one-unknown-edge procedure can miss the exact feasible lower endpoint. -/

set_option autoImplicit false

namespace D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation

open scoped InnerProductSpace Matrix

noncomputable section

/-- The three-pure-state upper bound of Galvão and Brod. -/
def upper (x y : ℝ) : ℝ :=
  (Real.sqrt (x * y) + Real.sqrt ((1 - x) * (1 - y))) ^ 2

/-- The lower bound is zero when the two known overlaps sum to at most one. -/
def lower (x y : ℝ) : ℝ :=
  if 1 < x + y then (Real.sqrt (x * y) - Real.sqrt ((1 - x) * (1 - y))) ^ 2 else 0

/-- Squared overlap of two pure-state vectors. -/
def overlap {n : ℕ} (u v : EuclideanSpace ℂ (Fin n)) : ℝ := ‖inner ℂ u v‖ ^ 2

/-- Unit vectors realizing every given edge except the unordered unknown pair. -/
def realizes {n N : ℕ} (i₀ j₀ : Fin N) (r : Fin N → Fin N → ℝ)
    (ψ : Fin N → EuclideanSpace ℂ (Fin n)) : Prop :=
  (∀ k, ‖ψ k‖ = 1) ∧ ∀ i j, i ≠ j →
    ({i, j} : Finset (Fin N)) ≠ {i₀, j₀} → overlap (ψ i) (ψ j) = r i j

/-- Feasible values of the unknown overlap, allowing every finite dimension. -/
def feasible (N : ℕ) (i₀ j₀ : Fin N) (r : Fin N → Fin N → ℝ) : Set ℝ :=
  {t | ∃ (n : ℕ) (ψ : Fin N → EuclideanSpace ℂ (Fin n)),
    realizes i₀ j₀ r ψ ∧ t = overlap (ψ i₀) (ψ j₀)}

/-- Maximum of all common-neighbour lower bounds; the finite set is nonempty for `3 ≤ N`. -/
def procLower (N : ℕ) (i₀ j₀ : Fin N) (r : Fin N → Fin N → ℝ) : ℝ :=
  sSup {t | ∃ k : Fin N, k ≠ i₀ ∧ k ≠ j₀ ∧ t = lower (r k i₀) (r k j₀)}

/-- Minimum of all common-neighbour upper bounds. -/
def procUpper (N : ℕ) (i₀ j₀ : Fin N) (r : Fin N → Fin N → ℝ) : ℝ :=
  sInf {t | ∃ k : Fin N, k ≠ i₀ ∧ k ≠ j₀ ∧ t = upper (r k i₀) (r k j₀)}

/-- Tightness of interval propagation for every realizable one-unknown-edge instance. -/
def claim : Prop :=
  ∀ (N : ℕ) (i₀ j₀ : Fin N) (r : Fin N → Fin N → ℝ), 3 ≤ N → i₀ ≠ j₀ →
    (feasible N i₀ j₀ r).Nonempty →
    procLower N i₀ j₀ r = sInf (feasible N i₀ j₀ r) ∧
      procUpper N i₀ j₀ r = sSup (feasible N i₀ j₀ r)

private def givenOverlaps : Fin 4 → Fin 4 → ℝ :=
  ![![1, 0, 1 / 2, 1 / 2], ![0, 1, 1 / 2, 0],
    ![1 / 2, 1 / 2, 1, 0], ![1 / 2, 0, 0, 1]]

private def witness : Fin 4 → EuclideanSpace ℂ (Fin 3) :=
  ![WithLp.toLp 2 ![1, 0, 0], WithLp.toLp 2 ![0, 1, 0],
    WithLp.toLp 2 ![(Real.sqrt (1 / 2) : ℂ), (Real.sqrt (1 / 2) : ℂ), 0],
    WithLp.toLp 2 ![(Real.sqrt (1 / 2) : ℂ), 0, (Real.sqrt (1 / 2) : ℂ)]]

private lemma lower_half_half : lower (1 / 2) (1 / 2) = 0 := by
  sorry

private lemma lower_half_zero : lower (1 / 2) 0 = 0 := by
  sorry

private lemma instance_lower : procLower 4 2 3 givenOverlaps = 0 := by
  sorry

private lemma witness_realizes : realizes 2 3 givenOverlaps witness := by
  sorry

private lemma span_saturation {n : ℕ} (a b c : EuclideanSpace ℂ (Fin n))
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hab : overlap a b = 0) (hac : overlap a c = 1 / 2)
    (hbc : overlap b c = 1 / 2) :
    c = (inner ℂ a c) • a + (inner ℂ b c) • b := by
  sorry

private lemma forced_overlap {n : ℕ} (ψ : Fin 4 → EuclideanSpace ℂ (Fin n))
    (hψ : realizes 2 3 givenOverlaps ψ) : overlap (ψ 2) (ψ 3) = 1 / 4 := by
  sorry

private lemma feasible_nonempty : (feasible 4 2 3 givenOverlaps).Nonempty := by
  exact ⟨overlap (witness 2) (witness 3), 3, witness, witness_realizes, rfl⟩

private lemma feasible_singleton : feasible 4 2 3 givenOverlaps = {1 / 4} := by
  sorry

private lemma instance_infimum : sInf (feasible 4 2 3 givenOverlaps) = 1 / 4 := by
  rw [feasible_singleton, csInf_singleton]

/-- Three-state interval propagation is not always tight for four pure states. -/
theorem result : ¬ claim := by
  intro h
  have hbound := (h 4 2 3 givenOverlaps (by norm_num) (by decide) feasible_nonempty).1
  rw [instance_lower, instance_infimum] at hbound
  norm_num at hbound

end

end D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation
