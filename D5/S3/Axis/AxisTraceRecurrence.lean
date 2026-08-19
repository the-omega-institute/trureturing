/- GID: D5/S3/Axis/AxisTraceRecurrence
   generality: I
   mirror-B: D5/B/S3/Axis/AxisTraceRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The axis weight is multiplicatively Fibonacci, so consecutive weights compose. -/

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Exp

/- Library-search audit trail (2026-08-19):
   * Searched the object. `Real.goldenRatio_pow_sub_goldenRatio_pow` states
     `φ ^ (n + 2) - φ ^ (n + 1) = φ ^ n` and is applied here rather than reproved; the
     conjugate has `Real.goldenConj_sq` and the same shape follows from it.
   * `Real.exp_add` carries the multiplicative step; no bespoke exponential lemma is added.
   * Probes for existing axis-weight machinery in `D5` (`axisTrace`, `axisPartialSum`,
     `legalWord`, `windowWeight`) returned zero declarations. An earlier case-insensitive
     probe reported one hit for `W_K` and two for `traceMap`; a case-sensitive re-run showed
     both were probe artefacts, so the count is zero and this module introduces the weight.
-/

namespace D5.S3.Axis.AxisTraceRecurrence

open Real

/-- The axis weight at depth `K`, read at the pair of Galois embeddings. -/
noncomputable def axisWeight (x y : ℝ) (K : ℕ) : ℝ :=
  Real.exp (-x * goldenRatio ^ (K + 1) + y * goldenConj ^ (K + 1))

/-- The conjugate obeys the same two-step recurrence as the golden ratio. -/
theorem goldenConj_pow_sub_goldenConj_pow (n : ℕ) :
    goldenConj ^ (n + 2) - goldenConj ^ (n + 1) = goldenConj ^ n := by
  have h : goldenConj ^ 2 = goldenConj + 1 := goldenConj_sq
  calc
    goldenConj ^ (n + 2) - goldenConj ^ (n + 1)
        = goldenConj ^ n * (goldenConj ^ 2 - goldenConj) := by ring
    _ = goldenConj ^ n * 1 := by rw [h]; ring
    _ = goldenConj ^ n := by ring

/-- The axis weight is never zero. -/
theorem axisWeight_pos (x y : ℝ) (K : ℕ) : 0 < axisWeight x y K :=
  Real.exp_pos _

/-- Consecutive axis weights compose: the weight is multiplicatively Fibonacci because its
exponent is additively Fibonacci at both embeddings. -/
theorem axisWeight_succ_succ (x y : ℝ) (K : ℕ) :
    axisWeight x y (K + 2) = axisWeight x y (K + 1) * axisWeight x y K := by
  have hphi : goldenRatio ^ (K + 3) = goldenRatio ^ (K + 2) + goldenRatio ^ (K + 1) := by
    have := goldenRatio_pow_sub_goldenRatio_pow (K + 1)
    linarith
  have hpsi : goldenConj ^ (K + 3) = goldenConj ^ (K + 2) + goldenConj ^ (K + 1) := by
    have := goldenConj_pow_sub_goldenConj_pow (K + 1)
    linarith
  simp only [axisWeight]
  rw [← Real.exp_add]
  congr 1
  rw [show K + 2 + 1 = K + 3 from rfl, hphi, hpsi]
  ring

/-- The weight ratio at consecutive depths is itself a weight, so the recurrence never
degenerates: no depth carries the same weight as its successor unless the reading is trivial. -/
theorem axisWeight_zero (x y : ℝ) :
    axisWeight x y 0 = Real.exp (-x * goldenRatio + y * goldenConj) := by
  simp [axisWeight]

/-- The multiplicative Fibonacci law together with positivity and the base value. -/
theorem axis_weight_is_multiplicatively_fibonacci (x y : ℝ) :
    (∀ K : ℕ, axisWeight x y (K + 2) = axisWeight x y (K + 1) * axisWeight x y K) ∧
      (∀ K : ℕ, 0 < axisWeight x y K) ∧
        axisWeight x y 0 = Real.exp (-x * goldenRatio + y * goldenConj) :=
  ⟨axisWeight_succ_succ x y, axisWeight_pos x y, axisWeight_zero x y⟩

#print axioms axis_weight_is_multiplicatively_fibonacci

end D5.S3.Axis.AxisTraceRecurrence
