/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates
   generality: I
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every supported OperationOmega coordinate is the grouped legal digit series. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge
import D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates

open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderBridge
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth (window_shift original_t_shift)
open Filter Topology

/-- The bounded affine coordinates of an arbitrary original source equal the
series of the same grouped legal digit stream at every deletion time. -/
theorem operation_coordinate_bridge (a : ℕ → CLabel) (x : ℕ → ℝ)
    (h : OperationOmega a x) :
    ∃ d : LegalDigits,
      (∀ p, window d p = labelWindow (a p)) ∧
      (∀ p, x p = kappa (bitShift d (3 * p))) ∧
      (OperationFiniteSource a ↔ finiteTail d) := by
  obtain ⟨d, path, hzero, hedges, hw, hguard, hs, hr⟩ := operation_digit_bridge a x h
  have ht : 0 < t := inv_pos.mpr Real.goldenRatio_pos
  have ht1 : t < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hg : 0 < g := pow_pos ht 3
  have hg1 : g < 1 := pow_lt_one₀ ht.le ht1 (by decide)
  have hshift (p : ℕ) : originalT (bitShift d (3 * p)) = bitShift d (3 * (p + 1)) := by
    exact original_t_shift d p
  have hwindow (p : ℕ) : window (bitShift d (3 * p)) 0 = labelWindow (a p) := by
    exact (window_shift d p).trans (hw p)
  have hk (p : ℕ) : kappa (bitShift d (3 * p)) =
      branch (labelWindow (a p)) (kappa (bitShift d (3 * (p + 1)))) := by
    have hh := (closed_observation_graph_realization.2.2.1 (bitShift d (3 * p))).1
    simpa only [hshift, hwindow] using hh
  have bounded (p : ℕ) : |x p - kappa (bitShift d (3 * p))| ≤ 4 := by
    have hx := hs p
    have hy : kappa (bitShift d (3 * p)) ∈ stateInterval false :=
      closed_observation_graph_realization.2.1 false ▸
        ⟨bitShift d (3 * p), by simp [stateAddress], rfl⟩
    have hxhi : x p ≤ 1 + t := by
      cases hp : guardBool (path p) <;> simp [hp, stateInterval] at hx <;> linarith [hx.2]
    have hxlo : -1 ≤ x p := hx.1
    change -1 ≤ kappa (bitShift d (3 * p)) ∧
      kappa (bitShift d (3 * p)) ≤ 1 + t at hy
    exact abs_le.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have difference (n p : ℕ) : x p - kappa (bitShift d (3 * p)) =
      (-g) ^ n * (x (p + n) - kappa (bitShift d (3 * (p + n)))) := by
    induction n generalizing p with
    | zero => simp
    | succ n ih =>
      calc
        x p - kappa (bitShift d (3 * p)) =
            -g * (x (p + 1) - kappa (bitShift d (3 * (p + 1)))) := by
          rw [hr p, hk p]
          dsimp [branch]
          ring
        _ = (-g) ^ (n + 1) *
            (x (p + (n + 1)) - kappa (bitShift d (3 * (p + (n + 1))))) := by
          rw [ih]
          simp only [pow_succ]
          rw [show p + 1 + n = p + (n + 1) by omega]
          ring
  refine ⟨d, hw, ?_, operation_finite_source_iff_of_bridge a d hw⟩
  intro p
  have hz : Tendsto (fun _ : ℕ => x p - kappa (bitShift d (3 * p))) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hg.le hg1).mul_const 4)
    rw [Real.norm_eq_abs, difference n p, abs_mul, abs_pow, abs_neg, abs_of_pos hg]
    exact mul_le_mul_of_nonneg_left (bounded (p + n)) (pow_nonneg hg.le n)
  exact sub_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hz)

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OnlineDecoderCoordinates
