/- GID: D5/S3/Geometry/Hyperideal/CoupledAngleBound
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/CoupledAngleBound
   mirror-E: none(waiver:coupled-angle-ratio-bound)
   anchors: []
   utility: none
   digest: A strict scalar ratio bound underlying the mixed-matching coupled-angle estimate. -/

/-
proof_shape: coupled_ratio_lt_half_angle: content
admission_basis: escape-witness.
escape_witness: gap_factorization, the strict factorized gap is derived from the
continuous hypotheses and is not an instance of an imported theorem.
Escape audit unfinished: issue #10609 tracks the missing faithful four-slot
registration for the paired hyperideal angle-response family; this scalar
coupled-angle theorem has no declared_validated Reg mirror yet.
-/

import Mathlib.Tactic

/-! A strict scalar estimate for the mixed-matching angle calculation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Geometry.Hyperideal.CoupledAngleBound

/-- The scalar expression appearing in the squared coupled-angle estimate. -/
def coupledRatio (Q T k : ℝ) : ℝ :=
  ((Q + T ^ 2) * k) / (2 * (T ^ 2 - 1) + (Q + 1) * k)

private theorem gap_factorization (Q T k : ℝ) :
    (2 * (T ^ 2 - 1) + (Q + 1) * k) -
        (Q + T ^ 2) * (2 - k) =
      k * T ^ 2 + 2 * Q * (k - 1) + k - 2 := by
  ring

/-- The coupled ratio is strictly below the half-angle rational bound. -/
theorem coupled_ratio_lt_half_angle {Q T k : ℝ}
    (hk_pos : 0 < k) (hk_lt_one : k < 1)
    (hQ : (2 - k) / k < Q) (hT : Q ≤ T) :
    coupledRatio Q T k < k / (2 - k) := by
  have hk_two : 0 < 2 - k := by linarith
  have hQ_threshold : 1 < (2 - k) / k := by
    apply (lt_div_iff₀ hk_pos).2
    nlinarith
  have hQ_pos : 0 < Q := by linarith
  have hQ_plus : 0 < Q + 1 := by linarith
  have hT_one : 1 < T := by
    have : 1 < Q := lt_trans hQ_threshold hQ
    linarith
  have hT_sq_ge : Q ^ 2 ≤ T ^ 2 := by
    have hprod : 0 ≤ (T - Q) * (T + Q) := by
      apply mul_nonneg
      · exact sub_nonneg.mpr hT
      · linarith
    nlinarith
  have hbase :
      0 < k * Q ^ 2 + 2 * Q * (k - 1) + k - 2 := by
    have hfactor :
        k * Q ^ 2 + 2 * Q * (k - 1) + k - 2 =
          (k * Q - (2 - k)) * (Q + 1) := by
      ring
    rw [hfactor]
    have hfactor_pos : 0 < k * Q - (2 - k) := by
      have hmul := (div_lt_iff₀ hk_pos).mp hQ
      nlinarith [hmul]
    exact mul_pos hfactor_pos hQ_plus
  have hscaled : 0 ≤ k * (T ^ 2 - Q ^ 2) := by
    exact mul_nonneg hk_pos.le (sub_nonneg.mpr hT_sq_ge)
  have hgap :
      0 < k * T ^ 2 + 2 * Q * (k - 1) + k - 2 := by
    nlinarith
  have hT_sq_one : 1 < T ^ 2 := by
    nlinarith [sq_nonneg (T - 1)]
  have hden_pos : 0 < 2 * (T ^ 2 - 1) + (Q + 1) * k := by
    have hfirst : 0 < 2 * (T ^ 2 - 1) := by linarith
    have hsecond : 0 < (Q + 1) * k := mul_pos hQ_plus hk_pos
    linarith
  have hcross :
      (Q + T ^ 2) * k * (2 - k) <
        k * (2 * (T ^ 2 - 1) + (Q + 1) * k) := by
    have hmul :
        0 < k * ((2 * (T ^ 2 - 1) + (Q + 1) * k) -
          (Q + T ^ 2) * (2 - k)) := by
      rw [gap_factorization]
      exact mul_pos hk_pos hgap
    nlinarith
  rw [coupledRatio]
  exact (div_lt_div_iff₀ hden_pos hk_two).2 hcross

#print axioms coupled_ratio_lt_half_angle

end D5.S3.Geometry.Hyperideal.CoupledAngleBound

