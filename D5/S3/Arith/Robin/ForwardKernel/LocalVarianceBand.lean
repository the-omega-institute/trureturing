/- GID: D5/S3/Arith/Robin/ForwardKernel/LocalVarianceBand
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/LocalVarianceBand
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cumulative variance errors bound local square integrals and retain interval length. -/

import D5.S3.Arith.Robin.ForwardKernel.MacroscopicVarianceDefs
import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer
import D5.S3.Arith.Robin.ForwardKernel.MovingEndpointVariance
import D5.S3.Quantum.Schatten.PowerMajorization

/-! A comparable window of cumulative variance estimates controls every subinterval. -/

namespace D5.S3.Arith.Robin.ForwardKernel.LocalVarianceBand

open Set MeasureTheory Filter
open VarianceTransferDefs MacroscopicVarianceDefs

noncomputable section

variable {E : ℝ → ℝ} {α θ β : ℝ}

/-- Uniform band asymptotics hold throughout every sufficiently large comparable window. -/
theorem variance_window_eventually
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop, VarianceWindowBound E α β X ε := by
  intro ε hε
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1 (hV ε hε)
  filter_upwards [eventually_ge_atTop (2 * Y₀)] with X hX
  intro Y hY v hvα hvβ
  exact hY₀ Y (by linarith [hY.1]) v hvα hvβ

/-- Local variance on a subinterval retains its length in the main term. -/
theorem local_variance_bound (hE : LocallyBoundedMeasurable E)
    (hB : ValidBand α θ β)
    {X A B R ε : ℝ} (hX : 4 ≤ X) (hR : 0 < R) (hε : 0 ≤ ε)
    (hA : X / 2 ≤ A) (hAB : A ≤ B) (hB4 : B ≤ 4 * X)
    (hlo : (4 * X) ^ α ≤ R) (hhi : 4 * R ≤ (X / 2) ^ β)
    (hV : VarianceWindowBound E α β X ε) :
    ∀ v ∈ Icc R (4 * R),
      (∫ y in A..B, increment E v y ^ 2) ≤
        v * Real.log X * (3 * (B - A) + 16 * ε * X) := by
  intro v hv
  have hX0 : 0 < X := by linarith
  have hv0 : 0 < v := hR.trans_le hv.1
  have hA1 : 1 < A := by linarith
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := hA0.trans_le hAB
  have hβ0 : 0 ≤ β := (hB.1.trans (hB.2.1.trans hB.2.2.1)).le
  have band (Y : ℝ) (hY : Y ∈ Icc (X / 2) (4 * X)) :
      Y ^ α ≤ v ∧ v ≤ Y ^ β := by
    constructor
    · exact (Real.rpow_le_rpow (by linarith [hY.1]) hY.2 hB.1.le).trans
        (hlo.trans hv.1)
    · exact (hv.2.trans hhi).trans
        (Real.rpow_le_rpow (by linarith) hY.1 hβ0)
  have hAmem : A ∈ Icc (X / 2) (4 * X) := ⟨hA, hAB.trans hB4⟩
  have hBmem : B ∈ Icc (X / 2) (4 * X) := ⟨hA.trans hAB, hB4⟩
  have hv1 : 1 ≤ v :=
    (Real.one_le_rpow hA1.le hB.1.le).trans (band A hAmem).1
  have hvA : v < A := by
    calc
      v ≤ A ^ β := (band A hAmem).2
      _ < A ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hA1 hB.2.2.2
      _ = A := Real.rpow_one _
  have logpos (Y : ℝ) (hY : A ≤ Y) : 0 < Real.log (Y / v) :=
    Real.log_pos ((one_lt_div hv0).2 (hvA.trans_le hY))
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlog4 : Real.log (4 : ℝ) ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have hlogX1 : 1 ≤ Real.log X := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] at hlog4
    norm_num only [Nat.cast_ofNat] at hlog4
    linarith [Real.log_two_gt_d9]
  have hlog4X : Real.log (4 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    linarith
  have logupper (Y : ℝ) (hY0 : 0 < Y) (hY4 : Y ≤ 4 * X) :
      Real.log (Y / v) ≤ 2 * Real.log X := by
    exact (Real.log_le_log (div_pos hY0 hv0)
      ((div_le_self hY0.le hv1).trans hY4)).trans hlog4X
  have hmain : B * Real.log (B / v) - A * Real.log (A / v) ≤
      3 * (B - A) * Real.log X := by
    have hlogBA := sub_ge_mul_log_div hA0 hB0
    rw [Real.log_div hB0.ne' hA0.ne'] at hlogBA
    rw [Real.log_div hB0.ne' hv0.ne', Real.log_div hA0.ne' hv0.ne']
    have hlogB := logupper B hB0 hB4
    rw [Real.log_div hB0.ne' hv0.ne'] at hlogB
    have hmul := mul_le_mul_of_nonneg_left hlogB (sub_nonneg.mpr hAB)
    nlinarith [mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hlogX1)]
  have herr : B * Real.log (B / v) + A * Real.log (A / v) ≤
      16 * X * Real.log X := by
    have hb := mul_le_mul_of_nonneg_left (logupper B hB0 hB4) hB0.le
    have ha := mul_le_mul_of_nonneg_left (logupper A hA0 hAmem.2) hA0.le
    have hs := mul_le_mul_of_nonneg_right
      (show A + B ≤ 8 * X by linarith) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlogX0)
    nlinarith
  have estimate (Y : ℝ) (hY : Y ∈ Icc (X / 2) (4 * X)) (hAY : A ≤ Y) :
      |cumulativeVariance E Y v - Y * v * Real.log (Y / v)| ≤
        ε * (Y * v * Real.log (Y / v)) := by
    have hd : 0 < Y * v * Real.log (Y / v) :=
      mul_pos (mul_pos (hA0.trans_le hAY) hv0) (logpos Y hAY)
    have hh := (hV Y hY v (band Y hY).1 (band Y hY).2)
    have heq : cumulativeVariance E Y v / (Y * v * Real.log (Y / v)) - 1 =
        (cumulativeVariance E Y v - Y * v * Real.log (Y / v)) /
          (Y * v * Real.log (Y / v)) := by
      field_simp [hv0.ne', (hA0.trans_le hAY).ne', (logpos Y hAY).ne']
    rw [heq, abs_div, abs_of_pos hd] at hh
    exact (div_le_iff₀ hd).1 hh
  have hEA := (abs_le.1 (estimate A hAmem le_rfl)).1
  have hEB := (abs_le.1 (estimate B hBmem hAB)).2
  have hi (Y : ℝ) : IntervalIntegrable (fun y => increment E v y ^ 2) volume 1 Y := by
    apply (VarianceTransfer.increment_product_comp_integrableOn (μ := volume) hE
      isCompact_uIcc (u := fun _ => v) (x := fun y => y)
      (v := fun _ => v) (y := fun y => y)
      continuous_const continuous_id continuous_const continuous_id).intervalIntegrable.congr
    intro y _
    exact (pow_two _).symm
  have hid : (∫ y in A..B, increment E v y ^ 2) =
      cumulativeVariance E B v - cumulativeVariance E A v :=
    (intervalIntegral.integral_interval_sub_left (hi B) (hi A)).symm
  rw [hid]
  have hm := mul_le_mul_of_nonneg_left hmain hv0.le
  have he := mul_le_mul_of_nonneg_left herr (mul_nonneg hε hv0.le)
  nlinarith

/-- The local variance estimate controls two moving endpoints with a signed gap. -/
theorem local_endpoint_bound (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    {p q p' q' : ℝ → ℝ} {l r A B R m X ε : ℝ}
    (hlr : l ≤ r) (hAB : A ≤ B) (hR : 0 < R) (hm : 0 < m)
    (hX : 4 ≤ X) (hε : 0 ≤ ε) (hA : X / 2 ≤ A) (hB4 : B ≤ 4 * X)
    (hlo : (4 * X) ^ α ≤ R) (hhi : 4 * R ≤ (X / 2) ^ β)
    (hV : VarianceWindowBound E α β X ε)
    (hp : ContinuousOn p (Icc l r)) (hq : ContinuousOn q (Icc l r))
    (hdp : ∀ x ∈ Icc l r, HasDerivWithinAt p (p' x) (Icc l r) x)
    (hdq : ∀ x ∈ Icc l r, HasDerivWithinAt q (q' x) (Icc l r) x)
    (hlower : ∀ x ∈ Icc l r, m ≤ p' x ∧ m ≤ q' x)
    (himage : ∀ x ∈ Icc l r, p x ∈ Icc A B ∧ q x ∈ Icc A B)
    (hgap : ∀ x ∈ Icc l r, |q x - p x| ≤ R) :
    (∫ x in l..r, (E (q x) - E (p x)) ^ 2) ≤
      (20 * R / m) * Real.log X * (3 * (B - A) + 16 * ε * X) := by
  have hC : 0 ≤ Real.log X * (3 * (B - A) + 16 * ε * X) := by
    have : 0 ≤ X := by linarith
    exact mul_nonneg (Real.log_nonneg (by linarith)) (by positivity)
  have hv := local_variance_bound hE hB hX hR hε hA hAB hB4 hlo hhi hV
  have hh := MovingEndpointVariance.local_two_endpoint_increment_square_le hE
    hlr hAB hR hC hm hp hq hdp hdq hlower himage hgap (by
      intro v hv'
      convert hv v hv' using 1 <;> ring)
  convert hh using 1 <;> ring

end

end D5.S3.Arith.Robin.ForwardKernel.LocalVarianceBand
