/- GID: D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Variable-length integrable profile averages are measurable and square integrable. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer

/-! Regularity of profile averages when their length varies with the starting point. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MovingLengthRegularity

open Set MeasureTheory Filter
open VarianceTransferDefs VarianceTransfer

noncomputable section

/-- Measurable lengths give measurable profile averages. -/
theorem profileAverage_variable_measurable {E g H : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g)
    (hH : Measurable H) :
    Measurable (fun x => profileAverage E g (H x) x) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      g p.2 * increment E (p.2 * H p.1) p.1) :=
    (hg.1.comp measurable_snd).mul
      ((hE.1.comp (measurable_fst.add
        (measurable_snd.mul (hH.comp measurable_fst)))).sub
          (hE.1.comp measurable_fst))
  simp_rw [profileAverage_eq_unit_integral,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := unitMeasure)).measurable.div hH

/-- Lengths bounded above and away from zero give locally square-integrable profile averages. -/
theorem profileAverage_variable_memLp {E g H : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g)
    (hH : Measurable H)
    {a b l L : ℝ} (hab : a ≤ b) (hl : 0 < l)
    (hbound : ∀ x ∈ Icc a b, H x ∈ Icc l L) :
    MemLp (fun x => profileAverage E g (H x) x) 2 (volume.restrict (Ioc a b)) := by
  have hL : 0 < L := (hl.trans_le (hbound a ⟨le_rfl, hab⟩).1).trans_le
    (hbound a ⟨le_rfl, hab⟩).2
  obtain ⟨M, hM, hMb⟩ := hE.2 a (b + L)
  apply MemLp.of_bound
    (profileAverage_variable_measurable hE hg hH).aestronglyMeasurable
    (profileL1 g * (2 * M) / l)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2⟩
  obtain ⟨hlo, hup⟩ := hbound x hx'
  have hp : 0 < H x := hl.trans_le hlo
  have hb : ‖∫ s, g s * increment E (s * H x) x ∂unitMeasure‖ ≤
      profileL1 g * (2 * M) := by
    have hh : ∀ᵐ s ∂unitMeasure,
        ‖g s * increment E (s * H x) x‖ ≤ |g s| * (2 * M) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hxE := hMb x ⟨hx.1.le, by linarith [hx.2]⟩
      have hxu := hMb (x + s * H x)
        ⟨le_trans hx.1.le (le_add_of_nonneg_right (mul_nonneg hs.1.le hp.le)),
        add_le_add hx.2 ((mul_le_of_le_one_left hp.le hs.2).trans hup)⟩
      simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith)) (abs_nonneg _)
    simpa only [integral_mul_const, profileL1] using
      norm_integral_le_of_norm_le (hg.2.abs.mul_const (2 * M)) hh
  rw [profileAverage_eq_unit_integral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    norm_div]
  simp only [Real.norm_eq_abs, abs_of_pos hp] at hb ⊢
  exact (div_le_div_of_nonneg_right hb hp.le).trans
    (div_le_div_of_nonneg_left
      (mul_nonneg (integral_nonneg (fun s => abs_nonneg (g s))) (by positivity)) hl hlo)

lemma step_integrable {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (x a b : ℝ) : IntervalIntegrable (fun u => increment E u x) volume a b :=
  (increment_comp_integrableOn hE isCompact_uIcc continuous_id continuous_const).intervalIntegrable

lemma step_sq_integrable {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (x a b : ℝ) : IntervalIntegrable (fun u => increment E u x ^ 2) volume a b := by
  simpa only [pow_two, Pi.mul_apply] using
    (increment_product_comp_integrableOn hE isCompact_uIcc
      (show Continuous (fun u : ℝ => u) from continuous_id)
      (show Continuous (fun _ : ℝ => x) from continuous_const)
      (show Continuous (fun u : ℝ => u) from continuous_id)
      (show Continuous (fun _ : ℝ => x) from continuous_const)).intervalIntegrable

end
end D5.S3.Arith.Robin.ForwardKernel.MovingLengthRegularity
