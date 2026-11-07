/- GID: D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Variable-length triangular averages are measurable and square integrable. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer

/-! Regularity of triangular averages when their length varies with the starting point. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MovingLengthRegularity

open Set MeasureTheory Filter
open VarianceTransferDefs VarianceTransfer

noncomputable section

private lemma error_intervalIntegrable {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (a b : ℝ) : IntervalIntegrable E volume a b := by
  obtain ⟨M, _, hM⟩ := hE.2 (min a b) (max a b)
  apply IntegrableOn.intervalIntegrable
  apply IntegrableOn.of_bound isCompact_uIcc.measure_lt_top hE.1.aestronglyMeasurable M
  filter_upwards [ae_restrict_mem measurableSet_uIcc] with x hx
  exact hM x hx

private lemma primitive_formula {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (h x : ℝ) :
    triangularPrimitive E h x =
      (∫ t in (0 : ℝ)..(x + h), E t) - (∫ t in (0 : ℝ)..x, E t) - h * E x := by
  have hi : IntervalIntegrable (fun u => E (x + u)) volume 0 h := by
    simpa using (error_intervalIntegrable hE x (x + h)).comp_add_left x
  change (∫ u in (0 : ℝ)..h, E (x + u) - E x) = _
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
    intervalIntegral.integral_comp_add_left, add_zero,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [intervalIntegral.integral_interval_sub_left
    (error_intervalIntegrable hE 0 (x + h)) (error_intervalIntegrable hE 0 x)]

/-- Measurable choices of length preserve measurability of the triangular average. -/
private theorem triangularAverage_variable_measurable {E H : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hH : Measurable H) :
    Measurable (fun x => triangularAverage E (H x) x) := by
  have hF := (intervalIntegral.continuous_primitive (error_intervalIntegrable hE) 0).measurable
  have he : (fun x => triangularAverage E (H x) x) =
      (fun x => ((∫ t in (0 : ℝ)..(x + H x), E t) -
        (∫ t in (0 : ℝ)..x, E t) - H x * E x) / H x ^ 2) := by
    funext x
    rw [triangularAverage, primitive_formula hE]
  rw [he]
  exact (((hF.comp (measurable_id.add hH)).sub hF).sub (hH.mul hE.1)).div (hH.pow_const 2)

/-- On a bounded interval, lengths bounded away from zero give square-integrable triangular averages. -/
theorem triangularAverage_variable_memLp {E H : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hH : Measurable H)
    {a b l L : ℝ} (hab : a ≤ b) (hl : 0 < l)
    (hbound : ∀ x ∈ Icc a b, H x ∈ Icc l L) :
    MemLp (fun x => triangularAverage E (H x) x) 2 (volume.restrict (Ioc a b)) := by
  have hL : 0 < L := (hl.trans_le (hbound a ⟨le_rfl, hab⟩).1).trans_le
    (hbound a ⟨le_rfl, hab⟩).2
  obtain ⟨M, hM, hMb⟩ := hE.2 a (b + L)
  apply MemLp.of_bound (triangularAverage_variable_measurable hE hH).aestronglyMeasurable
    (2 * M / l)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2⟩
  obtain ⟨hlo, hup⟩ := hbound x hx'
  have hp : 0 < H x := hl.trans_le hlo
  have hb : |triangularPrimitive E (H x) x| ≤ 2 * M * H x := by
    have hh : ∀ u ∈ uIoc (0 : ℝ) (H x), ‖increment E u x‖ ≤ 2 * M := by
      intro u hu
      rw [uIoc_of_le hp.le] at hu
      have hxE := hMb x ⟨hx.1.le, by linarith [hx.2]⟩
      have hxu := hMb (x + u) ⟨by linarith [hu.1, hx.1], by linarith [hu.2, hx.2]⟩
      exact (abs_sub _ _).trans (by linarith)
    simpa only [triangularPrimitive, Real.norm_eq_abs, sub_zero, abs_of_pos hp]
      using intervalIntegral.norm_integral_le_of_norm_le_const hh
  rw [Real.norm_eq_abs, triangularAverage, abs_div, abs_pow, sq_abs]
  calc
    _ ≤ (2 * M * H x) / H x ^ 2 := div_le_div_of_nonneg_right hb (sq_nonneg _)
    _ = 2 * M / H x := by field_simp <;> ring
    _ ≤ 2 * M / l := div_le_div_of_nonneg_left (by positivity) hl hlo

private lemma step_integrable {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (x a b : ℝ) : IntervalIntegrable (fun u => increment E u x) volume a b :=
  (increment_comp_integrableOn hE isCompact_uIcc continuous_id continuous_const).intervalIntegrable

private lemma step_sq_integrable {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (x a b : ℝ) : IntervalIntegrable (fun u => increment E u x ^ 2) volume a b := by
  simpa only [pow_two, Pi.mul_apply] using
    (increment_product_comp_integrableOn hE isCompact_uIcc
      (show Continuous (fun u : ℝ => u) from continuous_id)
      (show Continuous (fun _ : ℝ => x) from continuous_const)
      (show Continuous (fun u : ℝ => u) from continuous_id)
      (show Continuous (fun _ : ℝ => x) from continuous_const)).intervalIntegrable

/-- Increasing the upper length by at most d bounds the squared primitive tail by its square mass on that strip. -/
private theorem primitive_tail_square_le {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {h H d x : ℝ} (hd : 0 ≤ d) (hhH : h ≤ H) (hHd : H ≤ h + d) :
    (triangularPrimitive E H x - triangularPrimitive E h x) ^ 2 ≤
      d * ∫ u in h..(h + d), increment E u x ^ 2 := by
  rw [triangularPrimitive, triangularPrimitive,
    intervalIntegral.integral_interval_sub_left
      (step_integrable hE x 0 H) (step_integrable hE x 0 h)]
  by_cases he : h = H
  · subst H
    simp only [intervalIntegral.integral_same, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
    exact mul_nonneg hd (intervalIntegral.integral_nonneg_of_forall (by linarith)
      (fun _ => sq_nonneg _))
  have hpos : 0 < H - h := sub_pos.mpr (lt_of_le_of_ne hhH he)
  have hc := VarianceTransfer.interval_cauchy_schwarz hpos
    (by simpa only [sub_self] using (step_integrable hE x h H).comp_add_left h)
    (by simpa only [sub_self] using (step_sq_integrable hE x h H).comp_add_left h)
  have heq (f : ℝ → ℝ) : (∫ t in (0 : ℝ)..(H - h), f (h + t)) = ∫ t in h..H, f t := by
    simpa only [add_zero, add_sub_cancel] using
      (intervalIntegral.integral_comp_add_left (a := 0) (b := H - h) f h)
  rw [heq (fun u => increment E u x), heq (fun u => increment E u x ^ 2)] at hc
  have hm := intervalIntegral.integral_mono_interval (le_refl h) hhH hHd
    (Eventually.of_forall (fun u => sq_nonneg (increment E u x)))
    (step_sq_integrable hE x h (h + d))
  exact hc.trans ((mul_le_mul_of_nonneg_left hm hpos.le).trans
    (mul_le_mul_of_nonneg_right (show H - h ≤ d by linarith)
      (intervalIntegral.integral_nonneg_of_forall (by linarith) (fun _ => sq_nonneg _))))

private lemma average_difference_sq_le {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {h H d x : ℝ} (hh : 0 < h) (hd : 0 ≤ d) (hdh : d ≤ h)
    (hH : H ∈ Icc h (h + d)) :
    (triangularAverage E H x - triangularAverage E h x) ^ 2 ≤
      18 * (d / h) ^ 2 * triangularAverage E h x ^ 2 +
        (2 * d / h ^ 4) * ∫ u in h..(h + d), increment E u x ^ 2 := by
  have hH0 := hh.trans_le hH.1
  have hc : |h ^ 2 / H ^ 2 - 1| ≤ 3 * d / h := by
    have hle : h ^ 2 / H ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hH0)).mpr
      (pow_le_pow_left₀ hh.le hH.1 2)
    rw [abs_of_nonpos (by linarith : h ^ 2 / H ^ 2 - 1 ≤ 0)]
    calc
      -(h ^ 2 / H ^ 2 - 1) = (H - h) * (H + h) / H ^ 2 := by field_simp <;> ring
      _ ≤ (d * (3 * h)) / H ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg H)
        exact mul_le_mul (by linarith [hH.2]) (by linarith [hH.2])
          (by linarith [hH.1]) (by positivity)
      _ ≤ (d * (3 * h)) / h ^ 2 := div_le_div_of_nonneg_left (by positivity)
        (sq_pos_of_pos hh) (pow_le_pow_left₀ hh.le hH.1 2)
      _ = _ := by field_simp <;> ring
  have ht := primitive_tail_square_le hE hd hH.1 hH.2 (x := x)
  have hi0 : 0 ≤ ∫ u in h..(h + d), increment E u x ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall (by linarith) (fun _ => sq_nonneg _)
  have he : triangularAverage E H x - triangularAverage E h x =
      (h ^ 2 / H ^ 2 - 1) * triangularAverage E h x +
        (triangularPrimitive E H x - triangularPrimitive E h x) / H ^ 2 := by
    unfold triangularAverage
    field_simp
    ring
  have h1 : ((h ^ 2 / H ^ 2 - 1) * triangularAverage E h x) ^ 2 ≤
      9 * (d / h) ^ 2 * triangularAverage E h x ^ 2 := by
    rw [mul_pow]
    have hc' := pow_le_pow_left₀ (abs_nonneg _) hc 2
    rw [sq_abs] at hc'
    convert mul_le_mul_of_nonneg_right hc' (sq_nonneg (triangularAverage E h x)) using 1 <;> ring
  have h2 : ((triangularPrimitive E H x - triangularPrimitive E h x) / H ^ 2) ^ 2 ≤
      (d / h ^ 4) * ∫ u in h..(h + d), increment E u x ^ 2 := by
    rw [div_pow, ← pow_mul]
    norm_num only [show (2 : ℕ) * 2 = 4 by norm_num]
    calc
      _ ≤ (d * ∫ u in h..(h + d), increment E u x ^ 2) / H ^ 4 :=
        div_le_div_of_nonneg_right ht (by positivity)
      _ ≤ (d * ∫ u in h..(h + d), increment E u x ^ 2) / h ^ 4 :=
        div_le_div_of_nonneg_left (mul_nonneg hd hi0) (by positivity)
          (pow_le_pow_left₀ hh.le hH.1 4)
      _ = _ := by ring
  rw [he]
  exact (add_sq_le (a := (h ^ 2 / H ^ 2 - 1) * triangularAverage E h x)
    (b := (triangularPrimitive E H x - triangularPrimitive E h x) / H ^ 2)).trans
      (by linear_combination 2 * h1 + 2 * h2)

/-- A uniform variance bound on a length strip controls the square error from freezing a variable length. -/
theorem variable_average_square_error_le {E H : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hHm : Measurable H)
    {a b h d M : ℝ} (hab : a ≤ b) (hh : 0 < h) (hd : 0 ≤ d) (hdh : d ≤ h)
    (hH : ∀ x ∈ Icc a b, H x ∈ Icc h (h + d))
    (hV : ∀ u ∈ Icc h (h + d), (∫ x in a..b, increment E u x ^ 2) ≤ M) :
    (∫ x in a..b, (triangularAverage E (H x) x - triangularAverage E h x) ^ 2) ≤
      18 * (d / h) ^ 2 * (∫ x in a..b, triangularAverage E h x ^ 2) +
        2 * d ^ 2 / h ^ 4 * M := by
  have hf := triangularAverage_variable_memLp hE hHm hab hh hH
  have hg := triangularAverage_variable_memLp hE measurable_const hab hh
    (fun _ _ => ⟨le_rfl, le_rfl⟩)
  have hfg : IntervalIntegrable
      (fun x => (triangularAverage E (H x) x - triangularAverage E h x) ^ 2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact (memLp_two_iff_integrable_sq (hf.sub hg).aestronglyMeasurable).mp (hf.sub hg)
  have hg2 : IntervalIntegrable (fun x => triangularAverage E h x ^ 2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mp hg
  have hi := increment_sq_rectangle_integrable hE a b h (h + d) continuous_snd
  have hG : IntervalIntegrable (fun x => ∫ u in h..(h + d), increment E u x ^ 2)
      volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    simpa only [intervalIntegral.integral_of_le (by linarith : h ≤ h + d), IntegrableOn]
      using hi.integral_prod_left
  have hswap : (∫ x in a..b, ∫ u in h..(h + d), increment E u x ^ 2) =
      ∫ u in h..(h + d), ∫ x in a..b, increment E u x ^ 2 := by
    simp_rw [intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_of_le (by linarith : h ≤ h + d)]
    exact integral_integral_swap hi
  have hstrip : (∫ x in a..b, ∫ u in h..(h + d), increment E u x ^ 2) ≤ d * M := by
    rw [hswap]
    calc
      _ ≤ ∫ _u in h..(h + d), M := by
        apply intervalIntegral.integral_mono_on (by linarith) _ intervalIntegrable_const
          (fun u hu => hV u hu)
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : h ≤ h + d)]
        simpa only [intervalIntegral.integral_of_le hab, IntegrableOn]
          using hi.integral_prod_right
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  calc
    _ ≤ ∫ x in a..b,
        18 * (d / h) ^ 2 * triangularAverage E h x ^ 2 +
          (2 * d / h ^ 4) * ∫ u in h..(h + d), increment E u x ^ 2 := by
      apply intervalIntegral.integral_mono_on hab hfg
        ((hg2.const_mul _).add (hG.const_mul _))
      exact fun x hx => average_difference_sq_le hE hh hd hdh (hH x hx)
    _ = 18 * (d / h) ^ 2 * (∫ x in a..b, triangularAverage E h x ^ 2) +
        (2 * d / h ^ 4) * (∫ x in a..b, ∫ u in h..(h + d), increment E u x ^ 2) := by
      rw [intervalIntegral.integral_add (hg2.const_mul _) (hG.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left hstrip (by positivity : 0 ≤ 2 * d / h ^ 4)
      convert add_le_add_left this
        (18 * (d / h) ^ 2 * (∫ x in a..b, triangularAverage E h x ^ 2)) using 1 <;> ring

end
end D5.S3.Arith.Robin.ForwardKernel.MovingLengthRegularity
