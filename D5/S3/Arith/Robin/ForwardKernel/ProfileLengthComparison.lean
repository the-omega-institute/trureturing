/- GID: D5/S3/Arith/Robin/ForwardKernel/ProfileLengthComparison
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/ProfileLengthComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lipschitz profiles have square-error bounds when a variable length is frozen. -/

import D5.S3.Arith.Robin.ForwardKernel.MovingLengthRegularity

/-! Head and tail estimates for freezing the length of a profile average. -/

namespace D5.S3.Arith.Robin.ForwardKernel.ProfileLengthComparison

open Set MeasureTheory
open VarianceTransferDefs VarianceTransfer MovingLengthRegularity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma bounded_factor_square_le {f k : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hC : 0 ≤ C)
    (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume a b)
    (hk : ∀ u ∈ Icc a b, |k u| ≤ C) :
    (∫ u in a..b, k u * f u) ^ 2 ≤ C ^ 2 * (b - a) * ∫ u in a..b, f u ^ 2 := by
  by_cases he : a = b
  · subst b; simp
  have hp : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab he)
  have hn : |∫ u in a..b, k u * f u| ≤ C * ∫ u in a..b, |f u| := by
    simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul] using
      intervalIntegral.norm_integral_le_of_norm_le (f := fun u => k u * f u) hab
        (Filter.Eventually.of_forall (fun u hu => by
          simpa only [Real.norm_eq_abs, abs_mul] using
            mul_le_mul_of_nonneg_right (hk u ⟨hu.1.le, hu.2⟩) (abs_nonneg (f u))))
        (hf.norm.const_mul C)
  have hc := interval_cauchy_schwarz hp
    (by simpa only [sub_self, Real.norm_eq_abs] using hf.norm.comp_add_left a)
    (by simpa only [sub_self, sq_abs] using hf2.comp_add_left a)
  have heq (q : ℝ → ℝ) : (∫ u in (0 : ℝ)..(b - a), q (a + u)) = ∫ u in a..b, q u := by
    simpa only [add_zero, add_sub_cancel] using
      intervalIntegral.integral_comp_add_left (a := 0) (b := b - a) q a
  simp only [sq_abs] at hc
  rw [heq (fun u => |f u|), heq (fun u => f u ^ 2)] at hc
  have hn0 : 0 ≤ ∫ u in a..b, |f u| :=
    intervalIntegral.integral_nonneg hab (fun _ _ => abs_nonneg _)
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC hn0)).mpr hn
  rw [sq_abs, mul_pow] at hs
  exact hs.trans (by nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg C)])

private lemma inverse_length_bounds {h H d : ℝ} (hh : 0 < h) (hd : 0 ≤ d)
    (hH : H ∈ Icc h (h + d)) :
    |1 / H - 1 / h| ≤ d / h ^ 2 ∧
      |1 / H ^ 2 - 1 / h ^ 2| ≤ 2 * d / h ^ 3 := by
  have hH0 : 0 < H := hh.trans_le hH.1
  have hi : 1 / H ≤ 1 / h := one_div_le_one_div_of_le hh hH.1
  have hi0 : 0 ≤ 1 / H := by positivity
  have hj0 : 0 ≤ 1 / h := by positivity
  have he : 1 / h - 1 / H ≤ d / h ^ 2 := by
    calc
      _ = (H - h) / (h * H) := by field_simp
      _ ≤ d / (h * H) := div_le_div_of_nonneg_right (by linarith [hH.2]) (by positivity)
      _ ≤ d / h ^ 2 := div_le_div_of_nonneg_left hd (by positivity)
        (by nlinarith [hH.1])
  constructor
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hi), neg_sub] using he
  · have hi2 : 1 / H ^ 2 ≤ 1 / h ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos hh) (pow_le_pow_left₀ hh.le hH.1 2)
    rw [abs_of_nonpos (sub_nonpos.mpr hi2), neg_sub]
    calc
      _ = (1 / h - 1 / H) * (1 / h + 1 / H) := by ring
      _ ≤ (d / h ^ 2) * (2 / h) :=
        mul_le_mul he (by linarith [show 2 / h = 1 / h + 1 / h by ring])
          (by linarith) (by positivity)
      _ = _ := by ring

private lemma profile_head_coefficient_le {g : ℝ → ℝ} {M h H d u : ℝ} {L : NNReal}
    (hh : 0 < h) (hd : 0 ≤ d)
    (hgM : ∀ s ∈ Icc (0 : ℝ) 1, |g s| ≤ M)
    (hgLip : LipschitzOnWith L g (Icc (0 : ℝ) 1))
    (hH : H ∈ Icc h (h + d)) (hu : u ∈ Icc (0 : ℝ) h) :
    |g (u / H) / H ^ 2 - g (u / h) / h ^ 2| ≤ (2 * M + L) * d / h ^ 3 := by
  have hH0 : 0 < H := hh.trans_le hH.1
  have huH : u / H ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hu.1 hH0.le, (div_le_one hH0).mpr (hu.2.trans hH.1)⟩
  have huh : u / h ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hu.1 hh.le, (div_le_one hh).mpr hu.2⟩
  obtain ⟨hi, hi2⟩ := inverse_length_bounds hh hd hH
  have hdil : |u / H - u / h| ≤ d / h := by
    calc
      _ = u * |1 / H - 1 / h| := by
        calc
          _ = |u * (1 / H - 1 / h)| := by congr 1; ring
          _ = _ := by rw [abs_mul, abs_of_nonneg hu.1]
      _ ≤ h * (d / h ^ 2) := mul_le_mul hu.2 hi (abs_nonneg _) hh.le
      _ = _ := by field_simp
  have hgl : |g (u / H) - g (u / h)| ≤ (L : ℝ) * (d / h) := by
    have ht := hgLip.dist_le_mul _ huH _ huh
    simp only [Real.dist_eq] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left hdil L.coe_nonneg)
  calc
    _ = |(1 / H ^ 2 - 1 / h ^ 2) * g (u / H) +
        (1 / h ^ 2) * (g (u / H) - g (u / h))| := by congr 1; ring
    _ ≤ |1 / H ^ 2 - 1 / h ^ 2| * |g (u / H)| +
        (1 / h ^ 2) * |g (u / H) - g (u / h)| := by
      calc
        _ ≤ |(1 / H ^ 2 - 1 / h ^ 2) * g (u / H)| +
            |(1 / h ^ 2) * (g (u / H) - g (u / h))| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / h ^ 2)]
    _ ≤ (2 * d / h ^ 3) * M + (1 / h ^ 2) * ((L : ℝ) * (d / h)) :=
      add_le_add (mul_le_mul hi2 (hgM _ huH) (abs_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left hgl (by positivity))
    _ = _ := by ring

private lemma profile_integrand_integrable {E g : ℝ → ℝ} {L : NNReal}
    (hE : LocallyBoundedMeasurable E)
    (hgLip : LipschitzOnWith L g (Icc (0 : ℝ) 1))
    {q a b : ℝ} (hq : 0 < q) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ q) (x : ℝ) :
    IntervalIntegrable (fun u => g (u / q) * increment E u x) volume a b := by
  apply (step_integrable hE x a b).continuousOn_mul
  apply hgLip.continuousOn.comp (continuous_id.div_const q).continuousOn
  intro u hu
  rw [uIcc_of_le hab] at hu
  exact ⟨div_nonneg (ha.trans hu.1) hq.le, (div_le_one hq).mpr (hu.2.trans hb)⟩

private lemma profile_difference_sq_le {E g : ℝ → ℝ} {M h H d x : ℝ} {L : NNReal}
    (hE : LocallyBoundedMeasurable E)
    (hh : 0 < h) (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hgM : ∀ s ∈ Icc (0 : ℝ) 1, |g s| ≤ M)
    (hgLip : LipschitzOnWith L g (Icc (0 : ℝ) 1))
    (hH : H ∈ Icc h (h + d)) :
    (profileAverage E g H x - profileAverage E g h x) ^ 2 ≤
      2 * ((2 * M + (L : ℝ)) * d / h ^ 3) ^ 2 * h *
        (∫ u in (0 : ℝ)..h, increment E u x ^ 2) +
      2 * (M / h ^ 2) ^ 2 * d *
        (∫ u in h..(h + d), increment E u x ^ 2) := by
  have hH0 : 0 < H := hh.trans_le hH.1
  let A := ∫ u in (0 : ℝ)..h,
    (g (u / H) / H ^ 2 - g (u / h) / h ^ 2) * increment E u x
  let B := ∫ u in h..H, (g (u / H) / H ^ 2) * increment E u x
  have hiH := profile_integrand_integrable hE hgLip hH0 (le_refl 0) hh.le hH.1 x
  have hit := profile_integrand_integrable hE hgLip hH0 hh.le hH.1 (le_refl H) x
  have hih := profile_integrand_integrable hE hgLip hh (le_refl 0) hh.le (le_refl h) x
  have he : profileAverage E g H x - profileAverage E g h x = A + B := by
    unfold profileAverage profilePrimitive
    rw [← intervalIntegral.integral_add_adjacent_intervals hiH hit, add_div]
    have hA : A = (∫ u in (0 : ℝ)..h, g (u / H) * increment E u x) / H ^ 2 -
        (∫ u in (0 : ℝ)..h, g (u / h) * increment E u x) / h ^ 2 := by
      rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_div,
        ← intervalIntegral.integral_sub (hiH.div_const _) (hih.div_const _)]
      apply intervalIntegral.integral_congr
      intro u _; dsimp; ring
    have hB : B = (∫ u in h..H, g (u / H) * increment E u x) / H ^ 2 := by
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro u _; dsimp; ring
    rw [hA, hB]; ring
  have hA : A ^ 2 ≤ ((2 * M + (L : ℝ)) * d / h ^ 3) ^ 2 * h *
      ∫ u in (0 : ℝ)..h, increment E u x ^ 2 := by
    simpa only [sub_zero] using bounded_factor_square_le hh.le (by positivity)
      (step_integrable hE x 0 h) (step_sq_integrable hE x 0 h)
      (fun u hu => profile_head_coefficient_le hh hd hgM hgLip hH hu)
  have hB : B ^ 2 ≤ (M / h ^ 2) ^ 2 * d *
      ∫ u in h..(h + d), increment E u x ^ 2 := by
    have ht := bounded_factor_square_le hH.1 (div_nonneg hM (sq_nonneg h))
      (step_integrable hE x h H) (step_sq_integrable hE x h H)
      (k := fun u => g (u / H) / H ^ 2) (by
        intro u hu
        rw [abs_div, abs_of_nonneg (sq_nonneg H)]
        exact (div_le_div_of_nonneg_right
          (hgM _ ⟨div_nonneg (hh.le.trans hu.1) hH0.le, (div_le_one hH0).mpr hu.2⟩)
          (sq_nonneg H)).trans
          (div_le_div_of_nonneg_left hM (sq_pos_of_pos hh)
            (pow_le_pow_left₀ hh.le hH.1 2)))
    have hm := intervalIntegral.integral_mono_interval (le_refl h) hH.1 hH.2
      (Filter.Eventually.of_forall (fun u => sq_nonneg (increment E u x)))
      (step_sq_integrable hE x h (h + d))
    have hi0 := intervalIntegral.integral_nonneg_of_forall (show h ≤ h + d by linarith)
      (fun u => sq_nonneg (increment E u x)) (μ := volume)
    exact ht.trans ((mul_le_mul_of_nonneg_left hm
        (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hH.1))).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (show H - h ≤ d by linarith [hH.2]) (sq_nonneg _)) hi0))
  rw [he]
  exact (add_sq_le (a := A) (b := B)).trans (by nlinarith [hA, hB])

/-- Freezing a positive measurable length has a uniform square error
for bounded Lipschitz profiles. -/
theorem variable_profile_square_error_le {E g H : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g)
    (hHmeas : Measurable H)
    {a b h d M V : ℝ} {L : NNReal}
    (hab : a ≤ b) (hh : 0 < h) (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hgM : ∀ s ∈ Icc (0 : ℝ) 1, |g s| ≤ M)
    (hgLip : LipschitzOnWith L g (Icc (0 : ℝ) 1))
    (hH : ∀ x ∈ Icc a b, H x ∈ Icc h (h + d))
    (hV : ∀ u ∈ Icc (0 : ℝ) (h + d),
      (∫ x in a..b, increment E u x ^ 2) ≤ V) :
    (∫ x in a..b, (profileAverage E g (H x) x - profileAverage E g h x) ^ 2) ≤
      2 * ((2 * M + (L : ℝ)) ^ 2 + M ^ 2) * d ^ 2 / h ^ 4 * V := by
  have hf := profileAverage_variable_memLp hE hg hHmeas hab hh hH
  have hfrozen := profileAverage_variable_memLp hE hg measurable_const hab hh
    (fun _ _ => ⟨le_rfl, le_rfl⟩)
  have hfg : IntervalIntegrable
      (fun x => (profileAverage E g (H x) x - profileAverage E g h x) ^ 2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact (memLp_two_iff_integrable_sq (hf.sub hfrozen).aestronglyMeasurable).mp
      (hf.sub hfrozen)
  have strip (c e : ℝ) (hce : c ≤ e)
      (hc : 0 ≤ c) (he : e ≤ h + d) :
      IntervalIntegrable (fun x => ∫ u in c..e, increment E u x ^ 2) volume a b ∧
      (∫ x in a..b, ∫ u in c..e, increment E u x ^ 2) ≤ (e - c) * V := by
    have hi := increment_sq_rectangle_integrable hE a b c e continuous_snd
    have hleft : IntervalIntegrable (fun x => ∫ u in c..e, increment E u x ^ 2) volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      simpa only [intervalIntegral.integral_of_le hce, IntegrableOn] using hi.integral_prod_left
    refine ⟨hleft, ?_⟩
    have hswap : (∫ x in a..b, ∫ u in c..e, increment E u x ^ 2) =
        ∫ u in c..e, ∫ x in a..b, increment E u x ^ 2 := by
      simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hce]
      exact integral_integral_swap hi
    rw [hswap]
    calc
      _ ≤ ∫ _u in c..e, V := by
        apply intervalIntegral.integral_mono_on hce _ intervalIntegrable_const
          (fun u hu => hV u ⟨hc.trans hu.1, hu.2.trans he⟩)
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hce]
        simpa only [intervalIntegral.integral_of_le hab, IntegrableOn] using hi.integral_prod_right
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]
  obtain ⟨hhead, hhbound⟩ := strip 0 h hh.le (le_refl 0) (by linarith)
  obtain ⟨htail, htbound⟩ := strip h (h + d) (by linarith) hh.le (le_refl _)
  calc
    _ ≤ ∫ x in a..b,
        2 * ((2 * M + (L : ℝ)) * d / h ^ 3) ^ 2 * h *
          (∫ u in (0 : ℝ)..h, increment E u x ^ 2) +
        2 * (M / h ^ 2) ^ 2 * d * (∫ u in h..(h + d), increment E u x ^ 2) := by
      apply intervalIntegral.integral_mono_on hab hfg
        ((hhead.const_mul _).add (htail.const_mul _))
      exact fun x hx => profile_difference_sq_le hE hh hd hM hgM hgLip (hH x hx)
    _ = 2 * ((2 * M + (L : ℝ)) * d / h ^ 3) ^ 2 * h *
          (∫ x in a..b, ∫ u in (0 : ℝ)..h, increment E u x ^ 2) +
        2 * (M / h ^ 2) ^ 2 * d * (∫ x in a..b, ∫ u in h..(h + d), increment E u x ^ 2) := by
      rw [intervalIntegral.integral_add (hhead.const_mul _) (htail.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ 2 * ((2 * M + (L : ℝ)) * d / h ^ 3) ^ 2 * h * ((h - 0) * V) +
        2 * (M / h ^ 2) ^ 2 * d * ((h + d - h) * V) :=
      add_le_add (mul_le_mul_of_nonneg_left hhbound (by positivity))
        (mul_le_mul_of_nonneg_left htbound (by positivity))
    _ = _ := by field_simp; ring

end
end D5.S3.Arith.Robin.ForwardKernel.ProfileLengthComparison
