/- GID: D5/S3/Arith/Robin/ForwardKernel/TriangularMeanSquare
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/TriangularMeanSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-length triangular averages have the mean-square overlap constant one third. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer
import D5.S3.Arith.Robin.ForwardKernel.FixedLengthCovariance
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Fixed-length mean squares from truncated covariance convergence. -/

namespace D5.S3.Arith.Robin.ForwardKernel.TriangularMeanSquare

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer FixedLengthCovariance

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The cutoff occupies a vanishing fraction of the fixed length. -/
private theorem cutoff_div_fixedLength_tendsto_zero (c : ℝ) :
    Tendsto (fun X : ℝ => X ^ (31 / 40 : ℝ) / fixedLength c X) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 40)).div_const c
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [show -(1 / 40 : ℝ) = (31 / 40 : ℝ) - 4 / 5 by norm_num, Real.rpow_sub hX]
  dsimp [fixedLength]
  ring

/-- The cutoff is eventually smaller than both the fixed length and X/16. -/
private theorem cutoff_eventually_small {c : ℝ} (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop,
      0 < X ^ (31 / 40 : ℝ) ∧
      X ^ (31 / 40 : ℝ) ≤ X / 16 ∧
      X ^ (31 / 40 : ℝ) ≤ fixedLength c X := by
  have hratio : Tendsto (fun X : ℝ => X ^ (31 / 40 : ℝ) / X) atTop (𝓝 0) := by
    apply (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 9 / 40)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [show -(9 / 40 : ℝ) = (31 / 40 : ℝ) - 1 by norm_num, Real.rpow_sub hX,
      Real.rpow_one]
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    (cutoff_div_fixedLength_tendsto_zero c).eventually (gt_mem_nhds zero_lt_one)]
    with X hX hratio hcut
  have hh : 0 < fixedLength c X := by dsimp [fixedLength]; positivity
  refine ⟨Real.rpow_pos_of_pos hX _, ?_, ((div_lt_one hh).mp hcut).le⟩
  have ht := (div_lt_iff₀ hX).mp hratio
  linarith

private lemma cutoff_log_power_tendsto :
    Tendsto (fun X : ℝ =>
      (Real.log (2 * X / X ^ (31 / 40 : ℝ))) ^ 2 / X ^ (3 / 40 : ℝ))
      atTop (𝓝 0) := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 80)).tendsto_div_nhds_zero
  have hconst := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 80)).const_div_atTop
    (Real.log 2)
  have h := (hconst.add (hlog.const_mul (9 / 40 : ℝ))).pow 2
  simp only [mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  have hl : Real.log (2 * X / X ^ (31 / 40 : ℝ)) =
      Real.log 2 + (9 / 40 : ℝ) * Real.log X := by
    rw [Real.log_div (by positivity) (Real.rpow_pos_of_pos hX _).ne',
      Real.log_mul (by norm_num) hX.ne', Real.log_rpow hX]
    ring
  have hp : (X ^ (3 / 80 : ℝ)) ^ 2 = X ^ (3 / 40 : ℝ) := by
    rw [← Real.rpow_mul_natCast hX.le]
    norm_num
  rw [hl, ← hp]
  ring

/-- The fixed-length logarithm is eventually at least one. -/
private theorem lengthLog_eventually_ge_one {c : ℝ} (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ lengthLog c X := by
  exact (length_log_tendsto hc).eventually (eventually_ge_atTop 1)


/-- The discarded short-length primitive has vanishing square mass on every subinterval. -/
private theorem cutoff_triangular_square_tendsto_zero {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hSV : ShortIntervalMeanSquareBoundFor E)
    {a b c : ℝ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 2) (hc : 0 < c) :
    Tendsto (fun X : ℝ =>
      (∫ x in (a * X)..(b * X), triangularPrimitive E (X ^ (31 / 40 : ℝ)) x ^ 2) /
        (X * fixedLength c X ^ 3 * lengthLog c X)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := small_length_triangular_square_bound hE hSV
  have hL := lengthLog_eventually_ge_one hc
  have hzero := cutoff_log_power_tendsto.const_mul (C / c ^ 3)
  simp only [mul_zero] at hzero
  apply squeeze_zero' _ _ hzero
  · filter_upwards [eventually_gt_atTop (0 : ℝ), hL] with X hX hl
    have hh : 0 < fixedLength c X := by dsimp [fixedLength]; positivity
    exact div_nonneg (intervalIntegral.integral_nonneg_of_forall
      (mul_le_mul_of_nonneg_right hab.le hX.le) (fun _ => sq_nonneg _)) (by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℝ), hL, hbound, cutoff_eventually_small hc]
      with X hX hl hbound hsmall
    have hh : 0 < fixedLength c X := by dsimp [fixedLength]; positivity
    have hp : (X ^ (31 / 40 : ℝ)) ^ 3 * X ^ (3 / 40 : ℝ) =
        (X ^ (4 / 5 : ℝ)) ^ 3 := by
      rw [← Real.rpow_mul_natCast hX.le, ← Real.rpow_add hX,
        ← Real.rpow_mul_natCast hX.le]
      norm_num
    have hsub : (∫ x in (a * X)..(b * X),
        triangularPrimitive E (X ^ (31 / 40 : ℝ)) x ^ 2) ≤
        ∫ x in X..(2 * X), triangularPrimitive E (X ^ (31 / 40 : ℝ)) x ^ 2 := by
      apply intervalIntegral.integral_mono_interval
        (by nlinarith) (mul_le_mul_of_nonneg_right hab.le hX.le) (by nlinarith)
        (Eventually.of_forall (fun _ => sq_nonneg _))
        (triangularPrimitive_sq_intervalIntegrable hE _ _ _)
    calc
      _ ≤ (C * X * (X ^ (31 / 40 : ℝ)) ^ 3 *
          (Real.log (2 * X / X ^ (31 / 40 : ℝ))) ^ 2) /
          (X * fixedLength c X ^ 3 * lengthLog c X) :=
        div_le_div_of_nonneg_right
          (hsub.trans (hbound _ hsmall.1 hsmall.2.1)) (by positivity)
      _ = C / c ^ 3 *
          ((Real.log (2 * X / X ^ (31 / 40 : ℝ))) ^ 2 / X ^ (3 / 40 : ℝ)) /
          lengthLog c X := by
        dsimp [fixedLength]
        field_simp
        nlinarith [hp]
      _ ≤ _ := div_le_self (by positivity) hl

private lemma cutoff_band (c : ℝ) :
    ∀ᶠ X : ℝ in atTop,
      (2 * X) ^ (3 / 4 : ℝ) ≤ X ^ (31 / 40 : ℝ) ∧
      fixedLength c X ≤ (2 * X) ^ (7 / 8 : ℝ) := by
  have hlo := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 40)).const_mul
    ((2 : ℝ) ^ (3 / 4 : ℝ))
  have hhi := shifted_band (c := max c 1) (d := 2) (q := 1) (r := 0)
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (by norm_num)
    (by norm_num) (by norm_num)
  simp only [mul_zero] at hlo
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hlo.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)), hhi] with X hX hl hh
  have hp (p : ℝ) : (2 * X) ^ p = (2 : ℝ) ^ p * X ^ p :=
    Real.mul_rpow (by norm_num) hX.le
  have hratio₁ : (2 * X) ^ (3 / 4 : ℝ) / X ^ (31 / 40 : ℝ) =
      (2 : ℝ) ^ (3 / 4 : ℝ) * X ^ (-(1 / 40 : ℝ)) := by
    rw [hp, mul_div_assoc, ← Real.rpow_sub hX]
    norm_num
  constructor
  · apply (div_le_one (Real.rpow_pos_of_pos hX _)).mp
    rw [hratio₁]
    exact hl.le
  · calc
      fixedLength c X ≤ fixedLength (max c 1) X :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hX.le _)
      _ ≤ (2 * X) ^ (7 / 8 : ℝ) := by
        simpa only [one_mul, zero_mul, add_zero] using hh.2

/-- The normalized covariance is uniformly bounded for lengths between the power cutoff and the fixed length. -/
private theorem retained_covariance_bound
    {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (hGM : CumulativeVarianceBandAsymptoticFor E)
    {a b c : ℝ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 2) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, ∀ u v : ℝ,
      X ^ (31 / 40 : ℝ) ≤ u → u ≤ fixedLength c X →
      X ^ (31 / 40 : ℝ) ≤ v → v ≤ fixedLength c X →
      |(∫ x in (a * X)..(b * X), increment E u x * increment E v x) /
        (X * fixedLength c X * lengthLog c X)| ≤ 16 := by
  have hGM₂ := (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).eventually
    (hGM 1 zero_lt_one)
  filter_upwards [eventually_ge_atTop (1 : ℝ), cutoff_band c, hGM₂,
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (20 * (|Real.log c| + Real.log 2 + 1)))]
    with X hX1 hband hGMX hlarge
  have hX : 0 < X := by linarith
  have hH : 0 < fixedLength c X := by dsimp [fixedLength]; positivity
  have hlog : lengthLog c X = (1 / 5 : ℝ) * Real.log X - Real.log c := by
    rw [lengthLog, Real.log_div hX.ne' hH.ne', fixedLength,
      Real.log_mul hc.ne' (Real.rpow_pos_of_pos hX _).ne', Real.log_rpow hX]
    ring
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hL : 0 < lengthLog c X := by
    rw [hlog]
    linarith [le_abs_self (Real.log c), abs_nonneg (Real.log c)]
  have hN : 0 < X * fixedLength c X * lengthLog c X := by positivity
  have hA : 1 ≤ a * X := by nlinarith
  have hAB : a * X ≤ b * X := mul_le_mul_of_nonneg_right hab.le hX.le
  have hB : b * X ≤ 2 * X := mul_le_mul_of_nonneg_right hb hX.le
  have hsquare (w l r : ℝ) :
      IntervalIntegrable (fun x => increment E w x ^ 2) volume l r := by
    simpa only [pow_two, id_eq] using
      (increment_product_comp_integrableOn hE isCompact_uIcc
        continuous_const continuous_id continuous_const continuous_id).intervalIntegrable
  have hbound (w : ℝ) (hUw : X ^ (31 / 40 : ℝ) ≤ w)
      (hwH : w ≤ fixedLength c X) :
      (∫ x in (a * X)..(b * X), increment E w x ^ 2) ≤
        16 * (X * fixedLength c X * lengthLog c X) := by
    have hw : 0 < w := (Real.rpow_pos_of_pos hX _).trans_le hUw
    have hlogw : 0 < Real.log (2 * X / w) := by
      apply Real.log_pos
      apply (one_lt_div hw).mpr
      have hh : fixedLength c X < X := by
        have := (Real.log_pos_iff (div_pos hX hH).le).mp hL
        exact (one_lt_div hH).mp this
      linarith
    have hlogw_upper : Real.log (2 * X / w) ≤ 4 * lengthLog c X := by
      calc
        _ ≤ Real.log (2 * X / X ^ (31 / 40 : ℝ)) :=
          Real.log_le_log (div_pos (by positivity) hw)
            (div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hX _) hUw)
        _ = Real.log 2 + (9 / 40 : ℝ) * Real.log X := by
          rw [Real.log_div (by positivity) (Real.rpow_pos_of_pos hX _).ne',
            Real.log_mul (by norm_num) hX.ne', Real.log_rpow hX]
          ring
        _ ≤ _ := by rw [hlog]; linarith [le_abs_self (Real.log c)]
    have hV := (abs_le.mp (hGMX w (hband.1.trans hUw) (hwH.trans hband.2))).2
    simp only [id_eq] at hV
    have hden : 0 < 2 * X * w * Real.log (2 * X / w) := by positivity
    have hV' : cumulativeVariance E (2 * X) w ≤
        2 * (2 * X * w * Real.log (2 * X / w)) := by
      exact (div_le_iff₀ hden).mp (by linarith)
    have hmono := intervalIntegral.integral_mono_interval hA hAB hB
      (Eventually.of_forall (fun x => sq_nonneg (increment E w x))) (hsquare w 1 (2 * X))
    change (∫ x in (a * X)..(b * X), increment E w x ^ 2) ≤ _
    apply hmono.trans (hV'.trans ?_)
    have hprod := mul_le_mul hwH hlogw_upper hlogw.le hH.le
    nlinarith [mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 4 * X)]
  intro u v hu huH hv hvH
  have hi : IntervalIntegrable (fun x => increment E u x * increment E v x)
      volume (a * X) (b * X) :=
    (increment_product_comp_integrableOn hE isCompact_uIcc
      continuous_const continuous_id continuous_const continuous_id).intervalIntegrable
  have hm : (∫ x in (a * X)..(b * X), |increment E u x * increment E v x|) ≤
      (∫ x in (a * X)..(b * X),
        (increment E u x ^ 2 + increment E v x ^ 2) / 2) := by
    apply intervalIntegral.integral_mono_on hAB hi.abs
      (((hsquare u _ _).add (hsquare v _ _)).div_const 2)
    intro x hx
    rw [abs_mul]
    nlinarith [sq_nonneg (|increment E u x| - |increment E v x|),
      sq_abs (increment E u x), sq_abs (increment E v x)]
  rw [abs_div, abs_of_pos hN]
  apply (div_le_iff₀ hN).mpr
  apply (intervalIntegral.abs_integral_le_integral_abs hAB).trans (hm.trans ?_)
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (hsquare u _ _) (hsquare v _ _)]
  linarith [hbound u hu huH, hbound v hv hvH]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma increment_product_cube_integrable {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (A B h δ : ℝ) :
    Integrable (fun p : ℝ × (ℝ × ℝ) =>
      increment E (p.2.1 * h) p.1 * increment E (p.2.2 * h) p.1)
      ((volume.restrict (Ioc A B)).prod
        ((volume.restrict (Ioc δ 1)).prod (volume.restrict (Ioc δ 1)))) := by
  rw [Measure.prod_restrict, Measure.prod_restrict]
  have hi := increment_product_comp_integrableOn (μ := volume.prod (volume.prod volume))
    hE (K := Icc A B ×ˢ (Icc δ 1 ×ˢ Icc δ 1))
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
    (u := fun p : ℝ × (ℝ × ℝ) => p.2.1 * h) (x := fun p => p.1)
    (v := fun p : ℝ × (ℝ × ℝ) => p.2.2 * h) (y := fun p => p.1)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  exact hi.mono_set (Set.prod_mono Ioc_subset_Icc_self
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self))

/-- Integrating a square of an increment integral equals integrating its covariance on a square. -/
private theorem truncated_square_eq_covariance {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) {A B h δ : ℝ} (hAB : A ≤ B) (hδ : δ ≤ 1) :
    (∫ x in A..B, (∫ s in δ..1, increment E (s * h) x) ^ 2) =
      ∫ p : ℝ × ℝ,
        (∫ x in A..B, increment E (p.1 * h) x * increment E (p.2 * h) x)
        ∂((volume.restrict (Ioc δ 1)).prod (volume.restrict (Ioc δ 1))) := by
  simp_rw [intervalIntegral.integral_of_le hAB, intervalIntegral.integral_of_le hδ]
  have hi := increment_product_cube_integrable hE A B h δ
  rw [← integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [pow_two]
  exact (integral_prod_mul (fun s : ℝ => increment E (s * h) x)
    (fun s : ℝ => increment E (s * h) x)).symm

/-- Restricting the unit square above a nonnegative cutoff gives the smaller square. -/
private theorem unit_square_cut_integral (f : ℝ × ℝ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ p, (Ioi δ ×ˢ Ioi δ).indicator f p
      ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1)))) =
    ∫ p, f p ∂((volume.restrict (Ioc δ 1)).prod (volume.restrict (Ioc δ 1))) := by
  rw [integral_indicator (measurableSet_Ioi.prod measurableSet_Ioi),
    ← Measure.prod_restrict, Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_comm (Ioi δ), Ioc_inter_Ioi, max_eq_right hδ]

/-- The covariance integral is measurable in both increment lengths. -/
private theorem covariance_measurable {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (h A B : ℝ) : Measurable (fun p : ℝ × ℝ =>
      ∫ x in A..B, increment E (p.1 * h) x * increment E (p.2 * h) x) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      increment E (p.1.1 * h) p.2 * increment E (p.1.2 * h) p.2) := by
    unfold increment
    exact ((hE.1.comp (measurable_snd.add (measurable_fst.fst.mul_const h))).sub
      (hE.1.comp measurable_snd)).mul
      ((hE.1.comp (measurable_snd.add (measurable_fst.snd.mul_const h))).sub
        (hE.1.comp measurable_snd))
  unfold intervalIntegral
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc A B))).measurable.sub
    (hm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc B A))).measurable

/-- A rescaled truncated increment integral is the difference of triangular primitives. -/
private theorem truncated_integral_eq_primitive_sub {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) {h U : ℝ} (hh : h ≠ 0) (x : ℝ) :
    h * (∫ s in (U / h)..1, increment E (s * h) x) =
      triangularPrimitive E h x - triangularPrimitive E U x := by
  have hs := intervalIntegral.smul_integral_comp_mul_right
    (fun u => increment E u x) (a := U / h) (b := 1) h
  simp only [smul_eq_mul, div_mul_cancel₀ _ hh, one_mul] at hs
  rw [hs]
  exact (intervalIntegral.integral_interval_sub_left
    ((increment_comp_integrableOn hE isCompact_uIcc continuous_id continuous_const).intervalIntegrable)
    ((increment_comp_integrableOn hE isCompact_uIcc continuous_id continuous_const).intervalIntegrable)).symm

/-- A perturbation negligible in normalized squared L2 norm preserves a mean-square limit. -/
theorem interval_square_tendsto_of_l2_negligible
    {A B S : ℝ → ℝ} {f g : ℝ → ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L)
    (hAB : ∀ᶠ X in atTop, A X ≤ B X)
    (hS : ∀ᶠ X in atTop, 0 < S X)
    (hf : ∀ᶠ X in atTop, MemLp (f X) 2 (volume.restrict (Ioc (A X) (B X))))
    (hg : ∀ᶠ X in atTop, MemLp (g X) 2 (volume.restrict (Ioc (A X) (B X))))
    (hgLimit : Tendsto (fun X => (∫ x in (A X)..(B X), g X x ^ 2) / S X)
      atTop (𝓝 L))
    (hfgLimit : Tendsto (fun X => (∫ x in (A X)..(B X), (f X x - g X x) ^ 2) / S X)
      atTop (𝓝 0)) :
    Tendsto (fun X => (∫ x in (A X)..(B X), f X x ^ 2) / S X) atTop (𝓝 L) := by
  have hdiff : Tendsto (fun X =>
      Real.sqrt ((∫ x in (A X)..(B X), f X x ^ 2) / S X) -
        Real.sqrt ((∫ x in (A X)..(B X), g X x ^ 2) / S X)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hd := hfgLimit.sqrt
    simp only [Real.sqrt_zero] at hd
    apply squeeze_zero' (Eventually.of_forall (fun X => norm_nonneg _)) ?_ hd
    filter_upwards [hAB, hS, hf, hg] with X hAB hS hf hg
    have hn (q : ℝ → ℝ) : 0 ≤ ∫ x in (A X)..(B X), q x ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hAB (fun x => sq_nonneg _)
    simp only [Real.norm_eq_abs]
    rw [Real.sqrt_div (hn (f X)), Real.sqrt_div (hn (g X)),
      Real.sqrt_div (hn (fun x => f X x - g X x)), ← sub_div, abs_div,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right (interval_l2_reverse_triangle hAB hf hg)
      (Real.sqrt_nonneg _)
  have hroot := hdiff.add hgLimit.sqrt
  simp only [zero_add] at hroot
  have hroot' : Tendsto (fun X =>
      Real.sqrt ((∫ x in (A X)..(B X), f X x ^ 2) / S X)) atTop (𝓝 (Real.sqrt L)) := by
    convert hroot using 1
    ext X
    ring
  have hsq := hroot'.pow 2
  rw [Real.sq_sqrt hL] at hsq
  apply hsq.congr'
  filter_upwards [hAB, hS] with X hAB hS
  exact Real.sq_sqrt (div_nonneg
    (intervalIntegral.integral_nonneg_of_forall hAB (fun x => sq_nonneg _)) hS.le)

private lemma cut_covariance_integral_tendsto {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hGM : CumulativeVarianceBandAsymptoticFor E)
    {a b c : ℝ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 2) (hc : 0 < c) :
    Tendsto (fun X =>
      ∫ p : ℝ × ℝ, (Ioi (X ^ (31 / 40 : ℝ) / fixedLength c X) ×ˢ
        Ioi (X ^ (31 / 40 : ℝ) / fixedLength c X)).indicator
        (fun p => (∫ x in (a * X)..(b * X),
          increment E (p.1 * fixedLength c X) x *
            increment E (p.2 * fixedLength c X) x) /
              (X * fixedLength c X * lengthLog c X)) p
        ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))))
      atTop (𝓝 ((b - a) / 3)) := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let F (X : ℝ) (p : ℝ × ℝ) :=
    (Ioi (X ^ (31 / 40 : ℝ) / fixedLength c X) ×ˢ
      Ioi (X ^ (31 / 40 : ℝ) / fixedLength c X)).indicator
      (fun p => (∫ x in (a * X)..(b * X),
        increment E (p.1 * fixedLength c X) x * increment E (p.2 * fixedLength c X) x) /
          (X * fixedLength c X * lengthLog c X)) p
  have hmem : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ,
      p ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hlim : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ,
      Tendsto (fun X => F X p) atTop (𝓝 ((b - a) * min p.1 p.2)) := by
    filter_upwards [hmem] with p hp
    apply (fixed_length_covariance_tendsto hE hGM ha hab hb hc
      ⟨hp.1.1.le, hp.1.2⟩ ⟨hp.2.1.le, hp.2.2⟩).congr'
    filter_upwards [
      (cutoff_div_fixedLength_tendsto_zero c).eventually (gt_mem_nhds hp.1.1),
      (cutoff_div_fixedLength_tendsto_zero c).eventually (gt_mem_nhds hp.2.1)]
      with X hs ht
    dsimp only [F]
    rw [indicator_of_mem (show p ∈ Ioi (X ^ (31 / 40 : ℝ) / fixedLength c X) ×ˢ
      Ioi (X ^ (31 / 40 : ℝ) / fixedLength c X) from ⟨hs, ht⟩)]
  have hmeas : ∀ᶠ X : ℝ in atTop, AEStronglyMeasurable (F X) (μ.prod μ) := by
    apply Eventually.of_forall
    intro X
    exact (((covariance_measurable hE (fixedLength c X) (a * X) (b * X)).div_const _).indicator
      (measurableSet_Ioi.prod measurableSet_Ioi)).aestronglyMeasurable
  have hbound : ∀ᶠ X : ℝ in atTop, ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, ‖F X p‖ ≤ 16 := by
    filter_upwards [retained_covariance_bound hE hGM ha hab hb hc,
      eventually_gt_atTop (0 : ℝ)] with X hbound hX
    have hh : 0 < fixedLength c X := by dsimp [fixedLength]; positivity
    filter_upwards [hmem] with p hp
    by_cases hcut : p ∈ Ioi (X ^ (31 / 40 : ℝ) / fixedLength c X) ×ˢ
        Ioi (X ^ (31 / 40 : ℝ) / fixedLength c X)
    · dsimp only [F]
      rw [indicator_of_mem hcut, Real.norm_eq_abs]
      exact hbound _ _ ((div_lt_iff₀ hh).mp hcut.1).le
        (mul_le_of_le_one_left hh.le hp.1.2)
        ((div_lt_iff₀ hh).mp hcut.2).le (mul_le_of_le_one_left hh.le hp.2.2)
    · simp only [F, indicator_of_notMem hcut, norm_zero]
      norm_num
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ.prod μ)
    (fun _ => (16 : ℝ)) hmeas hbound (integrable_const _) hlim
  have hmin : (∫ p : ℝ × ℝ, (b - a) * min p.1 p.2 ∂μ.prod μ) = (b - a) / 3 := by
    have hi : Integrable (fun p : ℝ × ℝ => min p.1 p.2) (μ.prod μ) := by
      dsimp [μ]
      rw [Measure.prod_restrict]
      exact ((continuous_fst.min continuous_snd).continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
    rw [integral_const_mul, integral_prod _ hi]
    change (b - a) * (∫ s in Ioc (0 : ℝ) 1, ∫ t in Ioc (0 : ℝ) 1, min s t) = _
    simp_rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    rw [integral_min_unit_square]
    ring
  rw [hmin] at h
  exact h

private lemma cut_primitive_square_tendsto {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hGM : CumulativeVarianceBandAsymptoticFor E)
    {a b c : ℝ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 2) (hc : 0 < c) :
    Tendsto (fun X =>
      (∫ x in (a * X)..(b * X),
        (triangularPrimitive E (fixedLength c X) x -
          triangularPrimitive E (X ^ (31 / 40 : ℝ)) x) ^ 2) /
        (X * fixedLength c X ^ 3 * lengthLog c X)) atTop (𝓝 ((b - a) / 3)) := by
  apply (cut_covariance_integral_tendsto hE hGM ha hab hb hc).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), cutoff_eventually_small hc] with X hX hcut
  have hh : 0 < fixedLength c X := by dsimp [fixedLength]; positivity
  have hδ : 0 ≤ X ^ (31 / 40 : ℝ) / fixedLength c X := div_nonneg hcut.1.le hh.le
  have hδ1 : X ^ (31 / 40 : ℝ) / fixedLength c X ≤ 1 := (div_le_one hh).mpr hcut.2.2
  rw [unit_square_cut_integral _ hδ, integral_div,
    ← truncated_square_eq_covariance hE (mul_le_mul_of_nonneg_right hab.le hX.le) hδ1]
  have he : (∫ x in (a * X)..(b * X),
      (triangularPrimitive E (fixedLength c X) x -
        triangularPrimitive E (X ^ (31 / 40 : ℝ)) x) ^ 2) =
      fixedLength c X ^ 2 * (∫ x in (a * X)..(b * X),
        (∫ s in (X ^ (31 / 40 : ℝ) / fixedLength c X)..1,
          increment E (s * fixedLength c X) x) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [← truncated_integral_eq_primitive_sub hE hh.ne' x, mul_pow]
  rw [he]
  field_simp
  simp only [mul_comm (fixedLength c X)]

/-- The fixed-length triangular average has normalized mean square equal asymptotically to a third of the interval length. -/
theorem fixed_length_triangular_mean_square_tendsto
    {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hSV : ShortIntervalMeanSquareBoundFor E)
    (hGM : CumulativeVarianceBandAsymptoticFor E)
    {a b c : ℝ}
    (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 2)
    (hc : 0 < c) :
    Filter.Tendsto
      (fun X =>
        (∫ x in (a * X)..(b * X),
          triangularAverage E (fixedLength c X) x ^ 2) /
          (X / fixedLength c X * lengthLog c X))
      Filter.atTop (nhds ((b - a) / 3)) := by
  have hAB : ∀ᶠ X : ℝ in atTop, a * X ≤ b * X := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    exact mul_le_mul_of_nonneg_right hab.le hX.le
  have hS : ∀ᶠ X : ℝ in atTop, 0 < X * fixedLength c X ^ 3 * lengthLog c X := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), lengthLog_eventually_ge_one hc]
      with X hX hL
    have hh : 0 < fixedLength c X := by dsimp [fixedLength]; positivity
    positivity
  have hmem (h A B : ℝ) (hAB : A ≤ B) :
      MemLp (triangularPrimitive E h) 2 (volume.restrict (Ioc A B)) := by
    apply (memLp_two_iff_integrable_sq (triangularPrimitive_measurable hE h).aestronglyMeasurable).mpr
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hAB).mp
      (triangularPrimitive_sq_intervalIntegrable hE h A B)
  have hf : ∀ᶠ X : ℝ in atTop,
      MemLp (triangularPrimitive E (fixedLength c X)) 2
        (volume.restrict (Ioc (a * X) (b * X))) := hAB.mono (fun _ h => hmem _ _ _ h)
  have hg : ∀ᶠ X : ℝ in atTop,
      MemLp (fun x => triangularPrimitive E (fixedLength c X) x -
        triangularPrimitive E (X ^ (31 / 40 : ℝ)) x) 2
        (volume.restrict (Ioc (a * X) (b * X))) := by
    filter_upwards [hAB] with X hAB
    exact (hmem _ _ _ hAB).sub (hmem _ _ _ hAB)
  have hlimit := interval_square_tendsto_of_l2_negligible
    (A := fun X => a * X) (B := fun X => b * X)
    (S := fun X => X * fixedLength c X ^ 3 * lengthLog c X)
    (f := fun X => triangularPrimitive E (fixedLength c X))
    (g := fun X x => triangularPrimitive E (fixedLength c X) x -
      triangularPrimitive E (X ^ (31 / 40 : ℝ)) x)
    (by positivity : 0 ≤ (b - a) / 3) hAB hS hf hg
    (cut_primitive_square_tendsto hE hGM ha hab hb hc)
    (by simpa only [sub_sub_cancel] using
      cutoff_triangular_square_tendsto_zero hE hSV ha hab hb hc)
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  have hh : 0 < fixedLength c X := by dsimp [fixedLength]; positivity
  simp_rw [triangularAverage, div_pow]
  rw [intervalIntegral.integral_div]
  field_simp

end
end D5.S3.Arith.Robin.ForwardKernel.TriangularMeanSquare
