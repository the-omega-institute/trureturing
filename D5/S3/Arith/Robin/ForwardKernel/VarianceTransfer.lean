/- GID: D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/VarianceTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact integrability and profile square-norm estimates control variance transfer. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.CrossExponentDefs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Compact integrability and square-norm inequalities for profile averages. -/

namespace D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer

open Set MeasureTheory Filter
open VarianceTransferDefs CrossExponentDefs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Rescaling gives the unit-interval profile formula, including zero length. -/
theorem profileAverage_eq_unit_integral (E g : ℝ → ℝ) (h x : ℝ) :
    profileAverage E g h x =
      (∫ s in (0 : ℝ)..1, g s * increment E (s * h) x) / h := by
  by_cases hh : h = 0
  · simp [hh, profileAverage]
  have hs := intervalIntegral.smul_integral_comp_mul_right
    (fun u => g (u / h) * increment E u x) (a := 0) (b := 1) h
  simp only [smul_eq_mul, zero_mul, one_mul, mul_div_cancel_right₀ _ hh] at hs
  unfold profileAverage profilePrimitive
  rw [← hs]
  field_simp

/-- Weighted Cauchy–Schwarz with an integrable profile and a bounded measurable factor. -/
theorem profile_cauchy_schwarz {g k : ℝ → ℝ} {M : ℝ}
    (hg : Integrable g unitMeasure)
    (hk : AEStronglyMeasurable k unitMeasure)
    (hM : 0 ≤ M)
    (hbound : ∀ᵐ s ∂unitMeasure, |k s| ≤ M) :
    (∫ s, g s * k s ∂unitMeasure) ^ 2 ≤
      profileL1 g * ∫ s, |g s| * k s ^ 2 ∂unitMeasure := by
  have hki : Integrable (fun s => |g s| * k s ^ 2) unitMeasure :=
    hg.abs.mul_bdd (hk.pow 2) (by
      filter_upwards [hbound] with s hs
      simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hM).mpr hs)
  let f := fun s => Real.sqrt |g s|
  let q := fun s => Real.sqrt |g s| * |k s|
  have hf : MemLp f 2 unitMeasure := by
    apply (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hg.abs.aestronglyMeasurable)).mpr
    simpa [f, Real.sq_sqrt (abs_nonneg _)] using hg.abs
  have hq : MemLp q 2 unitMeasure := by
    apply (memLp_two_iff_integrable_sq
      ((Real.continuous_sqrt.comp_aestronglyMeasurable hg.abs.aestronglyMeasurable).mul
        (by simpa only [Real.norm_eq_abs] using hk.norm))).mpr
    simpa [q, mul_pow, Real.sq_sqrt (abs_nonneg _)] using hki
  have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp f (ENNReal.ofReal 2) unitMeasure by simpa using hf)
    (show MemLp q (ENNReal.ofReal 2) unitMeasure by simpa using hq)
  have hf0 (s : ℝ) : 0 ≤ f s := Real.sqrt_nonneg _
  have hq0 (s : ℝ) : 0 ≤ q s := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  simp only [Real.norm_eq_abs, abs_of_nonneg (hf0 _), abs_of_nonneg (hq0 _),
    Real.rpow_two, ← Real.sqrt_eq_rpow] at hc
  have he : (fun s => f s * q s) = (fun s => |g s * k s|) := by
    funext s
    dsimp [f, q]
    rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _), abs_mul]
  have he2 : (fun s => f s ^ 2) = (fun s => |g s|) := by
    funext s; exact Real.sq_sqrt (abs_nonneg _)
  have he3 : (fun s => q s ^ 2) = (fun s => |g s| * k s ^ 2) := by
    funext s
    simp [q, mul_pow, Real.sq_sqrt (abs_nonneg _)]
  rw [he, he2, he3] at hc
  have hn := (norm_integral_le_integral_norm (fun s => g s * k s)
    (μ := unitMeasure)).trans hc
  simp only [Real.norm_eq_abs] at hn
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hn
  rw [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg (fun s => abs_nonneg (g s))),
    Real.sq_sqrt (integral_nonneg (fun s => mul_nonneg (abs_nonneg _) (sq_nonneg _)))] at hs
  exact hs

lemma interval_cauchy_schwarz {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hf : IntervalIntegrable f volume 0 b)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume 0 b) :
    (∫ t in (0 : ℝ)..b, f t) ^ 2 ≤ b * ∫ t in (0 : ℝ)..b, f t ^ 2 := by
  let μ := volume.restrict (Ioc (0 : ℝ) b)
  have hfi : Integrable f μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mp hf
  have hf2i : Integrable (fun t => f t ^ 2) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mp hf2
  have hmem : MemLp f (ENNReal.ofReal 2) μ := by
    norm_num only [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hfi.aestronglyMeasurable).mpr hf2i
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hmem
    (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) μ)
  have hμ : μ.real Set.univ = b := by simp [μ, Real.volume_Ioc, hb.le]
  simp only [Real.norm_eq_abs, abs_one, mul_one, Real.rpow_two, sq_abs,
    one_pow, integral_const, smul_eq_mul, mul_one, hμ, ← Real.sqrt_eq_rpow] at hh
  have hnorm : |∫ t, f t ∂μ| ≤ Real.sqrt (∫ t, f t ^ 2 ∂μ) * Real.sqrt b :=
    (norm_integral_le_integral_norm f).trans hh
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hnorm
  rw [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _)),
    Real.sq_sqrt hb.le] at hs
  simpa only [intervalIntegral.integral_of_le hb.le, μ, mul_comm] using hs

lemma logarithmic_variance_mono :
    MonotoneOn (fun t : ℝ => t * (Real.log (2 / t)) ^ 2) (Ioc 0 (1 / 16)) := by
  have he (t : ℝ) (ht : 0 < t) : Real.log (2 / t) = Real.log 2 - Real.log t :=
    Real.log_div (by norm_num) ht.ne'
  have hm : MonotoneOn (fun t : ℝ => t * (Real.log 2 - Real.log t) ^ 2)
      (Ioc 0 (1 / 16)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t =>
      (Real.log 2 - Real.log t) ^ 2 - 2 * (Real.log 2 - Real.log t)) (convex_Ioc _ _)
    · exact continuousOn_id.mul ((continuousOn_const.sub
        (Real.continuousOn_log.mono (fun t ht => ne_of_gt ht.1))).pow 2)
    · intro t ht
      have ht0 : 0 < t := (interior_subset ht).1
      have hd := (hasDerivAt_id t).mul
        (((hasDerivAt_const t (Real.log 2)).sub (Real.hasDerivAt_log ht0.ne')).pow 2)
      apply HasDerivAt.hasDerivWithinAt
      convert hd using 1
      · rfl
      · dsimp
        field_simp
        ring
    · intro t ht
      have ht0 : 0 < t := (interior_subset ht).1
      have ht16 : t ≤ 1 / 16 := (interior_subset ht).2
      have hlog : 2 ≤ Real.log 2 - Real.log t := by
        have h := Real.log_le_log ht0 ht16
        have hl : Real.log (1 / 16 : ℝ) = -4 * Real.log 2 := by
          rw [Real.log_div (by norm_num) (by norm_num)]
          norm_num only [Real.log_one, zero_sub]
          rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
          ring
        rw [hl] at h
        linarith [Real.log_two_gt_d9]
      nlinarith
  intro t ht a ha hta
  simpa only [he t ht.1, he a ha.1] using hm ht ha hta

private lemma bounded_comp_on_compact {α : Type*} [TopologicalSpace α]
    {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E) {K : Set α} (hK : IsCompact K)
    {f : α → ℝ} (hf : Continuous f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, |E (f x)| ≤ M := by
  obtain ⟨a, ha⟩ := (hK.image hf).bddBelow
  obtain ⟨b, hb⟩ := (hK.image hf).bddAbove
  obtain ⟨M, hM, hbound⟩ := hE.2 a b
  exact ⟨M, hM, fun x hx => hbound _ ⟨ha (mem_image_of_mem f hx), hb (mem_image_of_mem f hx)⟩⟩

/-- Continuous starting points and steps give uniformly bounded increments on compact sets. -/
lemma bounded_increment_comp {α : Type*} [TopologicalSpace α]
    {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E) {K : Set α} (hK : IsCompact K)
    {u x : α → ℝ} (hu : Continuous u) (hx : Continuous x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ K, |increment E (u p) (x p)| ≤ M := by
  obtain ⟨A, hA, hAb⟩ := bounded_comp_on_compact hE hK (hx.add hu)
  obtain ⟨B, hB, hBb⟩ := bounded_comp_on_compact hE hK hx
  exact ⟨A + B, add_nonneg hA hB, fun p hp =>
    (abs_sub _ _).trans (add_le_add (hAb p hp) (hBb p hp))⟩

/-- Every natural power of a continuous moving increment is integrable on compact sets. -/
lemma increment_pow_integrableOn {A : Type*} [TopologicalSpace A]
    [MeasurableSpace A] [BorelSpace A] [T2Space A]
    {μ : Measure A} [IsFiniteMeasureOnCompacts μ]
    {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {K : Set A} (hK : IsCompact K) {u x : A → ℝ}
    (hu : Continuous u) (hx : Continuous x) (n : ℕ) :
    IntegrableOn (fun p => increment E (u p) (x p) ^ n) K μ := by
  obtain ⟨M, _, hM⟩ := bounded_increment_comp hE hK hu hx
  apply IntegrableOn.of_bound hK.measure_lt_top
    ((((hE.1.comp (hx.add hu).measurable).sub
      (hE.1.comp hx.measurable)).pow_const n).aestronglyMeasurable) (M ^ n)
  filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
  simpa only [Real.norm_eq_abs, abs_pow, Function.comp_apply, Pi.sub_apply, Pi.add_apply,
    increment] using
    pow_le_pow_left₀ (abs_nonneg _) (hM p hp) n

/-- An integrable unit profile times a fixed rescaled increment is integrable. -/
theorem unit_increment_integrable {E g : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : Integrable g unitMeasure)
    (h x : ℝ) :
    Integrable (fun s => g s * increment E (s * h) x) unitMeasure := by
  obtain ⟨M, _, hM⟩ := bounded_increment_comp hE
    (K := Icc (0 : ℝ) 1) isCompact_Icc
    (continuous_id.mul_const h) continuous_const
  apply hg.mul_bdd (c := M)
    (((hE.1.comp (measurable_const.add (measurable_id.mul_const h))).sub
      measurable_const).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact hM s ⟨hs.1.le, hs.2⟩

/-- Continuous choices of starting point and step give integrable increments on compact sets. -/
theorem increment_comp_integrableOn {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [T2Space α]
    {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E) {K : Set α} (hK : IsCompact K)
    {u x : α → ℝ} (hu : Continuous u) (hx : Continuous x) :
    IntegrableOn (fun p => increment E (u p) (x p)) K μ := by
  obtain ⟨M, _, hM⟩ := bounded_increment_comp hE hK hu hx
  apply IntegrableOn.of_bound hK.measure_lt_top
    (((hE.1.comp (hx.add hu).measurable).sub (hE.1.comp hx.measurable)).aestronglyMeasurable) M
  filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
  exact hM p hp

/-- Products of increments with continuous arguments are integrable on compact sets. -/
theorem increment_product_comp_integrableOn {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [T2Space α]
    {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E) {K : Set α} (hK : IsCompact K)
    {u x v y : α → ℝ} (hu : Continuous u) (hx : Continuous x)
    (hv : Continuous v) (hy : Continuous y) :
    IntegrableOn (fun p => increment E (u p) (x p) * increment E (v p) (y p)) K μ := by
  obtain ⟨A, hA, hAb⟩ := bounded_increment_comp hE hK hu hx
  obtain ⟨B, hB, hBb⟩ := bounded_increment_comp hE hK hv hy
  have hm (f g : α → ℝ) (hf : Continuous f) (hg : Continuous g) :
      Measurable (fun p => increment E (f p) (g p)) :=
    (hE.1.comp (hg.add hf).measurable).sub (hE.1.comp hg.measurable)
  apply IntegrableOn.of_bound hK.measure_lt_top
    ((hm u x hu hx).mul (hm v y hv hy)).aestronglyMeasurable (A * B)
  filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
  simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul] using
    mul_le_mul (hAb p hp) (hBb p hp) (abs_nonneg _) hA

/-- Joint increment squares are integrable on finite rectangles, also for variable continuous steps. -/
theorem increment_sq_rectangle_integrable {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (a b c d : ℝ) {u : ℝ × ℝ → ℝ} (hu : Continuous u) :
    Integrable (fun p : ℝ × ℝ => increment E (u p) p.1 ^ 2)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
  rw [Measure.prod_restrict]
  have hi := increment_product_comp_integrableOn (μ := volume.prod volume) hE
    (K := Icc a b ×ˢ Icc c d) (isCompact_Icc.prod isCompact_Icc) hu continuous_fst hu continuous_fst
  simpa only [pow_two, IntegrableOn] using hi.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- The `L²` norm on an interval is the corresponding `lpNorm` on its restricted measure. -/
theorem lpNorm_two_eq_intervalL2 {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioc a b))) :
    lpNorm f 2 (volume.restrict (Ioc a b)) = intervalL2 a b f := by
  simpa [intervalL2, NNReal.coe_ofNat, NNReal.coe_inv, Real.norm_eq_abs,
    Real.rpow_two, sq_abs, Real.sqrt_eq_rpow, one_div,
    intervalIntegral.integral_of_le hab] using
    lpNorm_nnreal_eq_integral_norm_rpow (p := (2 : NNReal)) (by norm_num) hf

/-- The square-root integral norm satisfies the reverse triangle inequality on an interval. -/
theorem interval_l2_reverse_triangle {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Ioc a b))) :
    |Real.sqrt (∫ x in a..b, f x ^ 2) - Real.sqrt (∫ x in a..b, g x ^ 2)| ≤
      Real.sqrt (∫ x in a..b, (f x - g x) ^ 2) := by
  have hfg := lpNorm_le_lpNorm_add_lpNorm_sub' (f := f) hg (by norm_num : (1 : ENNReal) ≤ 2)
  have hgf := lpNorm_le_lpNorm_add_lpNorm_sub (f := g) hf (by norm_num : (1 : ENNReal) ≤ 2)
  rw [lpNorm_two_eq_intervalL2 hab hf.aestronglyMeasurable,
    lpNorm_two_eq_intervalL2 hab hg.aestronglyMeasurable,
    lpNorm_two_eq_intervalL2 hab (hf.sub hg).aestronglyMeasurable] at hfg hgf
  have hfg' : Real.sqrt (∫ x in a..b, f x ^ 2) ≤
      Real.sqrt (∫ x in a..b, g x ^ 2) +
        Real.sqrt (∫ x in a..b, (f x - g x) ^ 2) := by
    simpa only [intervalL2, Pi.sub_apply] using hfg
  have hgf' : Real.sqrt (∫ x in a..b, g x ^ 2) ≤
      Real.sqrt (∫ x in a..b, f x ^ 2) +
        Real.sqrt (∫ x in a..b, (f x - g x) ^ 2) := by
    simpa only [intervalL2, Pi.sub_apply] using hgf
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The integral of the covariance kernel min(s,t) on the unit square is one third. -/
theorem integral_min_unit_square :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, min s t) = (1 / 3 : ℝ) := by
  have hinner (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (∫ t in (0 : ℝ)..1, min s t) = s - s ^ 2 / 2 := by
    have hi : Continuous (fun t : ℝ => min s t) := continuous_const.min continuous_id
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hi.intervalIntegrable 0 s) (hi.intervalIntegrable s 1)]
    have hleft : (∫ t in (0 : ℝ)..s, min s t) = ∫ t in (0 : ℝ)..s, t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hs.1] at ht
      exact min_eq_right ht.2
    have hright : (∫ t in s..(1 : ℝ), min s t) = ∫ _t in s..(1 : ℝ), s := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hs.2] at ht
      exact min_eq_left ht.1
    rw [hleft, hright, integral_id, intervalIntegral.integral_const]
    simp only [sub_zero, zero_pow (by decide : 2 ≠ 0), smul_eq_mul]
    ring
  calc
    _ = ∫ s in (0 : ℝ)..1, (s - s ^ 2 / 2) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact hinner s (by simpa using hs)
    _ = _ := by
      rw [intervalIntegral.integral_sub
        ((show Continuous (fun s : ℝ => s) from continuous_id).intervalIntegrable 0 1)
        ((show Continuous (fun s : ℝ => s ^ 2 / 2) by fun_prop).intervalIntegrable 0 1),
        intervalIntegral.integral_div, integral_id, integral_pow]
      norm_num

end
end D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer
