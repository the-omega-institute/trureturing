/- GID: D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/VarianceTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact integrability and interval square-norm estimates transfer short-interval variance bounds to triangular primitives. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer

open Set MeasureTheory Filter
open VarianceTransferDefs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

private lemma bounded_increment_comp {α : Type*} [TopologicalSpace α]
    {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E) {K : Set α} (hK : IsCompact K)
    {u x : α → ℝ} (hu : Continuous u) (hx : Continuous x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ K, |increment E (u p) (x p)| ≤ M := by
  obtain ⟨A, hA, hAb⟩ := bounded_comp_on_compact hE hK (hx.add hu)
  obtain ⟨B, hB, hBb⟩ := bounded_comp_on_compact hE hK hx
  exact ⟨A + B, add_nonneg hA hB, fun p hp =>
    (abs_sub _ _).trans (add_le_add (hAb p hp) (hBb p hp))⟩

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

/-- A fixed-length triangular primitive is measurable as a function of its starting point. -/
theorem triangularPrimitive_measurable {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (h : ℝ) : Measurable (triangularPrimitive E h) := by
  have hm : Measurable (fun p : ℝ × ℝ => increment E p.2 p.1) :=
    (hE.1.comp (measurable_fst.add measurable_snd)).sub (hE.1.comp measurable_fst)
  unfold triangularPrimitive intervalIntegral
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 h))).measurable.sub
    (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc h 0))).measurable

/-- Squares of fixed-length triangular primitives are integrable on finite intervals. -/
theorem triangularPrimitive_sq_intervalIntegrable {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (h a b : ℝ) :
    IntervalIntegrable (fun x => triangularPrimitive E h x ^ 2) volume a b := by
  obtain ⟨M, hM, hb⟩ := bounded_increment_comp hE
    (K := uIcc a b ×ˢ uIcc 0 h) (isCompact_uIcc.prod isCompact_uIcc)
    continuous_snd continuous_fst
  have hbound (x : ℝ) (hx : x ∈ uIcc a b) :
      |triangularPrimitive E h x| ≤ M * |h| := by
    simpa only [triangularPrimitive, Real.norm_eq_abs, sub_zero] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := h)
        (f := fun u => increment E u x) (fun u hu => hb (x, u) ⟨hx, uIoc_subset_uIcc hu⟩))
  apply IntegrableOn.intervalIntegrable
  apply IntegrableOn.of_bound isCompact_uIcc.measure_lt_top
    ((triangularPrimitive_measurable hE h).pow_const 2).aestronglyMeasurable ((M * |h|) ^ 2)
  filter_upwards [ae_restrict_mem measurableSet_uIcc] with x hx
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
    pow_le_pow_left₀ (abs_nonneg _) (hbound x hx) 2

/-- The square-root integral norm satisfies the reverse triangle inequality on an interval. -/
theorem interval_l2_reverse_triangle {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Ioc a b))) :
    |Real.sqrt (∫ x in a..b, f x ^ 2) - Real.sqrt (∫ x in a..b, g x ^ 2)| ≤
      Real.sqrt (∫ x in a..b, (f x - g x) ^ 2) := by
  let μ := volume.restrict (Ioc a b)
  have hn (q : ℝ → ℝ) (hq : AEStronglyMeasurable q μ) :
      lpNorm q 2 μ = Real.sqrt (∫ x in a..b, q x ^ 2) := by
    simpa [NNReal.coe_ofNat, NNReal.coe_inv, Real.norm_eq_abs, Real.rpow_two,
      sq_abs, Real.sqrt_eq_rpow, one_div, intervalIntegral.integral_of_le hab, μ]
      using lpNorm_nnreal_eq_integral_norm_rpow (p := (2 : NNReal)) (by norm_num) hq
  have hfg := lpNorm_le_lpNorm_add_lpNorm_sub' (f := f) hg (by norm_num : (1 : ENNReal) ≤ 2)
  have hgf := lpNorm_le_lpNorm_add_lpNorm_sub (f := g) hf (by norm_num : (1 : ENNReal) ≤ 2)
  rw [hn f hf.aestronglyMeasurable, hn g hg.aestronglyMeasurable,
    hn (f - g) (hf.sub hg).aestronglyMeasurable] at hfg hgf
  simp only [Pi.sub_apply] at hfg hgf
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

private lemma triangularPrimitive_sq_rectangle_le {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) {X U x : ℝ} (hX : 0 < X) (hU : 0 < U)
    (hx : x ∈ Icc X (2 * X)) :
    triangularPrimitive E U x ^ 2 ≤ 2 * U * X *
      ∫ θ in (0 : ℝ)..(U / X), increment E (θ * x) x ^ 2 := by
  have hx0 : 0 < x := hX.trans_le hx.1
  have hf : IntervalIntegrable (fun u => increment E u x) volume 0 U :=
    (increment_comp_integrableOn hE isCompact_uIcc continuous_id continuous_const).intervalIntegrable
  have hf2 : IntervalIntegrable (fun u => increment E u x ^ 2) volume 0 U := by
    simpa only [pow_two, id_eq, Pi.mul_apply] using
      (increment_product_comp_integrableOn hE isCompact_uIcc
        continuous_id continuous_const continuous_id continuous_const).intervalIntegrable
  have hcs := interval_cauchy_schwarz hU hf hf2
  have hs := intervalIntegral.smul_integral_comp_mul_right
    (fun u => increment E u x ^ 2) (a := 0) (b := U / x) x
  simp only [smul_eq_mul, zero_mul, div_mul_cancel₀ _ hx0.ne'] at hs
  have hi : IntervalIntegrable (fun θ => increment E (θ * x) x ^ 2) volume 0 (U / X) := by
    simpa only [pow_two, id_eq, Pi.mul_apply] using
      (increment_product_comp_integrableOn hE isCompact_uIcc
        (continuous_id.mul continuous_const) continuous_const
        (continuous_id.mul continuous_const) continuous_const).intervalIntegrable
  have hmono := intervalIntegral.integral_mono_interval (le_refl (0 : ℝ))
    (div_nonneg hU.le hx0.le) (div_le_div_of_nonneg_left hU.le hX hx.1)
    (Eventually.of_forall (fun θ => sq_nonneg (increment E (θ * x) x))) hi
  have hnonneg := intervalIntegral.integral_nonneg_of_forall (μ := volume)
    (div_nonneg hU.le hX.le) (fun θ => sq_nonneg (increment E (θ * x) x))
  calc
    _ ≤ U * ∫ u in (0 : ℝ)..U, increment E u x ^ 2 := hcs
    _ = U * x * ∫ θ in (0 : ℝ)..(U / x), increment E (θ * x) x ^ 2 := by
      rw [← hs]; ring
    _ ≤ U * x * ∫ θ in (0 : ℝ)..(U / X), increment E (θ * x) x ^ 2 :=
      mul_le_mul_of_nonneg_left hmono (mul_nonneg hU.le hx0.le)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [hx.2]) hnonneg

/-- Short-interval mean-square bounds control triangular primitives uniformly for small lengths. -/
theorem small_length_triangular_square_bound
    {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (hSV : ShortIntervalMeanSquareBoundFor E) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in Filter.atTop,
      ∀ U : ℝ, 0 < U → U ≤ X / 16 →
        (∫ x in X..(2 * X), triangularPrimitive E U x ^ 2) ≤
          C * X * U ^ 3 * (Real.log (2 * X / U)) ^ 2 := by
  obtain ⟨C, Y, hC, hY, hSV⟩ := hSV
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop Y] with X hXY
  intro U hU hUX
  have hX : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  let a := U / X
  have ha : 0 < a := div_pos hU hX
  have ha16 : a ≤ 1 / 16 := by dsimp [a]; apply (div_le_iff₀ hX).mpr; linarith
  have ha1 : a ≤ 1 := by linarith
  have hi := increment_sq_rectangle_integrable hE X (2 * X) 0 a
    (u := fun p => p.2 * p.1) (by fun_prop)
  have hG : IntervalIntegrable (fun x => 2 * U * X *
      ∫ θ in (0 : ℝ)..a, increment E (θ * x) x ^ 2) volume X (2 * X) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hXX]
    simpa only [IntegrableOn, intervalIntegral.integral_of_le ha.le] using
      hi.integral_prod_left.const_mul (2 * U * X)
  have hrect : (∫ x in X..(2 * X), ∫ θ in (0 : ℝ)..a, increment E (θ * x) x ^ 2) ≤
      C * X ^ 2 * a ^ 2 * (Real.log (2 / a)) ^ 2 := by
    simp_rw [intervalIntegral.integral_of_le hXX, intervalIntegral.integral_of_le ha.le]
    rw [integral_integral_swap hi]
    calc
      _ ≤ ∫ _θ in Ioc (0 : ℝ) a, C * X ^ 2 * (a * (Real.log (2 / a)) ^ 2) := by
        apply setIntegral_mono_on hi.integral_prod_right (integrableOn_const (by simp))
          measurableSet_Ioc
        intro θ hθ
        have he : (fun x => increment E (θ * x) x ^ 2) =
            (fun x => (E ((1 + θ) * x) - E x) ^ 2) := by
          funext x
          simp only [increment, show x + θ * x = (1 + θ) * x by ring]
        have h := hSV X hXY θ hθ.1 (hθ.2.trans ha1)
        rw [← he, intervalIntegral.integral_of_le hXX] at h
        have hl := logarithmic_variance_mono ⟨hθ.1, hθ.2.trans ha16⟩ ⟨ha, ha16⟩ hθ.2
        have hl' := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ C * X ^ 2)
        exact h.trans (by nlinarith [hl'])
      _ = _ := by
        rw [setIntegral_const, Measure.real, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith : 0 ≤ a - 0), smul_eq_mul]
        ring
  calc
    _ ≤ ∫ x in X..(2 * X), 2 * U * X *
        ∫ θ in (0 : ℝ)..a, increment E (θ * x) x ^ 2 :=
      intervalIntegral.integral_mono_on hXX
        (triangularPrimitive_sq_intervalIntegrable hE U X (2 * X)) hG
        (fun x hx => triangularPrimitive_sq_rectangle_le hE hX hU hx)
    _ = 2 * U * X * (∫ x in X..(2 * X),
        ∫ θ in (0 : ℝ)..a, increment E (θ * x) x ^ 2) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ 2 * U * X * (C * X ^ 2 * a ^ 2 * (Real.log (2 / a)) ^ 2) :=
      mul_le_mul_of_nonneg_left hrect (by positivity)
    _ = _ := by
      have he : 2 / a = 2 * X / U := by dsimp [a]; field_simp
      rw [he]
      dsimp [a]
      field_simp

end
end D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer
