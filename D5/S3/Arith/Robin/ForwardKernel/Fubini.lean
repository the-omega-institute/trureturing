/- GID: D5/S3/Arith/Robin/ForwardKernel/Fubini
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/Fubini
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute Fubini transports the complete forward Mellin response to its actual adjoint. -/

import D5.S3.Arith.Robin.ForwardKernel.Adjoint
import D5.S3.Arith.Robin.ForwardKernel.MellinConvergence
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Absolute integrability transports the actual complete arithmetic mass to the Mellin adjoint. -/

namespace D5.S3.Arith.Robin.ForwardKernel.Fubini

open Set Filter MeasureTheory
open scoped Topology
open OriginalMovingWindowMoment (width endpoint kernel moment)
open ForwardKernel.Transport (forwardResponse)
open ForwardKernel.Adjoint (adjointKernel)
open ActualVonMangoldtBandCompensation (weightedPrefix)
open ForwardKernel.MellinConvergence (forwardMellin kernel_volume_eq_moment)

noncomputable section

private lemma kernel_row_integrable {x : ℝ} (hx : 4 ≤ x) : Integrable (kernel x) := by
  have hm : Measurable (kernel x) :=
    OriginalMovingCutAggregate.measurable_kernel_joint.comp (measurable_const.prodMk measurable_id)
  have hi : IntegrableOn (kernel x) (Icc x (endpoint x)) := by
    apply (integrableOn_const (C := (1 : ℝ)) (by simp : volume (Icc x (endpoint x)) ≠ ⊤)).mono'
      hm.aestronglyMeasurable
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (OriginalMovingCutRow.kernel_nonneg hx)]
    exact OriginalMovingCutRow.kernel_le_one hx
  apply hi.integrable_of_forall_notMem_eq_zero
  intro t ht
  unfold kernel
  apply if_neg
  intro h
  exact ht ⟨h.1.le, h.2⟩

private lemma kernel_row_zero {x : ℝ} {i : ℕ} (hi : i ∉ Finset.range ⌊endpoint x⌋₊) :
    kernel x ((i + 1 : ℕ) : ℝ) = 0 := by
  have hni : ⌊endpoint x⌋₊ < i + 1 := by
    have : ⌊endpoint x⌋₊ ≤ i := by simpa only [Finset.mem_range, not_lt] using hi
    omega
  have hB : endpoint x < ((i + 1 : ℕ) : ℝ) := Nat.lt_of_floor_lt hni
  unfold kernel
  apply if_neg
  exact fun h => (not_le_of_gt hB) h.2

private lemma counting_row_integrable (x : ℝ) (c : ℂ) :
    Integrable (fun i : ℕ => (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
      (c * (kernel x ((i + 1 : ℕ) : ℝ) : ℂ))) Measure.count := by
  apply integrable_count_iff.mpr
  apply summable_of_ne_finset_zero (s := Finset.range ⌊endpoint x⌋₊)
  intro i hi
  rw [kernel_row_zero hi]
  simp

private lemma counting_row_norm {x : ℝ} (hx : 4 ≤ x) (c : ℂ) :
    (∫ i : ℕ, ‖(ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
      (c * (kernel x ((i + 1 : ℕ) : ℝ) : ℂ))‖ ∂Measure.count) =
      ‖c‖ * weightedPrefix (kernel x) (endpoint x) := by
  have hi := (counting_row_integrable x c).norm
  have he := integral_countable hi
  simp only [Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul] at he
  rw [he, tsum_eq_sum (s := Finset.range ⌊endpoint x⌋₊) (fun i hi => by
    rw [kernel_row_zero hi]; simp)]
  unfold weightedPrefix QuotientIntegralBudget.arithmeticPrefix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg), Real.norm_eq_abs,
    abs_of_nonneg (OriginalMovingCutRow.kernel_nonneg hx)]
  ring

private lemma volume_row_norm {x : ℝ} (hx : 4 ≤ x) (c : ℂ) :
    (∫ t : ℝ, ‖c * (kernel x t : ℂ)‖) = ‖c‖ * moment x 0 := by
  calc
    _ = ∫ t : ℝ, ‖c‖ * kernel x t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by
        dsimp only
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (OriginalMovingCutRow.kernel_nonneg hx)])
    _ = _ := by rw [integral_const_mul, kernel_volume_eq_moment hx]

private lemma weighted_volume_product_integrable {x0 : ℝ} (hx0 : 4 ≤ x0)
    {f : ℝ → ℂ} (hf : Measurable f)
    (hV : IntegrableOn (fun x => ‖f x‖ * moment x 0) (Ici x0)) :
    Integrable (fun p : ℝ × ℝ => f p.1 * (kernel p.1 p.2 : ℂ))
      ((volume.restrict (Ici x0)).prod volume) := by
  have hm : Measurable (fun p : ℝ × ℝ => f p.1 * (kernel p.1 p.2 : ℂ)) :=
    (hf.comp measurable_fst).mul
      (Complex.measurable_ofReal.comp OriginalMovingCutAggregate.measurable_kernel_joint)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    exact (kernel_row_integrable (hx0.trans hx)).ofReal.const_mul (f x)
  · apply hV.congr_fun _ measurableSet_Ici
    intro x hx
    exact (volume_row_norm (hx0.trans hx) (f x)).symm

private lemma weighted_arithmetic_product_integrable {x0 : ℝ} (hx0 : 4 ≤ x0)
    {f : ℝ → ℂ} (hf : Measurable f)
    (hT : IntegrableOn (fun x => ‖f x‖ * |forwardResponse x|) (Ici x0))
    (hV : IntegrableOn (fun x => ‖f x‖ * moment x 0) (Ici x0)) :
    Integrable (fun p : ℝ × ℕ => (ArithmeticFunction.vonMangoldt (p.2 + 1) : ℂ) *
      (f p.1 * (kernel p.1 ((p.2 + 1 : ℕ) : ℝ) : ℂ)))
      ((volume.restrict (Ici x0)).prod Measure.count) := by
  have hk : Measurable (fun p : ℝ × ℕ => kernel p.1 ((p.2 + 1 : ℕ) : ℝ)) :=
    OriginalMovingCutAggregate.measurable_kernel_joint.comp
      (measurable_fst.prodMk
        ((measurable_of_countable (f := fun i : ℕ => ((i + 1 : ℕ) : ℝ))).comp measurable_snd))
  have hv : Measurable (fun p : ℝ × ℕ => (ArithmeticFunction.vonMangoldt (p.2 + 1) : ℂ)) :=
    (measurable_of_countable
      (fun i : ℕ => (ArithmeticFunction.vonMangoldt (i + 1) : ℂ))).comp measurable_snd
  have hm : Measurable (fun p : ℝ × ℕ => (ArithmeticFunction.vonMangoldt (p.2 + 1) : ℂ) *
      (f p.1 * (kernel p.1 ((p.2 + 1 : ℕ) : ℝ) : ℂ))) :=
    hv.mul
      ((hf.comp measurable_fst).mul (Complex.measurable_ofReal.comp hk))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun x => counting_row_integrable x (f x))
  · have hmajor : IntegrableOn (fun x => ‖f x‖ * (|forwardResponse x| + moment x 0)) (Ici x0) := by
      convert hT.add hV using 1
      funext x
      change ‖f x‖ * (|forwardResponse x| + moment x 0) =
        ‖f x‖ * |forwardResponse x| + ‖f x‖ * moment x 0
      exact mul_add _ _ _
    apply hmajor.mono' hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    have hx4 : 4 ≤ x := hx0.trans hx
    rw [counting_row_norm (hx0.trans hx)]
    have hrow : 0 ≤ weightedPrefix (kernel x) (endpoint x) := by
      unfold weightedPrefix QuotientIntegralBudget.arithmeticPrefix
      exact Finset.sum_nonneg (fun _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (OriginalMovingCutRow.kernel_nonneg (hx0.trans hx)))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hrow)]
    have hresponse := ForwardKernel.Adjoint.forwardResponse_eq_prefix_kernel
      (show 1 < x by linarith)
    have hv : (∫ t in x..endpoint x, kernel x t) = moment x 0 := by
      simp [moment]
    rw [hv] at hresponse
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    linarith [le_abs_self (forwardResponse x)]

private lemma counting_row_value (x : ℝ) (c : ℂ) :
    (∫ i : ℕ, (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
      (c * (kernel x ((i + 1 : ℕ) : ℝ) : ℂ)) ∂Measure.count) =
      c * (weightedPrefix (kernel x) (endpoint x) : ℂ) := by
  have he := integral_countable (counting_row_integrable x c)
  simp only [Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul] at he
  rw [he, tsum_eq_sum (s := Finset.range ⌊endpoint x⌋₊) (fun i hi => by
    rw [kernel_row_zero hi]; simp)]
  unfold weightedPrefix QuotientIntegralBudget.arithmeticPrefix
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Absolute Fubini preserves the complete signed forward response. -/
theorem unbounded_forward_adjoint {x0 : ℝ} (hx0 : 4 ≤ x0)
    {f : ℝ → ℂ} (hf : Measurable f)
    (hT : IntegrableOn (fun x => ‖f x‖ * |forwardResponse x|) (Ici x0))
    (hV : IntegrableOn (fun x => ‖f x‖ * moment x 0) (Ici x0)) :
    Integrable (fun t : ℝ => ∫ x in Ici x0, f x * (kernel x t : ℂ)) ∧
    Summable (fun i : ℕ => (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
      ∫ x in Ici x0, f x * (kernel x ((i + 1 : ℕ) : ℝ) : ℂ)) ∧
    (∫ x in Ici x0, f x * (forwardResponse x : ℂ)) =
      (∑' i : ℕ, (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
        ∫ x in Ici x0, f x * (kernel x ((i + 1 : ℕ) : ℝ) : ℂ)) -
        ∫ t : ℝ, ∫ x in Ici x0, f x * (kernel x t : ℂ) := by
  have hA := weighted_arithmetic_product_integrable hx0 hf hT hV
  have hB := weighted_volume_product_integrable hx0 hf hV
  have hAi : Integrable (fun i : ℕ => (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
      ∫ x in Ici x0, f x * (kernel x ((i + 1 : ℕ) : ℝ) : ℂ)) Measure.count := by
    simpa only [integral_const_mul] using hA.integral_prod_right
  refine ⟨hB.integral_prod_right, (integrable_count_iff.mp hAi).of_norm, ?_⟩
  have hAI := integral_integral_swap
    (f := fun (x : ℝ) (i : ℕ) => (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
      (f x * (kernel x ((i + 1 : ℕ) : ℝ) : ℂ))) hA
  have hBI := integral_integral_swap
    (f := fun (x : ℝ) (t : ℝ) => f x * (kernel x t : ℂ)) hB
  simp only [integral_const_mul] at hAI
  rw [integral_countable hAi] at hAI
  simp only [Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul] at hAI
  rw [← hAI, ← hBI, ← integral_sub hA.integral_prod_left hB.integral_prod_left]
  apply setIntegral_congr_fun measurableSet_Ici
  intro x hx
  have hx4 : 4 ≤ x := hx0.trans hx
  dsimp only
  rw [counting_row_value, integral_const_mul, integral_complex_ofReal,
    kernel_volume_eq_moment hx4, ← mul_sub, ← Complex.ofReal_sub]
  congr 2
  have hresponse := ForwardKernel.Adjoint.forwardResponse_eq_prefix_kernel
    (show 1 < x by linarith)
  simpa [moment] using hresponse

#print axioms unbounded_forward_adjoint

private lemma adjointKernel_below_one {x0 t : ℝ} (hx0 : 4 ≤ x0)
    (ht : t ≤ 1) (s : ℂ) : adjointKernel x0 s t = 0 := by
  unfold adjointKernel
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  have htx : ¬ x < t := by have : x0 ≤ x := hx; linarith
  simp [kernel, htx]

/-- The complete signed adjoint truncations converge to the original Mellin integral. -/
theorem forwardMellin_adjoint_tendsto
    {α : ℝ} (hα : 0 ≤ α)
    (hE : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ α)
    {x0 : ℝ} (hx0 : 4 ≤ x0) {s : ℂ} (hs : max (1 / 2) (α - 3 / 10) < s.re) :
    IntegrableOn (adjointKernel x0 s) (Ioi (1 : ℝ)) ∧
    Tendsto (fun b : ℝ =>
      (∑ n ∈ Finset.Icc 0 ⌊b⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℂ) * adjointKernel x0 s n) -
      ∫ t in (1 : ℝ)..b, adjointKernel x0 s t)
      atTop (𝓝 (forwardMellin x0 s)) := by
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ (-s - 1)
  have hf : Measurable f := Complex.measurable_ofReal.pow_const _
  have hT : IntegrableOn (fun x => ‖f x‖ * |forwardResponse x|) (Ici x0) := by
    have hi : IntegrableOn
        (fun x : ℝ => ‖(forwardResponse x : ℂ) * (x : ℂ) ^ (-s - 1)‖) (Ioi x0) :=
      (ForwardKernel.MellinConvergence.forwardMellin_integrable hα hE
        (show 3 ≤ x0 by linarith) (lt_of_le_of_lt (le_max_right _ _) hs)).norm
    have hi' := (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hi
    simpa only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm] using hi'
  have hV := ForwardKernel.MellinConvergence.kernel_mellin_majorant_integrable hx0 (lt_of_le_of_lt (le_max_left _ _) hs)
  obtain ⟨hq, hsum, hidentity⟩ := unbounded_forward_adjoint hx0 hf hT hV
  change Integrable (adjointKernel x0 s) at hq
  change Summable (fun i : ℕ =>
    (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
      adjointKernel x0 s ((i + 1 : ℕ) : ℝ)) at hsum
  refine ⟨hq.integrableOn, ?_⟩
  have hcontinuous : (∫ t : ℝ, adjointKernel x0 s t) =
      ∫ t in Ioi (1 : ℝ), adjointKernel x0 s t := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    exact adjointKernel_below_one hx0 (le_of_not_gt ht) s
  have hcenter : (∫ x in Ici x0, f x * (forwardResponse x : ℂ)) =
      forwardMellin x0 s := by
    rw [integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    exact mul_comm _ _
  change (∫ x in Ici x0, f x * (forwardResponse x : ℂ)) =
    (∑' i : ℕ, (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
      adjointKernel x0 s ((i + 1 : ℕ) : ℝ)) - ∫ t : ℝ, adjointKernel x0 s t at hidentity
  rw [hcenter, hcontinuous] at hidentity
  let a : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) *
    adjointKernel x0 s n
  have hAll : Summable a := (summable_nat_add_iff 1).mp hsum
  have htail : (∑' n : ℕ, a n) = ∑' i : ℕ, a (i + 1) := by
    rw [hAll.tsum_eq_zero_add]
    simp [a]
  have hlim := hAll.hasSum.tendsto_sum_nat.comp
    ((tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop (α := ℝ)))
  change Tendsto (fun b : ℝ => ∑ n ∈ Finset.range (⌊b⌋₊ + 1), a n)
    atTop (𝓝 (∑' n : ℕ, a n)) at hlim
  have hlim' : Tendsto (fun b : ℝ => ∑ n ∈ Finset.Icc 0 ⌊b⌋₊, a n)
      atTop (𝓝 (∑' n : ℕ, a n)) := by
    simpa only [Nat.range_succ_eq_Icc_zero] using hlim
  have hlimV := intervalIntegral_tendsto_integral_Ioi (1 : ℝ) hq.integrableOn
    (tendsto_id : Tendsto (fun b : ℝ => b) atTop atTop)
  have htotal := hlim'.sub hlimV
  rw [htail, ← hidentity] at htotal
  exact htotal

#print axioms forwardMellin_adjoint_tendsto

end

end D5.S3.Arith.Robin.ForwardKernel.Fubini
