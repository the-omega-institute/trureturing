/- GID: D5/S3/Arith/Robin/ActualFactorialCumulativePositivity
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualFactorialCumulativePositivity
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Signed factorial cumulative positivity controls the complete Robin high integral. -/

import D5.S3.Arith.Robin.ActualFactorialRobinHighDerivative
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
The signed error is the actual factorial residual, not a pointwise positive
replacement. The scalar lower bound is consumed from its original owner,
LogConvolutionMassExpansion, preserving the Terence Tao / Apache 2.0 attribution
there. Fubini is paid with a separable absolute majorant on the entire high domain.
No low-part sign, odd Mobius prefix estimate, Robin inequality or RH is proved.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Robin.ActualFactorialCumulativePositivity

open ActualFactorialRobinHighDerivative (eta highRemainder highIntegrand)
open QuotientIntegralBudget (integrableOn_log_tail integral_log_tail measurable_residual)
open D5.S3.Arith.LogConvolutionMassExpansion
  (sum_log_floor_lower sum_log_eq_log_factorial)

def density (y : ℝ) : ℝ := eta y / y ^ 2

/-- Cumulative signed mass, including its actual lower endpoint. -/
def cumulative (Y : ℝ) : ℝ := ∫ y in (1 : ℝ)..Y, density y

def kappa : ℝ := Real.log 2 * (1 - Real.log 2) / 2

private lemma density_measurable : Measurable density := by
  have hm : Measurable eta := measurable_residual (fun n : ℕ => Real.log n) 1 1
  exact hm.div (measurable_id.pow_const 2)

private lemma density_lower {y : ℝ} (hy : 1 ≤ y) :
    (1 - Real.log y) / y ^ 2 ≤ density y := by
  have hl := sum_log_floor_lower hy
  rw [sum_log_eq_log_factorial] at hl
  have he := ActualFactorialRobinHighDerivative.result.1 y
  apply div_le_div_of_nonneg_right _ (sq_nonneg y)
  linarith

private lemma density_abs {y : ℝ} (hy : 1 ≤ y) :
    |density y| ≤ (1 + Real.log y) / y ^ 2 := by
  have he := ActualFactorialRobinHighDerivative.kernelData.residual_high y hy
  change |eta y| ≤ 1 * (1 + Real.log y) at he
  rw [density, abs_div, abs_of_nonneg (sq_nonneg y)]
  exact div_le_div_of_nonneg_right (by simpa using he) (sq_nonneg y)

private lemma density_integrable : IntegrableOn density (Ioi (1 : ℝ)) := by
  apply (integrableOn_log_tail (by norm_num : (1 : ℝ) ≤ 1)).mono'
    density_measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simpa only [Real.norm_eq_abs] using density_abs hy.le

private lemma density_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable density volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  exact density_integrable.mono_set (fun y hy => lt_of_le_of_lt ha hy.1)

private lemma lower_primitive {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => Real.log z / z) ((1 - Real.log y) / y ^ 2) y := by
  apply ((Real.hasDerivAt_log hy.ne').div (hasDerivAt_id y) hy.ne').congr_deriv
  simp only [id_eq]
  field_simp [hy.ne']

private lemma lower_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun y : ℝ => (1 - Real.log y) / y ^ 2) volume a b := by
  apply ContinuousOn.intervalIntegrable _
  rw [uIcc_of_le hab]
  have hlog : ContinuousOn Real.log (Icc a b) :=
    Real.continuousOn_log.mono (fun y hy =>
      ne_of_gt (zero_lt_one.trans_le (ha.trans hy.1)))
  exact (continuousOn_const.sub hlog).div (continuousOn_id.pow 2)
    (fun y hy => pow_ne_zero _ (ne_of_gt (zero_lt_one.trans_le (ha.trans hy.1))))

private lemma upper_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun y : ℝ => (1 + Real.log y) / y ^ 2) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  exact (integrableOn_log_tail (by norm_num : (1 : ℝ) ≤ 1)).mono_set
    (fun y hy => lt_of_le_of_lt ha hy.1)

private lemma cumulative_lower {Y : ℝ} (hY : 1 ≤ Y) :
    Real.log Y / Y ≤ cumulative Y := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => lower_primitive (show 0 < y by
      rw [uIcc_of_le hY] at hy
      linarith [hy.1])) (lower_interval (by norm_num) hY)
  simp only [Real.log_one, zero_div, sub_zero] at hFTC
  rw [← hFTC]
  apply intervalIntegral.integral_mono_on hY (lower_interval (by norm_num) hY)
    (density_interval (by norm_num) hY)
  intro y hy
  exact density_lower hy.1

private lemma cumulative_upper {Y : ℝ} (hY : 1 ≤ Y) :
    cumulative Y ≤ 2 - (Real.log Y + 2) / Y := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => QuotientIntegralBudget.hasDerivAt_log_tail_primitive (show 0 < y by
      rw [uIcc_of_le hY] at hy
      linarith [hy.1])) (upper_interval (by norm_num) hY)
  have hm : cumulative Y ≤ ∫ y in (1 : ℝ)..Y, (1 + Real.log y) / y ^ 2 := by
    apply intervalIntegral.integral_mono_on hY (density_interval (by norm_num) hY)
      (upper_interval (by norm_num) hY)
    intro y hy
    exact (le_abs_self _).trans (density_abs hy.1)
  rw [hFTC] at hm
  simpa only [Real.log_one, zero_add, div_one, neg_sub_neg, neg_div] using hm

private lemma cumulative_two : cumulative 2 = Real.log 2 - (Real.log 2) ^ 2 / 2 := by
  have heq : cumulative 2 = ∫ y in (1 : ℝ)..2, (1 - Real.log y) / y := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro y hy
    have hf : ⌊y⌋₊ = 1 := by
      apply (Nat.floor_eq_iff (zero_lt_one.trans hy.1).le).mpr
      constructor <;> norm_num <;> linarith [hy.1, hy.2]
    rw [density, ActualFactorialRobinHighDerivative.result.1, hf]
    simp only [Nat.factorial_one, Nat.cast_one, Real.log_one, zero_sub]
    field_simp
    ring
  rw [heq]
  have h := QuotientIntegralBudget.integral_affine_log_div
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 2) 1 (-1)
  simp only [neg_one_mul, ← sub_eq_add_neg, Real.log_one, sub_zero, one_mul,
    zero_pow (by norm_num : 2 ≠ 0)] at h
  rw [h]
  ring

private lemma cumulative_improved {Y : ℝ} (hY : 2 ≤ Y) :
    kappa + Real.log Y / Y ≤ cumulative Y := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => lower_primitive (show 0 < y by
      rw [uIcc_of_le hY] at hy
      linarith [hy.1])) (lower_interval (by norm_num) hY)
  have hm : (∫ y in (2 : ℝ)..Y, (1 - Real.log y) / y ^ 2) ≤
      ∫ y in (2 : ℝ)..Y, density y := by
    apply intervalIntegral.integral_mono_on hY (lower_interval (by norm_num) hY)
      (density_interval (by norm_num) hY)
    intro y hy
    exact density_lower (by linarith [hy.1])
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (density_interval (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2))
    (density_interval (by norm_num : (1 : ℝ) ≤ 2) hY)
  change cumulative 2 + (∫ y in (2 : ℝ)..Y, density y) = cumulative Y at hadd
  rw [hFTC] at hm
  rw [cumulative_two] at hadd
  dsimp [kappa]
  linarith

private lemma cumulative_pos {Y : ℝ} (hY : 1 < Y) : 0 < cumulative Y :=
  (div_pos (Real.log_pos hY) (zero_lt_one.trans hY)).trans_le (cumulative_lower hY.le)

private lemma cumulative_lt_two {Y : ℝ} (hY : 1 ≤ Y) : cumulative Y < 2 := by
  have hpos : 0 < (Real.log Y + 2) / Y :=
    div_pos (by linarith [Real.log_nonneg hY]) (zero_lt_one.trans_le hY)
  exact (cumulative_upper hY).trans_lt (by linarith)

private lemma kappa_pos : 0 < kappa := by
  have hcpos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hclt : Real.log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at h
    exact h
  exact div_pos (mul_pos hcpos (by linarith)) (by norm_num)

def tailKernel (r y : ℝ) : ℝ :=
  ((r + Real.log y)⁻¹ ^ 2 + 2 * (r + Real.log y)⁻¹ ^ 3) / y

private lemma tailKernel_pos {r y : ℝ} (hr : 0 < r) (hy : 1 ≤ y) :
    0 < tailKernel r y := by
  have hypos : 0 < y := zero_lt_one.trans_le hy
  have hden : 0 < r + Real.log y := add_pos_of_pos_of_nonneg hr (Real.log_nonneg hy)
  unfold tailKernel
  positivity

private lemma kernel_primitive {r y : ℝ} (hr : 0 < r) (hy : 1 ≤ y) :
    HasDerivAt (fun z : ℝ => -((r + Real.log z)⁻¹ + (r + Real.log z)⁻¹ ^ 2))
      (tailKernel r y) y := by
  have hypos : 0 < y := zero_lt_one.trans_le hy
  have hden : 0 < r + Real.log y := add_pos_of_pos_of_nonneg hr (Real.log_nonneg hy)
  have hd := ((Real.hasDerivAt_log hypos.ne').const_add r).inv hden.ne'
  apply (hd.add (hd.pow 2)).neg.congr_deriv
  dsimp [tailKernel]
  field_simp
  ring

private lemma kernel_primitive_limit (r : ℝ) :
    Tendsto (fun z : ℝ => -((r + Real.log z)⁻¹ + (r + Real.log z)⁻¹ ^ 2))
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun z : ℝ => (r + Real.log z)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop r Real.tendsto_log_atTop)
  simpa using (hinv.add (hinv.pow 2)).neg

private lemma tailKernel_integrable {r a : ℝ} (hr : 0 < r) (ha : 1 ≤ a) :
    IntegrableOn (tailKernel r) (Ioi a) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun y hy => kernel_primitive hr (ha.trans hy))
    (fun y hy => (tailKernel_pos hr (ha.trans hy.le)).le) (kernel_primitive_limit r)

private lemma tailKernel_integral {r a : ℝ} (hr : 0 < r) (ha : 1 ≤ a) :
    (∫ y in Ioi a, tailKernel r y) =
      (r + Real.log a)⁻¹ + (r + Real.log a)⁻¹ ^ 2 := by
  simpa only [zero_sub, neg_neg] using integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun y hy => kernel_primitive hr (ha.trans hy))
    (fun y hy => (tailKernel_pos hr (ha.trans hy.le)).le) (kernel_primitive_limit r)

private def triangle (r : ℝ) (p : ℝ × ℝ) : ℝ :=
  {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => density p.1 * tailKernel r p.2) p

private lemma triangle_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (triangle r)
      ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioi (1 : ℝ)))) := by
  exact (density_integrable.mul_prod (tailKernel_integrable hr (by norm_num))).indicator
    (measurableSet_lt measurable_fst measurable_snd)

private lemma triangle_right {r y : ℝ} (hr : 0 < r) (hy : 1 < y) :
    (∫ z in Ioi (1 : ℝ), triangle r (y, z)) = highIntegrand r y := by
  have heq : (fun z => triangle r (y, z)) =
      (Ioi y).indicator (fun z => density y * tailKernel r z) := by
    ext z
    simp only [triangle, Set.indicator_apply, mem_ofPred_eq, mem_Ioi]
  rw [heq, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hy.le), integral_const_mul,
    tailKernel_integral hr hy.le]
  rw [highIntegrand, ActualFactorialRobinHighDerivative.highKernel_formula hr hy]
  dsimp [density]
  ring

private lemma triangle_left {r z : ℝ} (hz : 1 < z) :
    (∫ y in Ioi (1 : ℝ), triangle r (y, z)) = cumulative z * tailKernel r z := by
  have heq : (fun y => triangle r (y, z)) =
      (Iio z).indicator (fun y => density y * tailKernel r z) := by
    ext y
    simp only [triangle, Set.indicator_apply, mem_ofPred_eq, mem_Iio]
  rw [heq, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    inter_comm, Ioi_inter_Iio, integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hz.le]
  rfl

private lemma positive_representation_y {r : ℝ} (hr : 0 < r) :
    highRemainder r = ∫ y in Ioi (1 : ℝ), cumulative y * tailKernel r y := by
  have hswap := integral_integral_swap (f := fun y z => triangle r (y, z))
    (triangle_integrable hr)
  calc
    highRemainder r = ∫ y in Ioi (1 : ℝ), ∫ z in Ioi (1 : ℝ), triangle r (y, z) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact (triangle_right hr hy).symm
    _ = ∫ z in Ioi (1 : ℝ), ∫ y in Ioi (1 : ℝ), triangle r (y, z) := hswap
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z hz
      exact triangle_left hz

private lemma positive_integrable_y {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y => cumulative y * tailKernel r y) (Ioi (1 : ℝ)) := by
  apply (triangle_integrable hr).integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact triangle_left hy

private lemma positive_representation {r : ℝ} (hr : 0 < r) :
    highRemainder r = ∫ u in Ioi (0 : ℝ), cumulative (Real.exp u) *
      ((r + u)⁻¹ ^ 2 + 2 * (r + u)⁻¹ ^ 3) := by
  rw [positive_representation_y hr]
  have hc := integral_comp_exp_Ioi (fun y => cumulative y * tailKernel r y) 0
  rw [Real.exp_zero] at hc
  rw [← hc]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  simp only [smul_eq_mul, tailKernel, Real.log_exp]
  field_simp

private lemma high_strict_lower {r : ℝ} (hr : 0 < r) :
    kappa * ((r + Real.log 2)⁻¹ + (r + Real.log 2)⁻¹ ^ 2) < highRemainder r := by
  let g : ℝ → ℝ := fun y => cumulative y * tailKernel r y
  let b : ℝ → ℝ := fun y => kappa * (Ioi (2 : ℝ)).indicator (tailKernel r) y
  have hg : IntegrableOn g (Ioi (1 : ℝ)) := positive_integrable_y hr
  have hb : IntegrableOn b (Ioi (1 : ℝ)) :=
    ((tailKernel_integrable hr (by norm_num : (1 : ℝ) ≤ 1)).indicator
      measurableSet_Ioi).const_mul kappa
  have hnonneg : ∀ y ∈ Ioi (1 : ℝ), 0 ≤ g y - b y := by
    intro y hy
    by_cases h2 : 2 < y
    · have hC : kappa ≤ cumulative y := by
        have hl := cumulative_improved h2.le
        have hlog : 0 ≤ Real.log y / y :=
          div_nonneg (Real.log_nonneg hy.le) (zero_lt_one.trans hy).le
        linarith
      dsimp [g, b]
      rw [indicator_of_mem (show y ∈ Ioi (2 : ℝ) from h2)]
      exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right hC (tailKernel_pos hr hy.le).le)
    · dsimp [g, b]
      rw [indicator_of_notMem (show y ∉ Ioi (2 : ℝ) from h2), mul_zero, sub_zero]
      exact (mul_pos (cumulative_pos hy) (tailKernel_pos hr hy.le)).le
  have hsubset : Ioo (1 : ℝ) 2 ⊆ Function.support (fun y => g y - b y) ∩ Ioi 1 := by
    intro y hy
    refine ⟨?_, hy.1⟩
    change g y - b y ≠ 0
    dsimp [g, b]
    rw [indicator_of_notMem (show y ∉ Ioi (2 : ℝ) from not_lt_of_ge hy.2.le),
      mul_zero, sub_zero]
    exact (mul_pos (cumulative_pos hy.1) (tailKernel_pos hr hy.1.le)).ne'
  have hmass : 0 < volume (Function.support (fun y => g y - b y) ∩ Ioi 1) := by
    have hi : 0 < volume (Ioo (1 : ℝ) 2) := by norm_num [Real.volume_Ioo]
    exact hi.trans_le (measure_mono hsubset)
  have hp : 0 < ∫ y in Ioi (1 : ℝ), g y - b y :=
    (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioi hnonneg) (hg.sub hb)).mpr hmass
  rw [integral_sub hg hb] at hp
  have hbi : (∫ y in Ioi (1 : ℝ), b y) =
      kappa * ((r + Real.log 2)⁻¹ + (r + Real.log 2)⁻¹ ^ 2) := by
    rw [show b = fun y => kappa * (Ioi (2 : ℝ)).indicator (tailKernel r) y from rfl,
      integral_const_mul, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict_of_subset (Ioi_subset_Ioi (by norm_num : (1 : ℝ) ≤ 2)),
      tailKernel_integral hr (by norm_num)]
  rw [hbi] at hp
  rw [positive_representation_y hr]
  exact sub_pos.mp hp

private lemma high_strict_upper {r : ℝ} (hr : 0 < r) :
    highRemainder r < 2 * (r⁻¹ + r⁻¹ ^ 2) := by
  let g : ℝ → ℝ := fun y => cumulative y * tailKernel r y
  let b : ℝ → ℝ := fun y => 2 * tailKernel r y
  have hg : IntegrableOn g (Ioi (1 : ℝ)) := positive_integrable_y hr
  have hb : IntegrableOn b (Ioi (1 : ℝ)) :=
    (tailKernel_integrable hr (by norm_num : (1 : ℝ) ≤ 1)).const_mul 2
  have hpos : ∀ y ∈ Ioi (1 : ℝ), 0 < b y - g y := by
    intro y hy
    exact sub_pos.mpr (mul_lt_mul_of_pos_right (cumulative_lt_two hy.le)
      (tailKernel_pos hr hy.le))
  have hsubset : Ioo (1 : ℝ) 2 ⊆ Function.support (fun y => b y - g y) ∩ Ioi 1 :=
    fun y hy => ⟨(hpos y hy.1).ne', hy.1⟩
  have hmass : 0 < volume (Function.support (fun y => b y - g y) ∩ Ioi 1) := by
    have hi : 0 < volume (Ioo (1 : ℝ) 2) := by norm_num [Real.volume_Ioo]
    exact hi.trans_le (measure_mono hsubset)
  have hp : 0 < ∫ y in Ioi (1 : ℝ), b y - g y :=
    (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => (hpos y hy).le))
      (hb.sub hg)).mpr hmass
  rw [integral_sub hb hg] at hp
  have hbi : (∫ y in Ioi (1 : ℝ), b y) = 2 * (r⁻¹ + r⁻¹ ^ 2) := by
    rw [show b = fun y => 2 * tailKernel r y from rfl, integral_const_mul,
      tailKernel_integral hr (by norm_num)]
    simp
  rw [hbi] at hp
  rw [positive_representation_y hr]
  exact sub_pos.mp hp

/-- Signed factorial mass accumulates positively and controls the literal complete
high integral, with both strict budgets and all finite endpoints paid. -/
theorem result :
    cumulative 1 = 0 ∧
    cumulative 2 = Real.log 2 - (Real.log 2) ^ 2 / 2 ∧
    (∀ Y : ℝ, 1 ≤ Y → Real.log Y / Y ≤ cumulative Y ∧
      cumulative Y ≤ 2 - (Real.log Y + 2) / Y ∧ cumulative Y < 2) ∧
    (∀ Y : ℝ, 1 < Y → 0 < cumulative Y) ∧
    (∀ Y : ℝ, 2 ≤ Y → kappa + Real.log Y / Y ≤ cumulative Y) ∧
    0 < kappa ∧
    (∀ r : ℝ, 0 < r →
      IntegrableOn (fun y => cumulative y * tailKernel r y) (Ioi (1 : ℝ)) ∧
      highRemainder r = ∫ u in Ioi (0 : ℝ), cumulative (Real.exp u) *
        ((r + u)⁻¹ ^ 2 + 2 * (r + u)⁻¹ ^ 3) ∧
      kappa * ((r + Real.log 2)⁻¹ + (r + Real.log 2)⁻¹ ^ 2) < highRemainder r ∧
      highRemainder r < 2 * (r⁻¹ + r⁻¹ ^ 2)) := by
  refine ⟨by simp [cumulative], cumulative_two, ?_, fun _ h => cumulative_pos h,
    fun _ h => cumulative_improved h, kappa_pos, ?_⟩
  · intro Y hY
    exact ⟨cumulative_lower hY, cumulative_upper hY, cumulative_lt_two hY⟩
  · intro r hr
    exact ⟨positive_integrable_y hr, positive_representation hr,
      high_strict_lower hr, high_strict_upper hr⟩

end D5.S3.Arith.Robin.ActualFactorialCumulativePositivity

#print axioms D5.S3.Arith.Robin.ActualFactorialCumulativePositivity.result
