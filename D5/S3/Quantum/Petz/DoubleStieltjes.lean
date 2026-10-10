/- GID: D5/S3/Quantum/Petz/DoubleStieltjes
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive symmetric double Stieltjes kernels and their finite positive-mixture resolvent marginals. -/

import D5.S3.Quantum.Petz.StieltjesDensity
import D5.S3.Quantum.PositiveResolvent.EulerResolvent
import D5.S3.Quantum.PositiveResolvent.ExponentialSecondDifference
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

namespace D5.S3.Quantum.Petz.DoubleStieltjes

open Set MeasureTheory
open scoped Topology
open D5.S3.Quantum.PositiveResolvent.EulerResolvent

/-- The open two-dimensional simplex; its boundary has no role in the density. -/
def triangle : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}

lemma triangle_isOpen : IsOpen triangle := by
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))

lemma triangle_subset : triangle ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  rintro p ⟨ha, hb, hab⟩
  exact ⟨⟨ha.le, by linarith⟩, ⟨hb.le, by linarith⟩⟩

/-- The parameter integrand of the symmetric positive kernel `A`. -/
private noncomputable def aIntegrand (z s t : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.sin (Real.pi * p.1) * Real.sin (Real.pi * p.2) *
    Real.exp (-p.1 * Real.log s - p.2 * Real.log t + (p.1 + p.2 - 1) * Real.log z)

/-- Source formula (8)'s density kernel, with ordinary product Lebesgue measure. -/
noncomputable def A (z s t : ℝ) : ℝ :=
  (1 / Real.pi ^ 2) * ∫ p in triangle, aIntegrand z s t p ∂(volume.prod volume)

private lemma aIntegrand_continuous (z s t : ℝ) : Continuous (aIntegrand z s t) := by
  unfold aIntegrand
  fun_prop

/-- The finite parameter integral defining `A` is absolutely integrable. -/
private theorem aIntegrand_integrable (z s t : ℝ) :
    IntegrableOn (aIntegrand z s t) triangle (volume.prod volume) := by
  exact ((aIntegrand_continuous z s t).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set triangle_subset

private lemma aIntegrand_pos (z s t : ℝ) {p : ℝ × ℝ} (hp : p ∈ triangle) :
    0 < aIntegrand z s t p := by
  rcases hp with ⟨ha, hb, hab⟩
  have ha1 : p.1 < 1 := by linarith
  have hb1 : p.2 < 1 := by linarith
  have hsina : 0 < Real.sin (Real.pi * p.1) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ha) (by simpa only [mul_one] using mul_lt_mul_of_pos_left ha1 Real.pi_pos)
  have hsinb : 0 < Real.sin (Real.pi * p.2) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hb) (by simpa only [mul_one] using mul_lt_mul_of_pos_left hb1 Real.pi_pos)
  exact mul_pos (mul_pos hsina hsinb) (Real.exp_pos _)

/-- Strict positivity holds also when the two resolvent parameters coincide. -/
theorem A_pos (z s t : ℝ) : 0 < A z s t := by
  have hnonneg : ∀ᵐ p ∂(volume.prod volume).restrict triangle, 0 ≤ aIntegrand z s t p := by
    filter_upwards [ae_restrict_mem triangle_isOpen.measurableSet] with p hp
    exact (aIntegrand_pos z s t hp).le
  have hsupp : triangle ⊆ Function.support (aIntegrand z s t) := by
    intro p hp
    exact (aIntegrand_pos z s t hp).ne'
  have htriangle : 0 < (volume.prod volume) triangle :=
    triangle_isOpen.measure_pos (volume.prod volume) ⟨(1 / 4, 1 / 4), by norm_num [triangle]⟩
  have hsupport : 0 < (volume.prod volume).restrict triangle
      (Function.support (aIntegrand z s t)) := by
    rw [Measure.restrict_apply (aIntegrand_continuous z s t).stronglyMeasurable.measurableSet_support]
    simpa only [inter_eq_right.mpr hsupp] using htriangle
  exact mul_pos (by positivity)
    ((integral_pos_iff_support_of_nonneg_ae hnonneg (aIntegrand_integrable z s t)).2 hsupport)

/-- Global measurability needed for Tonelli on the two resolvent variables. -/
theorem A_measurable (z : ℝ) : Measurable (fun p : ℝ × ℝ => A z p.1 p.2) := by
  have hf : StronglyMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      aIntegrand z q.1.1 q.1.2 q.2) := by
    apply Measurable.stronglyMeasurable
    unfold aIntegrand
    fun_prop
  exact measurable_const.mul (hf.integral_prod_right'
    (ν := (volume.prod volume).restrict triangle)).measurable

/-- Exchanging the two resolvent variables preserves `A`. -/
theorem A_symm (z s t : ℝ) : A z s t = A z t s := by
  have heq (p : ℝ × ℝ) :
      triangle.indicator (aIntegrand z s t) p.swap =
        triangle.indicator (aIntegrand z t s) p := by
    have hswap : p.swap ∈ triangle ↔ p ∈ triangle := by
      simp only [triangle, mem_setOf_eq, Prod.fst_swap, Prod.snd_swap]
      constructor <;> rintro ⟨ha, hb, hab⟩ <;> exact ⟨hb, ha, by linarith⟩
    by_cases hp : p ∈ triangle
    · simp only [indicator_of_mem hp, indicator_of_mem (hswap.mpr hp)]
      dsimp [aIntegrand]
      congr 1
      · ring
      · congr 1
        ring
    · simp only [indicator_of_notMem hp, indicator_of_notMem (mt hswap.mp hp)]
  unfold A
  congr 1
  rw [← integral_indicator triangle_isOpen.measurableSet,
    ← integral_indicator triangle_isOpen.measurableSet,
    ← integral_prod_swap (triangle.indicator (aIntegrand z s t))]
  exact integral_congr_ae (Filter.Eventually.of_forall heq)

noncomputable def aMarginalIntegrand (z s y : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.sin (Real.pi * p.1) *
    Real.exp (-p.1 * Real.log s - p.2 * Real.log y + (p.1 + p.2 - 1) * Real.log z)

private lemma aRow_integral (z s : ℝ) {y : ℝ} (hy : 0 < y)
    {p : ℝ × ℝ} (hp : p ∈ triangle) :
    IntegrableOn (fun t => aIntegrand z s t p / (y + t)) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), aIntegrand z s t p / (y + t)) =
        Real.pi * aMarginalIntegrand z s y p := by
  have hb0 : 0 < p.2 := hp.2.1
  have hb1 : p.2 < 1 := by have := hp.1; have := hp.2.2; linarith
  let c := Real.pi * Real.sin (Real.pi * p.1) *
    Real.exp (-p.1 * Real.log s + (p.1 + p.2 - 1) * Real.log z)
  have heq (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      aIntegrand z s t p / (y + t) =
        c * (Real.sin (Real.pi * p.2) / Real.pi * (t ^ (-p.2) / (y + t))) := by
    unfold aIntegrand
    rw [Real.rpow_def_of_pos ht]
    have hexp : -p.1 * Real.log s - p.2 * Real.log t +
        (p.1 + p.2 - 1) * Real.log z =
        (-p.1 * Real.log s + (p.1 + p.2 - 1) * Real.log z) + Real.log t * (-p.2) := by ring
    rw [hexp, Real.exp_add]
    dsimp [c]
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hi := ((euler_resolvent_integrable p.2 y hb0 hb1 hy).const_mul
    (Real.sin (Real.pi * p.2) / Real.pi)).const_mul c
  constructor
  · exact IntegrableOn.congr_fun hi (fun t ht => (heq t ht).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
      integral_const_mul, ← euler_resolvent p.2 y hb0 hb1 hy,
      Real.rpow_def_of_pos hy]
    unfold aMarginalIntegrand
    have hexp : -p.1 * Real.log s - p.2 * Real.log y +
        (p.1 + p.2 - 1) * Real.log z =
        (-p.1 * Real.log s + (p.1 + p.2 - 1) * Real.log z) + Real.log y * (-p.2) := by ring
    rw [hexp, Real.exp_add]
    dsimp [c]
    ring

/-- Formula (9)'s first equality, with its absolute convergence justified by positive rows. -/
theorem A_marginal (z s : ℝ) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun t => A z s t / (y + t)) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), A z s t / (y + t)) =
        (1 / Real.pi) * ∫ p in triangle, aMarginalIntegrand z s y p ∂(volume.prod volume) := by
  let μ := (volume.prod volume).restrict triangle
  let ν := volume.restrict (Ioi (0 : ℝ))
  let f : (ℝ × ℝ) × ℝ → ℝ := fun q => aIntegrand z s q.2 q.1 / (y + q.2)
  have hf : Measurable f := by unfold f aIntegrand; fun_prop
  have hgcont : Continuous (aMarginalIntegrand z s y) := by unfold aMarginalIntegrand; fun_prop
  have hg : Integrable (fun p => Real.pi * aMarginalIntegrand z s y p) μ :=
    (((hgcont.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set triangle_subset).const_mul Real.pi)
  have hfin : Integrable f (μ.prod ν) := by
    apply (integrable_prod_iff hf.aestronglyMeasurable).2
    constructor
    · filter_upwards [ae_restrict_mem triangle_isOpen.measurableSet] with p hp
      exact (aRow_integral z s hy hp).1
    · apply hg.congr
      filter_upwards [ae_restrict_mem triangle_isOpen.measurableSet] with p hp
      have he : (∫ t, ‖f (p,t)‖ ∂ν) = ∫ t, f (p,t) ∂ν := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        change 0 < t at ht
        change ‖aIntegrand z s t p / (y+t)‖ = aIntegrand z s t p / (y+t)
        exact Real.norm_of_nonneg (div_nonneg (aIntegrand_pos z s t hp).le (add_pos hy ht).le)
      rw [he]
      exact (aRow_integral z s hy hp).2.symm
  have heq (t : ℝ) : A z s t / (y + t) = (1 / Real.pi ^ 2) * ∫ p, f (p,t) ∂μ := by
    dsimp [A, f, μ]
    rw [integral_div]
    ring
  have hswap := integral_integral_swap (f := fun p t => f (p,t)) (μ := μ) (ν := ν) hfin
  constructor
  · exact (hfin.integral_prod_right.const_mul (1 / Real.pi ^ 2)).congr
      (Filter.Eventually.of_forall fun t => (heq t).symm)
  · rw [integral_congr_ae (Filter.Eventually.of_forall heq), integral_const_mul, ← hswap]
    have hrow : (∫ p, ∫ t, f (p,t) ∂ν ∂μ) =
        ∫ p, Real.pi * aMarginalIntegrand z s y p ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem triangle_isOpen.measurableSet] with p hp
      exact (aRow_integral z s hy hp).2
    rw [hrow, integral_const_mul]
    dsimp [μ]
    field_simp [Real.pi_ne_zero]
    <;> ring

/-- Symmetric positive two-variable density in source formula (12). -/
noncomputable def B (z s t : ℝ) : ℝ := k s t / ((s + z) * (t + z))

/-- Positivity on the resolvent half-lines. -/
theorem B_pos {z s t : ℝ} (hz : 0 < z) (hs : 0 < s) (ht : 0 < t) :
    0 < B z s t := by
  exact div_pos (k_pos s t hs ht) (mul_pos (add_pos hs hz) (add_pos ht hz))

/-- Symmetry on the two resolvent variables. -/
theorem B_symm (z s t : ℝ) : B z s t = B z t s := by
  unfold B
  rw [k_symm s t, mul_comm (s + z) (t + z)]

private noncomputable def pRow (s y z θ t : ℝ) : ℝ :=
  Real.sin (Real.pi * θ) ^ 2 * s ^ (1 - θ) * t ^ θ / ((y + t) * (z + t))

private noncomputable def pRowValue (s y z θ : ℝ) : ℝ :=
  Real.pi * Real.sin (Real.pi * θ) * s ^ (1 - θ) *
    ((y ^ θ - z ^ θ) / (y - z))

private lemma pRow_integral {s y z θ : ℝ} (hs : 0 < s) (hy : 0 < y)
    (hz : 0 < z) (hyz : y ≠ z) (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (pRow s y z θ) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), pRow s y z θ t) = pRowValue s y z θ := by
  have hid : pRow s y z θ = fun t =>
      (Real.pi * Real.sin (Real.pi * θ) * s ^ (1 - θ)) *
        (Real.sin (Real.pi * θ) / Real.pi * (t ^ θ / ((y+t)*(z+t)))) := by
    funext t
    unfold pRow
    field_simp [Real.pi_ne_zero]
    <;> ring
  rw [hid]
  constructor
  · exact ((power_divdiff_integrable θ y z hθ.1 hθ.2 hy hz).const_mul
      (Real.sin (Real.pi * θ) / Real.pi)).const_mul _
  · rw [integral_const_mul, integral_const_mul,
      ← power_divdiff_resolvent θ y z hθ.1 hθ.2 hy hz hyz]
    rfl

/-- The divided difference of `H` is the positive `k` resolvent transform. -/
theorem H_divdiff_integral {s y z : ℝ} (hs : 0 < s) (hy : 0 < y)
    (hz : 0 < z) (hyz : y ≠ z) :
    IntegrableOn (fun t => k s t / ((y+t)*(z+t))) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), k s t / ((y+t)*(z+t))) =
        (H s y - H s z) / (y-z) := by
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  let ν := volume.restrict (Ioi (0 : ℝ))
  let f : ℝ × ℝ → ℝ := fun q => pRow s y z q.1 q.2
  have hf : Measurable f := by unfold f pRow; fun_prop
  have hgcont : Continuous (pRowValue s y z) := by
    unfold pRowValue
    fun_prop (disch := positivity)
  have hg : Integrable (pRowValue s y z) μ :=
    hgcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hfin : Integrable f (μ.prod ν) := by
    apply (integrable_prod_iff hf.aestronglyMeasurable).2
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact (pRow_integral hs hy hz hyz hθ).1
    · apply hg.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have he : (∫ t, ‖f (θ,t)‖ ∂ν) = ∫ t, f (θ,t) ∂ν := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        change 0 < t at ht
        exact Real.norm_of_nonneg (by dsimp [f, pRow]; positivity)
      rw [he]
      exact (pRow_integral hs hy hz hyz hθ).2.symm
  have heq (t : ℝ) : k s t / ((y+t)*(z+t)) =
      (1 / Real.pi ^ 2) * ∫ θ, f (θ,t) ∂μ := by
    dsimp [k, f, pRow, μ]
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo, integral_div]
    ring
  constructor
  · exact (hfin.integral_prod_right.const_mul (1 / Real.pi ^ 2)).congr
      (Filter.Eventually.of_forall fun t => (heq t).symm)
  · rw [integral_congr_ae (Filter.Eventually.of_forall heq), integral_const_mul,
      ← integral_integral_swap (f := fun θ t => f (θ,t)) (μ := μ) (ν := ν) hfin]
    have hrow : (∫ θ, ∫ t, f (θ,t) ∂ν ∂μ) = ∫ θ, pRowValue s y z θ ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact (pRow_integral hs hy hz hyz hθ).2
    rw [hrow, H_eq_integral s y hs hy, H_eq_integral s z hs hz]
    have he (u : ℝ) (hu : 0 < u) : IntervalIntegrable
        (fun θ => Real.sin (Real.pi * θ) * s ^ (1-θ) * u ^ θ) volume 0 1 :=
      (by fun_prop (disch := positivity) : Continuous _).intervalIntegrable 0 1
    rw [← mul_sub, ← intervalIntegral.integral_sub (he y hy) (he z hz)]
    dsimp [pRowValue, μ]
    rw [← integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_div, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro θ hθ
    field_simp [Real.pi_ne_zero]
    <;> ring

/-- Source formula (11)'s continuous-integral part at distinct density nodes. -/
theorem B_marginal {s y z : ℝ} (hs : 0 < s) (hy : 0 < y)
    (hz : 0 < z) (hyz : y ≠ z) :
    IntegrableOn (fun t => B z s t / (y+t)) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), B z s t / (y+t)) =
        (H s y - H s z) / ((s+z)*(y-z)) := by
  have h := H_divdiff_integral hs hy hz hyz
  have heq (t : ℝ) : B z s t / (y+t) =
      (k s t / ((y+t)*(z+t))) / (s+z) := by
    unfold B
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  constructor
  · exact (h.1.div_const (s+z)).congr (Filter.Eventually.of_forall fun t => (heq t).symm)
  · rw [integral_congr_ae (Filter.Eventually.of_forall heq), integral_div, h.2]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- Global measurability of the two-variable kernel in source (12). -/
theorem B_measurable (z : ℝ) : Measurable (fun p : ℝ × ℝ => B z p.1 p.2) := by
  have hf : StronglyMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      Real.sin (Real.pi * q.2) ^ 2 * q.1.1 ^ (1-q.2) * q.1.2 ^ q.2) := by
    apply Measurable.stronglyMeasurable
    fun_prop
  have hk : Measurable (fun p : ℝ × ℝ => k p.1 p.2) := by
    simp only [k, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact measurable_const.mul (hf.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable
  exact hk.div (by fun_prop)

private lemma rP_rewrite {s y z : ℝ} (hs : 0 < s) (hy : 0 < y)
    (hz : 0 < z) (hyz : y ≠ z) :
    StieltjesDensity.rP y z s = E s z / (y+s) +
      (H s y - H s z) / ((s+z)*(y-z)) := by
  have hlog (u : ℝ) (hu : 0 < u) :
      Real.log (s/u) ^ 2 = Real.log (u/s) ^ 2 := by
    rw [Real.log_div hs.ne' hu.ne', Real.log_div hu.ne' hs.ne']
    ring
  unfold StieltjesDensity.rP H E
  rw [← hlog y hy, ← hlog z hz]
  have hDy : Real.log (s/y) ^ 2 + Real.pi ^ 2 ≠ 0 := by positivity
  have hDz : Real.log (s/z) ^ 2 + Real.pi ^ 2 ≠ 0 := by positivity
  field_simp [hDy, hDz, (add_pos hs hy).ne', (add_pos hy hs).ne',
    (add_pos hs hz).ne', sub_ne_zero.mpr hyz]
  <;> ring

/-- Formula (11), identifying its positive integral with the existing off-diagonal density. -/
theorem rP_marginal {s y z : ℝ} (hs : 0 < s) (hy : 0 < y)
    (hz : 0 < z) (hyz : y ≠ z) :
    IntegrableOn (fun t => B z s t / (y+t)) (Ioi 0) ∧
      StieltjesDensity.rP y z s = E s z / (y+s) +
        ∫ t in Ioi (0 : ℝ), B z s t / (y+t) := by
  have h := B_marginal hs hy hz hyz
  exact ⟨h.1, by rw [h.2]; exact rP_rewrite hs hy hz hyz⟩

end D5.S3.Quantum.Petz.DoubleStieltjes
