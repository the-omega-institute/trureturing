/- GID: D5/S3/Entropy/ProductAbsorptionLogIntegral
   generality: G
   mirror-B: D5/B/S3/Entropy/ProductAbsorptionLogIntegral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute integrability and exact first moment of the product absorption logarithmic kernel. -/

import D5.S3.Entropy.ProductAbsorptionLogKernel
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
namespace D5.S3.Entropy.ProductAbsorptionLogIntegral
open Set Filter MeasureTheory
open scoped Topology
open D5.S3.Entropy.ProductAbsorptionLogKernel

/-- The exact logarithmic first moment; multiplication by zero uses the total
real logarithm, so every zero-root boundary is included. -/
def productLogMoment (u v : ℝ) : ℝ :=
  let A := u + v
  let B := u * v
  let L := A - B
  let q := Real.sqrt (B * (1 - A + B))
  let mp := A - 2 * B + 2 * q
  let mm := A - 2 * B - 2 * q
  2 * L * Real.log L - u * Real.log u - v * Real.log v -
    (mp * Real.log mp + mm * Real.log mm) / 2

private def primitive (x s : ℝ) : ℝ :=
  (s + x) * Real.log (s + x) - s * Real.log s

private lemma primitive_continuous (x : ℝ) : Continuous (primitive x) := by
  exact (Real.continuous_mul_log.comp (continuous_id.add_const x)).sub
    Real.continuous_mul_log

private lemma primitive_hasDerivAt {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) :
    HasDerivAt (primitive x) (Real.log (1 + x / s)) s := by
  have hsp : 0 < s + x := by linarith
  have hlog : Real.log (1 + x / s) = Real.log (s + x) - Real.log s := by
    rw [show 1 + x / s = (s + x) / s by field_simp [hs.ne']; ring]
    exact Real.log_div hsp.ne' hs.ne'
  have h := ((Real.hasDerivAt_mul_log hsp.ne').comp s
    ((hasDerivAt_id s).add_const x)).sub (Real.hasDerivAt_mul_log hs.ne')
  convert h using 1 <;> simp only [hlog, mul_one] <;> ring

private lemma primitive_shift {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) :
    primitive x s - x * Real.log s =
      (s + x) * Real.log (1 + x / s) := by
  have hsp : 0 < s + x := by linarith
  rw [show 1 + x / s = (s + x) / s by field_simp [hs.ne']; ring,
    Real.log_div hsp.ne' hs.ne']
  dsimp [primitive]
  ring

private lemma primitive_shift_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun s : ℝ => primitive x s - x * Real.log s) atTop (𝓝 x) := by
  have hb : ∀ s : ℝ, 0 < s →
      0 ≤ (s + x) * Real.log (1 + x / s) - x ∧
      (s + x) * Real.log (1 + x / s) - x ≤ x ^ 2 / s := by
    intro s hs
    have hsp : 0 < s + x := by linarith
    have hpos : 0 < 1 + x / s := by positivity
    have hlo := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hpos) hsp.le
    have hhi := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hpos) hsp.le
    have helo : (s + x) * (1 - (1 + x / s)⁻¹) = x := by
      rw [show 1 + x / s = (s + x) / s by field_simp [hs.ne']; ring]
      field_simp [hs.ne', hsp.ne']
      <;> ring
    have hehi : (s + x) * ((1 + x / s) - 1) = x + x ^ 2 / s := by
      field_simp [hs.ne']
      <;> ring
    rw [helo] at hlo
    rw [hehi] at hhi
    constructor <;> linarith
  have hzero : Tendsto (fun s : ℝ => (s + x) * Real.log (1 + x / s) - x)
      atTop (𝓝 0) := by
    apply squeeze_zero'
      ((eventually_gt_atTop (0 : ℝ)).mono fun s hs => (hb s hs).1)
      ((eventually_gt_atTop (0 : ℝ)).mono fun s hs => (hb s hs).2)
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun s : ℝ => x ^ 2 * s⁻¹) atTop (𝓝 (x ^ 2 * 0)))
  have htail : Tendsto (fun s : ℝ => (s + x) * Real.log (1 + x / s))
      atTop (𝓝 x) := by
    convert hzero.add_const x using 1 <;> simp
  apply htail.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  exact (primitive_shift hx hs).symm

private lemma root_data {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    let A := u + v
    let B := u * v
    let q := Real.sqrt (B * (1 - A + B))
    0 ≤ A - B ∧ 0 ≤ A - 2 * B + 2 * q ∧ 0 ≤ A - 2 * B - 2 * q := by
  dsimp only
  let A := u + v
  let B := u * v
  let q := Real.sqrt (B * (1 - A + B))
  have hB : 0 ≤ B := mul_nonneg hu.1 hv.1
  have hAB : 0 ≤ A - 2 * B := by
    have h1 := mul_nonneg hu.1 (sub_nonneg.mpr hv.2)
    have h2 := mul_nonneg hv.1 (sub_nonneg.mpr hu.2)
    dsimp [A, B]
    nlinarith
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = B * (1 - A + B) := by
    apply Real.sq_sqrt
    apply mul_nonneg hB
    have hh := mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hv.2)
    dsimp [A, B]
    nlinarith
  have hd : (A - 2 * B) ^ 2 - 4 * q ^ 2 = (u - v) ^ 2 := by
    rw [hq2]
    dsimp [A, B]
    ring
  change 0 ≤ A - B ∧ 0 ≤ A - 2 * B + 2 * q ∧ 0 ≤ A - 2 * B - 2 * q
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith [sq_nonneg (u - v)]

private def momentPrimitive (u v s : ℝ) : ℝ :=
  let A := u + v
  let B := u * v
  let L := A - B
  let q := Real.sqrt (B * (1 - A + B))
  primitive u s + primitive v s - 2 * primitive L s +
    (primitive (A - 2 * B + 2 * q) s + primitive (A - 2 * B - 2 * q) s) / 2

private lemma moment_continuous (u v : ℝ) : Continuous (momentPrimitive u v) := by
  dsimp only [momentPrimitive]
  exact (((primitive_continuous u).add (primitive_continuous v)).sub
    ((primitive_continuous _).const_mul 2)).add
    (((primitive_continuous _).add (primitive_continuous _)).div_const 2)

private lemma moment_hasDerivAt {u v s : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (hs : 0 < s) :
    HasDerivAt (momentPrimitive u v) (productLogKernel u v s) s := by
  obtain ⟨hL, hp, hm⟩ := root_data hu hv
  have h := (((primitive_hasDerivAt hu.1 hs).add (primitive_hasDerivAt hv.1 hs)).sub
    ((primitive_hasDerivAt hL hs).const_mul 2)).add
    (((primitive_hasDerivAt hp hs).add (primitive_hasDerivAt hm hs)).div_const 2)
  exact h

private lemma moment_tendsto {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) : Tendsto (momentPrimitive u v) atTop (𝓝 0) := by
  obtain ⟨hL, hp, hm⟩ := root_data hu hv
  have h := (((primitive_shift_tendsto hu.1).add (primitive_shift_tendsto hv.1)).sub
    ((primitive_shift_tendsto hL).const_mul 2)).add
    (((primitive_shift_tendsto hp).add (primitive_shift_tendsto hm)).div_const 2)
  convert h using 1
  · funext s
    dsimp [momentPrimitive]
    ring
  · congr 1
    ring

private lemma moment_zero (u v : ℝ) : momentPrimitive u v 0 = -productLogMoment u v := by
  simp only [momentPrimitive, primitive, productLogMoment, zero_add, zero_mul, sub_zero]
  ring

/-- The five-term kernel is absolutely integrable on the positive half-line, and
its integral is exactly the logarithmic first moment, including all closed-square
parameter boundaries. This statement does not assert that the moment is nonnegative. -/
theorem product_log_kernel_integrable_integral {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    IntegrableOn (productLogKernel u v) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), productLogKernel u v s) = productLogMoment u v := by
  have hc := moment_continuous u v
  have hd := fun s (hs : s ∈ Ioi (0 : ℝ)) => moment_hasDerivAt hu hv hs
  have ht := moment_tendsto hu hv
  have hi : IntegrableOn (productLogKernel u v) (Ioi 0) := by
    rcases product_log_kernel_single_crossing hu hv with h | ⟨r, hr, _, hp, hn⟩
    · exact integrableOn_Ioi_deriv_of_nonneg hc.continuousAt.continuousWithinAt hd h ht
    · have hleft : IntegrableOn (productLogKernel u v) (Ioc 0 r) :=
        intervalIntegral.integrableOn_deriv_of_nonneg hc.continuousOn
          (fun s hs => moment_hasDerivAt hu hv hs.1) (fun s hs => (hp s hs).le)
      have hright : IntegrableOn (productLogKernel u v) (Ioi r) :=
        integrableOn_Ioi_deriv_of_nonpos hc.continuousAt.continuousWithinAt
          (fun s hs => moment_hasDerivAt hu hv (hr.trans hs)) (fun s hs => (hn s hs).le) ht
      simpa only [Ioc_union_Ioi_eq_Ioi hr.le] using hleft.union hright
  refine ⟨hi, ?_⟩
  have he := integral_Ioi_of_hasDerivAt_of_tendsto hc.continuousAt.continuousWithinAt hd hi ht
  simpa only [moment_zero, zero_sub, neg_neg] using he

#print axioms product_log_kernel_integrable_integral
end D5.S3.Entropy.ProductAbsorptionLogIntegral
