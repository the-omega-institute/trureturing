/- GID: D5/S3/Quantum/Matrix/FixedSumResolventKernel
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/FixedSumResolventKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.Layercake]
   utility: none
   digest: Layer cake expresses fixed-sum resolvent moments as integrals of convex quadratic-root lengths. -/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Matrix.FixedSumResolventKernel

open Set MeasureTheory
open scoped ENNReal

/-- The actual scalar shifted-resolvent product at fixed sum. -/
def resolvent (S r s : ℝ) : ℝ := r ^ 2 / (s ^ 2 + S * s + r ^ 2)

/-- The fixed-sum integrated resolvent moment; division at zero is immaterial. -/
def kernel (S : ℝ) (j : ℕ) (r : ℝ) : ℝ :=
  (∫ s in Ioi 0, resolvent S r s ^ j) / j

private lemma resolvent_nonneg {S : ℝ} (hS : 0 ≤ S) (r : ℝ) {s : ℝ}
    (hs : 0 ≤ s) : 0 ≤ resolvent S r s := by
  unfold resolvent
  positivity

private lemma resolvent_le_one {S : ℝ} (hS : 0 < S) (r : ℝ) {s : ℝ}
    (hs : 0 < s) : resolvent S r s ≤ 1 := by
  have hd : 0 < s ^ 2 + S * s + r ^ 2 := by positivity
  rw [resolvent, div_le_one hd]
  nlinarith [mul_pos hS hs]

private lemma measurable_resolvent (S r : ℝ) : Measurable (resolvent S r) := by
  unfold resolvent
  fun_prop

/-- All positive integer moments are integrable, including at zero radius. -/
theorem integrable_resolvent {S : ℝ} (hS : 0 < S) (r : ℝ) {j : ℕ}
    (hj : 1 ≤ j) : IntegrableOn (fun s => resolvent S r s ^ j) (Ioi 0) := by
  apply ((integrable_inv_one_add_sq.const_mul (r ^ 2 + 1)).integrableOn).mono'
    ((measurable_resolvent S r).pow_const j).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 < s := hs
  have hd : 0 < s ^ 2 + S * s + r ^ 2 := by positivity
  have hc : 0 < 1 + s ^ 2 := by positivity
  have h0 := resolvent_nonneg hS.le r hs0.le
  have h1 := resolvent_le_one hS r hs0
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 _)]
  calc
    resolvent S r s ^ j ≤ resolvent S r s := pow_le_self₀ h0 h1 (by omega)
    _ ≤ (r ^ 2 + 1) * (1 + s ^ 2)⁻¹ := by
      rw [resolvent, ← div_eq_mul_inv, div_le_div_iff₀ hd hc]
      nlinarith [mul_nonneg (sq_nonneg r) (sq_nonneg r),
        mul_nonneg (show 0 ≤ r ^ 2 + 1 by positivity) (mul_nonneg hS.le hs0.le)]

private def levelLength (S r t : ℝ) : ℝ :=
  (Real.sqrt (S ^ 2 + 4 * r ^ 2 * (t⁻¹ - 1)) - S) / 2

private lemma length_nonneg {S r t : ℝ} (hS : 0 ≤ S) (ht : t ∈ Ioo 0 1) :
    0 ≤ levelLength S r t := by
  have ht' : 0 ≤ t⁻¹ - 1 := by
    rw [sub_nonneg, one_le_inv₀ ht.1]
    exact ht.2.le
  have hh : S ≤ Real.sqrt (S ^ 2 + 4 * r ^ 2 * (t⁻¹ - 1)) := by
    apply (Real.le_sqrt hS (by positivity)).mpr
    nlinarith [mul_nonneg (sq_nonneg r) ht']
  exact div_nonneg (sub_nonneg.mpr hh) (by norm_num)

private lemma superlevel {S r t s : ℝ} (hS : 0 < S) (ht : t ∈ Ioo 0 1)
    (hs : 0 < s) : t < resolvent S r s ↔ s < levelLength S r t := by
  have hd : 0 < s ^ 2 + S * s + r ^ 2 := by positivity
  have ht' : 0 ≤ t⁻¹ - 1 := by
    rw [sub_nonneg, one_le_inv₀ ht.1]
    exact ht.2.le
  have hq : 0 ≤ S ^ 2 + 4 * r ^ 2 * (t⁻¹ - 1) := by positivity
  have hroot := Real.sq_sqrt hq
  have hroot0 := Real.sqrt_nonneg (S ^ 2 + 4 * r ^ 2 * (t⁻¹ - 1))
  have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.1.ne'
  rw [resolvent, lt_div_iff₀ hd]
  unfold levelLength
  constructor
  · intro h
    have hquad : s ^ 2 + S * s < r ^ 2 * (t⁻¹ - 1) := by
      apply (mul_lt_mul_iff_right₀ ht.1).mp
      nlinarith [hinv]
    have hpos : 0 ≤ 2 * s + S := by positivity
    have hlt : 2 * s + S < Real.sqrt (S ^ 2 + 4 * r ^ 2 * (t⁻¹ - 1)) := by
      nlinarith only [hquad, hroot, hroot0, hpos]
    linarith
  · intro h
    have hquad : s ^ 2 + S * s < r ^ 2 * (t⁻¹ - 1) := by
      have hp : 0 < 2 * s + S := by positivity
      nlinarith only [h, hroot, hroot0, hp]
    have hm := mul_lt_mul_of_pos_right hquad ht.1
    nlinarith [hinv]

private lemma length_convex {S t : ℝ} (hS : 0 ≤ S) (ht : t ∈ Ioo 0 1) :
    ConvexOn ℝ (Ici 0) (fun r => levelLength S r t) := by
  have hc : 0 ≤ t⁻¹ - 1 := by
    rw [sub_nonneg, one_le_inv₀ ht.1]
    exact ht.2.le
  let c := 2 * Real.sqrt (t⁻¹ - 1)
  have hc2 : c ^ 2 = 4 * (t⁻¹ - 1) := by
    dsimp [c]
    rw [mul_pow, Real.sq_sqrt hc]
    ring
  have hn (r : ℝ) : ‖(⟨S, c * r⟩ : ℂ)‖ =
      Real.sqrt (S ^ 2 + 4 * r ^ 2 * (t⁻¹ - 1)) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    congr 1
    simp only [Complex.mk_re, Complex.mk_im, mul_pow, hc2]
    ring
  refine ⟨convex_Ici 0, ?_⟩
  intro x _ y _ a b ha hb hab
  have hv : (⟨S, c * (a * x + b * y)⟩ : ℂ) =
      a • (⟨S, c * x⟩ : ℂ) + b • (⟨S, c * y⟩ : ℂ) := by
    apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im,
      Complex.real_smul_re, Complex.real_smul_im, Complex.mk_re, Complex.mk_im]
    · nlinarith only [hab]
    · ring
  have hh := norm_add_le (a • (⟨S, c * x⟩ : ℂ)) (b • (⟨S, c * y⟩ : ℂ))
  rw [← hv, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha, abs_of_nonneg hb, hn, hn, hn] at hh
  simp only [smul_eq_mul, levelLength]
  nlinarith only [hh, hab]

end D5.S3.Quantum.Matrix.FixedSumResolventKernel
