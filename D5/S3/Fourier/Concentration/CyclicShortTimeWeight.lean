/- GID: D5/S3/Fourier/Concentration/CyclicShortTimeWeight
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/CyclicShortTimeWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Short lifted frequencies incur a quadratic phase deficit for a cyclic majorant. -/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The Fourier weight in any short set of lifted modes loses a term determined by
the product of two squared-position sums. -/

open Finset Set
open scoped ZMod
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.Concentration.CyclicShortTimeWeight

private theorem phase_deficit (q : ℕ) [NeZero q] (r k : ℤ)
    (hshort : 2 * |(r : ℝ) * (k : ℝ)| ≤ (q : ℝ)) :
    8 * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 / (q : ℝ) ^ 2 ≤
      1 - (ZMod.stdAddChar (-((r : ZMod q) * (k : ZMod q)))).re := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  let u : ℝ := 2 * Real.pi * (-((r : ℝ) * (k : ℝ))) / q
  have hu : |u| ≤ Real.pi := by
    dsimp [u]
    rw [abs_div, abs_of_pos hq, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi), abs_neg]
    apply (div_le_iff₀ hq).mpr
    calc
      _ = Real.pi * (2 * |(r : ℝ) * (k : ℝ)|) := by ring
      _ ≤ Real.pi * (q : ℝ) := mul_le_mul_of_nonneg_left hshort Real.pi_pos.le
  have hchar : (ZMod.stdAddChar (-((r : ZMod q) * (k : ZMod q)))).re = Real.cos u := by
    rw [show -((r : ZMod q) * (k : ZMod q)) = ((-(r * k) : ℤ) : ZMod q) by push_cast; rfl,
      ZMod.stdAddChar_coe]
    have he : (2 * (Real.pi : ℂ) * Complex.I * ((-(r * k) : ℤ) : ℂ) / (q : ℂ)) =
        (u : ℂ) * Complex.I := by
      dsimp [u]
      push_cast
      ring
    rw [he, Complex.exp_re]
    simp [Complex.mul_re, Complex.mul_im]
  rw [hchar]
  have hcos := Real.cos_le_one_sub_mul_cos_sq hu
  have he : 2 / Real.pi ^ 2 * u ^ 2 =
      8 * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 / (q : ℝ) ^ 2 := by
    dsimp [u]
    field_simp [Real.pi_ne_zero, hq.ne']
    ring
  linarith

/-- Replacing each selected transform value by the zero-mode value has a
quadratic cost from each sampled point of the spatial majorant. Only the
spatial samples must represent distinct residues. -/
theorem low_fourier_weight_deficit (q : ℕ) [NeZero q] (F : ZMod q → ℝ)
    (hF : ∀ r, 0 ≤ F r) (a : ℝ) (R J : Finset ℤ)
    (hR : Set.InjOn (fun r : ℤ => (r : ZMod q)) (R : Set ℤ))
    (hmajor : ∀ r ∈ R, a ≤ F (r : ZMod q))
    (hshort : ∀ r ∈ R, ∀ k ∈ J, 2 * |(r : ℝ) * (k : ℝ)| ≤ (q : ℝ)) :
    let realPart : ℂ → ℝ := Complex.re
    (∑ k ∈ J, realPart (ZMod.dft (fun x => (F x : ℂ)) (k : ZMod q))) +
      (8 * a / (q : ℝ) ^ 2) * (∑ r ∈ R, (r : ℝ) ^ 2) * (∑ k ∈ J, (k : ℝ) ^ 2) ≤
        (J.card : ℝ) * ∑ x, F x := by
  classical
  let d (k : ℤ) (x : ZMod q) := F x * (1 - (ZMod.stdAddChar (-(x * (k : ZMod q)))).re)
  have hnonneg (k : ℤ) (x : ZMod q) : 0 ≤ d k x :=
    mul_nonneg (hF x)
      (sub_nonneg.mpr ((Complex.re_le_norm _).trans_eq ((ZMod.stdAddChar (N := q)).norm_apply _)))
  have hidentity (k : ℤ) :
      (ZMod.dft (fun x => (F x : ℂ)) (k : ZMod q)).re + ∑ x, d k x = ∑ x, F x := by
    rw [ZMod.dft_apply, Complex.re_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro x _
    simp only [smul_eq_mul, d, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    ring
  have hsample (k : ℤ) (hk : k ∈ J) :
      (8 * a / (q : ℝ) ^ 2) * (∑ r ∈ R, (r : ℝ) ^ 2) * (k : ℝ) ^ 2 ≤ ∑ x, d k x := by
    calc
      _ = ∑ r ∈ R, a * (8 * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 / (q : ℝ) ^ 2) := by
        rw [mul_sum, Finset.sum_mul]
        apply sum_congr rfl
        intro r _
        ring
      _ ≤ ∑ r ∈ R, d k (r : ZMod q) := by
        refine sum_le_sum fun r hr => ?_
        have hgap := phase_deficit q r k (hshort r hr k hk)
        exact mul_le_mul (hmajor r hr) hgap (by positivity) (hF _)
      _ = ∑ x ∈ R.image (fun r : ℤ => (r : ZMod q)), d k x :=
        (Finset.sum_image (fun _ hx _ hy he => hR hx hy he)).symm
      _ ≤ ∑ x, d k x :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => hnonneg k x)
  dsimp only
  rw [mul_sum, ← sum_add_distrib, ← nsmul_eq_mul, ← sum_const]
  exact sum_le_sum fun k hk =>
    (add_le_add le_rfl (hsample k hk)).trans_eq (hidentity k)

end D5.S3.Fourier.Concentration.CyclicShortTimeWeight
