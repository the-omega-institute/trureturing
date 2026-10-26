/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfGaussianBounds
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual Gaussian weighted convergence for the same-source cap comparison. -/

/-
SPDX-License-Identifier: Apache-2.0
UNCOMPILED source, 2026-10-26. No compiler or acceptance claim.

New proofs using the root-collected GaussianAtom/Cauchy/Generating suppliers.
Their definitions and proofs are imported, not copied. The imported polynomial
supplier retains its OAI attribution and license; the imported Cauchy supplier
retains its Mathlib attribution and license. No proof body is directly ported
from either external project in this file.
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfGaussianAtom
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Ring.GeomSum

/-! Actual Gaussian weighted convergence for the same-source cap comparison. -/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace FiniteGaussianCap4.LaguerreSevenHalf

/-- The literal finite prefix of the actual Gaussian atom series. -/
def gaussianPartialSum (a : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (gaussianSiteAmplitude a * phi x n) * gaussianSiteQ a ^ n

/-- The actual atom, with the same exponent as `gaussian_atom_hasSum`. -/
def gaussianAtom (a x : ℝ) : ℝ :=
  Real.exp (9 * a / 2 - Real.exp (2 * a) * x)

theorem continuous_phi (n : ℕ) : Continuous (fun x : ℝ => phi x n) := by
  unfold phi
  exact (Real.continuous_exp.comp continuous_id.neg).mul
    ((laguerre n).continuous.comp (continuous_const.mul continuous_id))

theorem continuous_gaussianPartialSum (a : ℝ) (N : ℕ) :
    Continuous (gaussianPartialSum a N) := by
  unfold gaussianPartialSum
  exact continuous_finsetSum _ (fun n _ =>
    (continuous_const.mul (continuous_phi n)).mul continuous_const)

theorem continuous_gaussianAtom (a : ℝ) : Continuous (gaussianAtom a) := by
  unfold gaussianAtom
  exact Real.continuous_exp.comp
    (continuous_const.sub (continuous_const.mul continuous_id))

/-- Pointwise convergence is supplied by the actual atom HasSum, for all x. -/
theorem gaussianPartialSum_tendsto (a x : ℝ) :
    Tendsto (fun N => gaussianPartialSum a N x) atTop (𝓝 (gaussianAtom a x)) := by
  exact (gaussian_atom_hasSum a x).tendsto_sum_nat

theorem gaussian_error_tendsto (a x : ℝ) :
    Tendsto (fun N => gaussianPartialSum a N x - gaussianAtom a x)
      atTop (𝓝 (0 : ℝ)) := by
  have hc : Tendsto (fun _ : ℕ => gaussianAtom a x) atTop
      (𝓝 (gaussianAtom a x)) := tendsto_const_nhds
  simpa only [sub_self] using (gaussianPartialSum_tendsto a x).sub hc

private theorem geometric_prefix_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (N : ℕ) : (∑ n ∈ Finset.range N, t ^ n) ≤ 1 / (1 - t) := by
  apply (le_div_iff₀ (sub_pos.mpr ht1)).2
  rw [geom_sum_mul_neg]
  linarith [pow_nonneg ht0 N]

/-- One site and one strictly larger Cauchy radius determine a finite constant.
There is no radius claimed to work uniformly over all real sites. -/
def gaussianPrefixConstant (a r : ℝ) : ℝ :=
  (|gaussianSiteAmplitude a| * (1 - r) ^ (-9 / 2 : ℝ)) /
    (1 - |gaussianSiteQ a| / r)

theorem gaussianPrefixConstant_nonneg (a : ℝ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hqr : |gaussianSiteQ a| < r) :
    0 ≤ gaussianPrefixConstant a r := by
  have ht1 : |gaussianSiteQ a| / r < 1 := (div_lt_one hr).2 hqr
  exact div_nonneg
    (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (sub_nonneg.mpr hr1.le) _))
    (sub_nonneg.mpr ht1.le)

/-- Sum the finite geometric prefix of the actual coefficient bound. -/
theorem gaussianPartialSum_bound (a : ℝ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hqr : |gaussianSiteQ a| < r)
    (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    |gaussianPartialSum a N x| ≤
      gaussianPrefixConstant a r * Real.exp (-circleDecay r * x) := by
  let t : ℝ := |gaussianSiteQ a| / r
  let C : ℝ := (1 - r) ^ (-9 / 2 : ℝ)
  have ht0 : 0 ≤ t := div_nonneg (abs_nonneg _) hr.le
  have ht1 : t < 1 := (div_lt_one hr).2 hqr
  have hC : 0 ≤ C := Real.rpow_nonneg (sub_nonneg.mpr hr1.le) _
  have hterm (n : ℕ) :
      |(gaussianSiteAmplitude a * phi x n) * gaussianSiteQ a ^ n| ≤
        |gaussianSiteAmplitude a| *
          ((C * Real.exp (-circleDecay r * x)) * t ^ n) := by
    rw [mul_assoc, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (phi_geometric_bound x hx (gaussianSiteQ a) hr hr1 hqr n) (abs_nonneg _)
  calc
    |gaussianPartialSum a N x| ≤
        ∑ n ∈ Finset.range N,
          |(gaussianSiteAmplitude a * phi x n) * gaussianSiteQ a ^ n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N, |gaussianSiteAmplitude a| *
        ((C * Real.exp (-circleDecay r * x)) * t ^ n) :=
      Finset.sum_le_sum (fun n _ => hterm n)
    _ = (|gaussianSiteAmplitude a| * C * Real.exp (-circleDecay r * x)) *
        (∑ n ∈ Finset.range N, t ^ n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ (|gaussianSiteAmplitude a| * C * Real.exp (-circleDecay r * x)) *
        (1 / (1 - t)) := by
      exact mul_le_mul_of_nonneg_left (geometric_prefix_le ht0 ht1 N)
        (mul_nonneg (mul_nonneg (abs_nonneg _) hC) (Real.exp_pos _).le)
    _ = gaussianPrefixConstant a r * Real.exp (-circleDecay r * x) := by
      dsimp [gaussianPrefixConstant, C, t]
      ring

/-- Closedness of a scalar inequality passes the prefix bound to its actual limit. -/
theorem gaussianAtom_bound (a : ℝ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hqr : |gaussianSiteQ a| < r)
    (x : ℝ) (hx : 0 ≤ x) :
    |gaussianAtom a x| ≤
      gaussianPrefixConstant a r * Real.exp (-circleDecay r * x) := by
  exact le_of_tendsto' (gaussianPartialSum_tendsto a x).abs
    (fun N => gaussianPartialSum_bound a hr hr1 hqr N x hx)

theorem gaussian_error_bound (a : ℝ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hqr : |gaussianSiteQ a| < r)
    (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    |gaussianPartialSum a N x - gaussianAtom a x| ≤
      2 * gaussianPrefixConstant a r * Real.exp (-circleDecay r * x) := by
  calc
    |gaussianPartialSum a N x - gaussianAtom a x| ≤
        |gaussianPartialSum a N x| + |gaussianAtom a x| := by
      simpa only [Real.norm_eq_abs] using
        norm_sub_le (gaussianPartialSum a N x) (gaussianAtom a x)
    _ ≤ gaussianPrefixConstant a r * Real.exp (-circleDecay r * x) +
        gaussianPrefixConstant a r * Real.exp (-circleDecay r * x) :=
      add_le_add (gaussianPartialSum_bound a hr hr1 hqr N x hx)
        (gaussianAtom_bound a hr hr1 hqr x hx)
    _ = 2 * gaussianPrefixConstant a r * Real.exp (-circleDecay r * x) := by ring

/-- Unconditional, site-dependent domination data, used by the integral module.
The chosen positive decay rate is exactly `circleDecay r` with |q(a)|<r<1. -/
theorem gaussian_dominated_bounds (a : ℝ) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧
      (∀ N x, 0 < x → |gaussianPartialSum a N x| ≤ K * Real.exp (-c * x)) ∧
      (∀ x, 0 < x → |gaussianAtom a x| ≤ K * Real.exp (-c * x)) ∧
      (∀ N x, 0 < x → |gaussianPartialSum a N x - gaussianAtom a x| ≤
        2 * K * Real.exp (-c * x)) := by
  obtain ⟨r, hr, hqr, hr1⟩ := gaussianSiteQ_exists_radius a
  refine ⟨gaussianPrefixConstant a r, circleDecay r,
    gaussianPrefixConstant_nonneg a hr hr1 hqr, circleDecay_pos hr hr1, ?_, ?_, ?_⟩
  · intro N x hx
    exact gaussianPartialSum_bound a hr hr1 hqr N x hx.le
  · intro x hx
    exact gaussianAtom_bound a hr hr1 hqr x hx.le
  · intro N x hx
    exact gaussian_error_bound a hr hr1 hqr N x hx.le

end FiniteGaussianCap4.LaguerreSevenHalf
