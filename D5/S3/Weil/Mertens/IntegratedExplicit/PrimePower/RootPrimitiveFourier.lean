/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootPrimitiveFourier
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common coefficient bound and exponential normalization of actual root primitives. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootSpectrum
import D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean (frequency)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

/-- The integrated mode gains at most one factor of the root degree from its primitive. -/
theorem root_primitive_coefficient_norm_le {r : ℝ} (hr : 1 < r) (k : ℕ) :
    ‖rootCoeff r k / rootExponent r k‖ ≤ (r * ‖actualCoeff k‖) * r := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  rw [norm_div]
  calc
    _ ≤ ‖rootCoeff r k‖ / r⁻¹ :=
      div_le_div_of_nonneg_left (norm_nonneg _) (inv_pos.mpr hr0) (rootExponent_norm hr k)
    _ ≤ _ := by rw [div_inv_eq_mul]; gcongr; exact rootCoeff_bound hr k

/-- Removing the common real decay rate expresses the primitive as a centered zero series. -/
theorem normalized_root_primitive_series {r : ℝ} (hr : 1 < r) (u : ℝ) :
    let s : ℝ := 1/2-(2*r)⁻¹
    Real.exp (s*u)*rootPrimitive r (Real.exp u) =
      (∑' k, (rootCoeff r k / rootExponent r k) *
        Complex.exp ((frequency k/(r : ℂ))*(u : ℂ))).re := by
  let s : ℝ := 1/2-(2*r)⁻¹
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hshift (k : ℕ) : rootExponent r k + (s : ℂ) = frequency k/(r : ℂ) := by
    simp only [rootExponent, frequency, s]
    push_cast
    field_simp
    ring
  change Real.exp (s*u)*rootPrimitive r (Real.exp u) = _
  unfold rootPrimitive
  rw [← Complex.re_ofReal_mul, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro k
  rw [← rootPrimitiveMode_eq hr]
  change (Real.exp (s*u) : ℂ) *
    (rootCoeff r k * Complex.exp (rootExponent r k * (u : ℂ))/rootExponent r k) = _
  rw [Complex.ofReal_exp]
  push_cast
  rw [show Complex.exp ((s : ℂ)*(u : ℂ)) *
      (rootCoeff r k * Complex.exp (rootExponent r k * (u : ℂ))/rootExponent r k) =
      (rootCoeff r k / rootExponent r k) * (Complex.exp (rootExponent r k * (u : ℂ)) *
        Complex.exp ((s : ℂ)*(u : ℂ))) by ring,
    ← Complex.exp_add, ← add_mul, hshift]

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
