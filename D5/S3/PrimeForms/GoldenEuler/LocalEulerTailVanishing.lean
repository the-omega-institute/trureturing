/- GID: D5/S3/PrimeForms/GoldenEuler/LocalEulerTailVanishing
   generality: G
   mirror-B: D5/B/S3/PrimeForms/GoldenEuler/LocalEulerTailVanishing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite local Euler factor has an explicit tail residual that
     vanishes under a strict unit-disk bound. -/
/- Library-search audit trail (2026-08-31):
   * Repository searches for the local definitions and residual theorem found
     no existing owner of this exact one-place completion package.
   * Pinned Mathlib owns `mul_neg_geom_sum` and
     `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`; both are consumed directly.
   * The theorem packages the exact residual together with the local limit, so
     later Euler work does not silently replace a finite factor by its inverse.
   * No infinite prime product, uniform majorant, limit interchange, or
     nonvanishing statement is introduced here. -/

import Mathlib

/-!
Finite Euler factors are not equal to their infinite completion. Their exact
multiplicative defect is the geometric tail `x^N`. Under `‖x‖ < 1`, that
residual tends to zero, so the normalized finite factor converges to one.

This is a one-place theorem. Passing to a product over all primes still
requires a uniform summable majorant and is not asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.PrimeForms.GoldenEuler.LocalEulerTailVanishing

open Filter Topology

/-- Geometric local Euler truncation through exponents strictly below `N`. -/
def localEulerPartial (x : ℂ) (N : ℕ) : ℂ :=
  ∑ m ∈ Finset.range N, x ^ m

/-- Exact tail omitted by the finite local Euler truncation. -/
def localEulerResidual (x : ℂ) (N : ℕ) : ℂ :=
  x ^ N

/-- Multiplying a finite local factor by `1 - x` leaves exactly the tail
residual. -/
theorem local_euler_partial_residual (x : ℂ) (N : ℕ) :
    (1 - x) * localEulerPartial x N = 1 - localEulerResidual x N := by
  simpa [localEulerPartial, localEulerResidual] using
    (mul_neg_geom_sum x N)

/-- A strict unit-disk bound forces the local Euler residual to vanish. -/
theorem local_euler_residual_tendsto_zero
    {x : ℂ} (hx : ‖x‖ < 1) :
    Tendsto (localEulerResidual x) atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => x ^ N) atTop (𝓝 0)
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx

/-- Consequently the normalized finite local Euler factor converges to one. -/
theorem normalized_local_euler_partial_tendsto_one
    {x : ℂ} (hx : ‖x‖ < 1) :
    Tendsto
      (fun N => (1 - x) * localEulerPartial x N)
      atTop (𝓝 1) := by
  have hResidual := local_euler_residual_tendsto_zero hx
  have hTranslated :
      Tendsto (fun N => 1 - localEulerResidual x N)
        atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hResidual
  simpa [local_euler_partial_residual] using hTranslated

/-- The finite local factor converges to the inverse Euler denominator. -/
theorem local_euler_partial_tendsto_inv
    {x : ℂ} (hx : ‖x‖ < 1) :
    Tendsto (localEulerPartial x) atTop
      (𝓝 ((1 - x)⁻¹)) := by
  have hOneSub : 1 - x ≠ 0 := by
    intro hZero
    have hxOne : x = 1 := (sub_eq_zero.mp hZero).symm
    rw [hxOne, norm_one] at hx
    exact lt_irrefl 1 hx
  have hNormalized := normalized_local_euler_partial_tendsto_one hx
  have hScaled := hNormalized.const_mul ((1 - x)⁻¹)
  convert hScaled using 1 <;> simp [hOneSub]

/-- The unit-disk hypothesis is inhabited. -/
example :
    Tendsto (localEulerResidual 0) atTop (𝓝 0) := by
  apply local_euler_residual_tendsto_zero
  norm_num

#print axioms local_euler_partial_residual
#print axioms local_euler_residual_tendsto_zero
#print axioms normalized_local_euler_partial_tendsto_one
#print axioms local_euler_partial_tendsto_inv

end D5.S3.PrimeForms.GoldenEuler.LocalEulerTailVanishing
