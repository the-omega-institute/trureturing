/- GID: D5/S3/Analytic/EulerTails/PrimeDepthSummabilityWindow
   generality: G
   mirror-B: D5/B/S3/Analytic/EulerTails/PrimeDepthSummabilityWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime tail weights at extraction depth N are summable exactly on the half-plane N sigma greater than one. -/

import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib

/-!
Library-first audit:
* Mathlib's `Nat.Primes.summable_rpow` is the canonical exact convergence
  criterion for real prime-power weights and is used directly.
* Repository search found many specialized Euler-germ tail estimates but no
  generic owner exposing the extraction-depth threshold `N * sigma > 1`.

This module controls the scalar prime majorant only. It does not establish an
Euler-product identity, logarithmic weighting, local uniform convergence in a
complex variable, or analytic continuation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.EulerTails.PrimeDepthSummabilityWindow

/-- Prime weight remaining after `depth` multiplicative orders at real part
`sigma`. -/
def primeDepthWeight (depth : ℕ) (sigma : ℝ)
    (prime : Nat.Primes) : ℝ :=
  (prime.1 : ℝ) ^ (-((depth : ℝ) * sigma))

/-- Exact convergence threshold for the depth-weighted prime majorant. -/
theorem prime_depth_weight_summable_iff
    (depth : ℕ) (sigma : ℝ) :
    Summable (primeDepthWeight depth sigma) ↔
      1 < (depth : ℝ) * sigma := by
  unfold primeDepthWeight
  rw [Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

/-- Every point strictly inside the depth window gives a summable prime
majorant. -/
theorem prime_depth_weight_summable
    {depth : ℕ} {sigma : ℝ}
    (hWindow : 1 < (depth : ℝ) * sigma) :
    Summable (primeDepthWeight depth sigma) :=
  (prime_depth_weight_summable_iff depth sigma).2 hWindow

/-- On or below the boundary `depth * sigma = 1`, the prime majorant is not
summable. -/
theorem prime_depth_weight_not_summable
    {depth : ℕ} {sigma : ℝ}
    (hOutside : (depth : ℝ) * sigma ≤ 1) :
    ¬Summable (primeDepthWeight depth sigma) := by
  rw [prime_depth_weight_summable_iff]
  linarith

/-- Increasing extraction depth preserves the summability window when the real
part is positive. -/
theorem summability_window_mono_depth
    {shallow deep : ℕ} {sigma : ℝ}
    (hDepth : shallow ≤ deep) (hSigma : 0 < sigma)
    (hWindow : 1 < (shallow : ℝ) * sigma) :
    1 < (deep : ℝ) * sigma := by
  have hCast : (shallow : ℝ) ≤ (deep : ℝ) := by
    exact_mod_cast hDepth
  nlinarith

/-- Consequently, a deeper extraction keeps every already summable prime
majorant summable. -/
theorem prime_depth_weight_summable_mono
    {shallow deep : ℕ} {sigma : ℝ}
    (hDepth : shallow ≤ deep) (hSigma : 0 < sigma)
    (hSummable : Summable (primeDepthWeight shallow sigma)) :
    Summable (primeDepthWeight deep sigma) := by
  apply prime_depth_weight_summable
  exact summability_window_mono_depth hDepth hSigma
    ((prime_depth_weight_summable_iff shallow sigma).1 hSummable)

/-- Depth zero never gives a summable prime majorant. -/
theorem zero_depth_not_summable (sigma : ℝ) :
    ¬Summable (primeDepthWeight 0 sigma) := by
  apply prime_depth_weight_not_summable
  simp

#print axioms prime_depth_weight_summable_iff
#print axioms prime_depth_weight_summable
#print axioms prime_depth_weight_not_summable
#print axioms summability_window_mono_depth
#print axioms prime_depth_weight_summable_mono
#print axioms zero_depth_not_summable

end D5.S3.Analytic.EulerTails.PrimeDepthSummabilityWindow
