/- GID: D5/S3/Analytic/Adelic/ToroidalCommonZeroLocus
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/ToroidalCommonZeroLocus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pointwise nonvanishing quadratic twists identify the common period-zero locus with xi. -/

import D5.S3.Analytic.Adelic.ToroidalCechCompletion

/- Library-search audit trail (2026-08-29):
   * Repository searches for a toroidal common-zero theorem and for the body
     shape `forall index, period index point = 0` found no exact owner.
   * `toroidal_cech_completion` supplies the canonical complex period/twist
     carrier and factorization shape, but proves overlap gluing and uniqueness
     rather than the common-zero-locus equality below.
   * Pinned Mathlib has no exact product-family zero-locus theorem.
     `mul_eq_zero` is the exact algebraic constituent applied in the reverse
     inclusion. No new definition or carrier is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Adelic.ToroidalCommonZeroLocus

open D5.S3.Zeros.CompletedZeta

/-- On a regular spectral domain, a point is invisible to every factored
quadratic-period readout exactly when the canonical completed-zeta amplitude
vanishes there. -/
theorem toroidal_common_zero_locus {Index : Type*} (Omega : Set ℂ)
    (period twist : Index -> ℂ -> ℂ)
    (factorization : ∀ index point,
      period index point = xiReading point * twist index point)
    (pointwiseNonvanishing : ∀ point ∈ Omega, ∃ index, twist index point ≠ 0) :
    {point : Omega | ∀ index, period index point.1 = 0} =
      {point : Omega | xiReading point.1 = 0} := by
  ext point
  simp only [Set.mem_setOf_eq]
  constructor
  · intro allPeriodsZero
    obtain ⟨index, twistNonzero⟩ :=
      pointwiseNonvanishing point.1 point.2
    have productZero : xiReading point.1 * twist index point.1 = 0 := by
      rw [← factorization]
      exact allPeriodsZero index
    exact (mul_eq_zero.mp productZero).resolve_right twistNonzero
  · intro xiZero index
    rw [factorization, xiZero, zero_mul]

#print axioms toroidal_common_zero_locus

end D5.S3.Analytic.Adelic.ToroidalCommonZeroLocus
