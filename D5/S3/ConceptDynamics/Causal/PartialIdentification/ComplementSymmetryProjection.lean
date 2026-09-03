/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/ComplementSymmetryProjection
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/ComplementSymmetryProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal averaging with a complementary parameter projects every value to one half while erasing the antisymmetric centered defect. -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-09-03):
   * `CovariateSharedParameterObstruction` contains the concrete two-stratum
     singleton query at one half.
   * Repository searches for an involutive complement average, its centered
     antisymmetric defect, and uniqueness of the equal-weight cancellation
     returned no reusable theorem.
   * This module isolates the algebraic symmetry mechanism. It makes no claim
     about the Riemann zeta function or localization of its zeros. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.ComplementSymmetryProjection

/-- Complement involution on a real affine coordinate. -/
def complement (theta : Real) : Real := 1 - theta

/-- Equal averaging of a parameter and its complement. -/
def symmetricAverage (theta : Real) : Real :=
  (theta + complement theta) / 2

/-- The component reversed by the complement involution. -/
def centeredDefect (theta : Real) : Real :=
  theta - 1 / 2

/-- Symmetrization projects every real parameter to the center one half. -/
theorem symmetricAverage_eq_half (theta : Real) :
    symmetricAverage theta = 1 / 2 := by
  unfold symmetricAverage complement
  ring

/-- The centered defect changes sign under complementation. -/
theorem centeredDefect_complement (theta : Real) :
    centeredDefect (complement theta) = -centeredDefect theta := by
  unfold centeredDefect complement
  ring

/-- A point is fixed by complementation exactly at the affine center. -/
theorem complement_fixed_iff_centered (theta : Real) :
    complement theta = theta <-> theta = 1 / 2 := by
  unfold complement
  constructor <;> intro hypothesis <;> linarith

/-- Symmetric averaging cannot identify whether the original parameter was at
the center: an off-center parameter has the same symmetrized value. -/
theorem symmetric_average_does_not_identify_center :
    exists theta : Real,
      theta ≠ 1 / 2 /\ symmetricAverage theta = 1 / 2 := by
  exact ⟨0, by norm_num, symmetricAverage_eq_half 0⟩

/-- Complementary strata with arbitrary first weight. -/
def weightedComplementaryQuery
    (weight theta : Real) : Real :=
  weight * theta + (1 - weight) * complement theta

/-- The complementary weighted query separates into a constant center term and
an antisymmetric coefficient. -/
theorem weightedComplementaryQuery_decomposition
    (weight theta : Real) :
    weightedComplementaryQuery weight theta =
      (1 - weight) + (2 * weight - 1) * theta := by
  unfold weightedComplementaryQuery complement
  ring

/-- Cancellation for every shared parameter occurs exactly at equal weight.
At that weight the constant identified value is one half. -/
theorem weightedComplementaryQuery_constant_half_iff
    (weight : Real) :
    (forall theta : Real,
      weightedComplementaryQuery weight theta = 1 / 2) <->
      weight = 1 / 2 := by
  constructor
  · intro constant
    have at_zero := constant 0
    unfold weightedComplementaryQuery complement at at_zero
    linarith
  · intro equal_weight
    subst weight
    intro theta
    unfold weightedComplementaryQuery complement
    ring

#print axioms symmetricAverage_eq_half
#print axioms centeredDefect_complement
#print axioms complement_fixed_iff_centered
#print axioms symmetric_average_does_not_identify_center
#print axioms weightedComplementaryQuery_constant_half_iff

end D5.S3.ConceptDynamics.Causal.PartialIdentification.ComplementSymmetryProjection
