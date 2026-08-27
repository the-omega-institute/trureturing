/- GID: D5/S3/Observer/ArithmeticTomography/ThreeFiveResidueCollisionDimension
   generality: G
   mirror-B: D5/B/S3/Observer/ArithmeticTomography/ThreeFiveResidueCollisionDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The three-five residue collision accompanies statistical dimension three. -/

import D5.S3.Observer.ArithmeticTomography.ResidueCoordinateDimension

/- Library-search audit trail (2026-08-28):
   * The parent theorem is frozen as `statistical_dimension_eq_three`, but its
     public statement omits this clause's required three-five collision.
   * The same canonical family separately exposes the exact collision as
     `q3_q5_collision`; no D5 declaration states both required public clauses.
   * Pinned Mathlib provides the underlying `ZMod.equivPi`, but has no theorem
     combining this concrete collision with the repository statistical dimension. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ArithmeticTomography.ThreeFiveResidueCollisionDimension

open D5.S3.Observer.ArithmeticTomography.ResidueCoordinateDimension

/-- The coordinates modulo three and five merge zero with fifteen, while the
minimum complete coordinate count for the same canonical system is three. -/
theorem three_five_residue_collision_and_dimension :
    Merges {q3, q5} 0 15 /\ statisticalDimension = 3 := by
  exact ⟨q3_q5_collision, statistical_dimension_eq_three⟩

#print axioms three_five_residue_collision_and_dimension

end D5.S3.Observer.ArithmeticTomography.ThreeFiveResidueCollisionDimension
