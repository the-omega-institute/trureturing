/- GID: D5/S3/ConceptDynamics/Spacetime/CopyRegionExpressibility
   generality: I
   mirror-B: none
   mirror-E: none(waiver:stage-a-open)
   anchors: []
   utility: none
   digest: Proposition 64 is compiled conditionally on the explicit unsupplied profile and saturation laws. -/

import D5.S3.ConceptDynamics.Spacetime.CopyProfilePolynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.CopyRegionExpressibility

open D5.S3.ConceptDynamics.Spacetime
open D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility
open CopyProfilePolynomial

noncomputable section

/-- Proposition 64, with the quantifiers over positive copy arity and total copy terms. -/
def Proposition64 (R : Region) : Prop :=
  CopyQExpressible R ↔ Tail R

/-- The three-way form using the existing one-hole criterion. -/
def Proposition64ThreeWay (R : Region) : Prop :=
  CopyQExpressible R ↔ QExpressible R ∧ Tail R

/-- Conditional Stage-A theorem: only the two explicit missing laws remain open. -/
theorem proposition64_of_profile_and_saturation
    (hSlice : CopySliceReadoutLaw) (hSat : CopySaturationLaw) (R : Region) :
    Proposition64 R := by
  unfold Proposition64
  constructor
  · exact copy_q_expressible_implies_tail hSlice hSat R
  · exact tail_implies_copy_q_expressible R

/-- The copy criterion agrees with the existing one-hole criterion under the same laws. -/
theorem proposition64_three_way_of_profile_and_saturation
    (hSlice : CopySliceReadoutLaw) (hSat : CopySaturationLaw) (R : Region) :
    Proposition64ThreeWay R := by
  unfold Proposition64ThreeWay
  constructor
  · intro h
    have ht : Tail R := copy_q_expressible_implies_tail hSlice hSat R h
    exact ⟨(q_expressible_iff_tail R).mpr ht, ht⟩
  · rintro ⟨_, ht⟩
    exact tail_implies_copy_q_expressible R ht

end
end D5.S3.ConceptDynamics.Spacetime.CopyRegionExpressibility
