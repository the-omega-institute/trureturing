/- GID: D5/S3/ConceptDynamics/Spacetime/CopyRegionExpressibility
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/CopyRegionExpressibility
   mirror-E: none(waiver:stage-a-open)
   anchors: []
   utility: none
   digest: Positive total native copy expressibility is equivalent to the uniform past-tail criterion. -/

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

/-- Proposition 64 with no profile or saturation assumptions. -/
theorem proposition64 (R : Region) :
    CopyQExpressible R ↔ Tail R := by
  constructor
  · exact copy_q_expressible_implies_tail R
  · exact tail_implies_copy_q_expressible R

/-- The copy criterion agrees with the existing one-hole criterion and the tail condition. -/
theorem proposition64_three_way (R : Region) :
    CopyQExpressible R ↔ QExpressible R ∧ Tail R := by
  constructor
  · intro h
    have ht : Tail R := copy_q_expressible_implies_tail R h
    exact ⟨(q_expressible_iff_tail R).mpr ht, ht⟩
  · rintro ⟨_, ht⟩
    exact tail_implies_copy_q_expressible R ht

end
end D5.S3.ConceptDynamics.Spacetime.CopyRegionExpressibility
