/- GID: D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation.claim; result=D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation.result; claim=D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation.claim
   digest: A two-element T1-groupoid whose reduct is not a reduced T1-groupoid. -/

import Mathlib.Data.Bool.Basic

set_option autoImplicit false

namespace D5.S3.StatisticalMechanics.VertexModels.TetrahedralGroupoidReductRefutation

/-- The four axioms of a first tetrahedral 4-groupoid, in the order of Section 9.2 of
Bardakov et al., arXiv:2206.08906v1. -/
def IsT1Groupoid {X : Type} (star circ lt rt : X → X → X) : Prop :=
  (∀ x y z, circ x y = circ (lt x z) (lt y z)) ∧
  (∀ x y z w, star (circ x y) (circ z w) = circ (star x z) (star y w)) ∧
  (∀ x y z, rt (rt x y) z = rt (rt x z) (star y z)) ∧
  (∀ x y z, lt (star x y) z = rt x (circ y z))

/-- The three axioms of a reduced first tetrahedral 4-groupoid, in the order of Section 9.2
of Bardakov et al., arXiv:2206.08906v1. -/
def IsReducedT1Groupoid {X : Type} (star circ : X → X → X) : Prop :=
  (∀ x y z, circ x y = circ (circ x z) (circ y z)) ∧
  (∀ x y z, star (star x y) z = star (star x z) (star y z)) ∧
  (∀ x y z w, star (circ x y) (circ z w) = circ (star x z) (star y w))

/-- The assertion that forgetting the two triangle operations in any T1-groupoid yields a
reduced T1-groupoid. -/
def claim : Prop := ∀ (X : Type) (star circ lt rt : X → X → X),
  IsT1Groupoid star circ lt rt → IsReducedT1Groupoid star circ

/-- Left projections for the three other operations and Boolean conjunction for `circ`
satisfy the four T1 axioms, but the first reduced axiom fails at `true, true, false`. -/
theorem result : ¬ claim := by
  intro h
  have hT1 : IsT1Groupoid (fun x _ : Bool => x) (fun x y => x && y)
      (fun x _ => x) (fun x _ => x) := by
    unfold IsT1Groupoid
    decide
  have hReduced := h Bool (fun x _ => x) (fun x y => x && y)
    (fun x _ => x) (fun x _ => x) hT1
  have hFalse : (true : Bool) = false := hReduced.1 true true false
  exact Bool.true_eq_false_eq_False hFalse

end D5.S3.StatisticalMechanics.VertexModels.TetrahedralGroupoidReductRefutation
