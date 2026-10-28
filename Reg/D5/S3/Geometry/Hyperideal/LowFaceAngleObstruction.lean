import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.Hyperideal.LowFaceAngleObstruction

/-!
# Dependent source families for low-face transport

These source bridges retain the finite tetrahedron type, original face pairing,
actual quotient length field, selected middle length and global edge. The angle
family also retains every local angle. They establish the actual laws; full
four-slot registration requires variation, sensitivity, observational dependence
and complete source reconstruction and occurrence ties.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace Reg.D5.S3.Geometry.Hyperideal.LowFaceAngleObstruction

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.EdgeStarTransitions
open _root_.D5.S3.Geometry.Hyperideal.LowFaceAngleObstruction

attribute [local instance] Classical.propDecidable

structure Inputs.{u} where
  T : Type u
  finite : Fintype T
  pairing : RawFacePairing T
  length : pairing.GlobalEdge → ℝ
  middle : ℝ
  edge : pairing.GlobalEdge

abbrev shape.{u} (P : Inputs.{u}) : Prop :=
  ∀ t, BlockShape (fun j => P.length (P.pairing.edgeLabel t j)) P.middle

abbrev middleEdge.{u} (P : Inputs.{u}) : Prop := P.length P.edge = P.middle

namespace Count

abbrev sourceScope.{u} :=
  type_of% (@_root_.D5.S3.Geometry.Hyperideal.LowFaceAngleObstruction.genuine_occurrences_even.{u})

abbrev signature.{u} : Signature where
  Params := Inputs.{u}
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u} : Realization signature.{u} := realize signature
  (fun _ P _ => by
    letI := P.finite
    exact Fintype.card {i : Occurrence P.T //
      P.pairing.edgeLabel i.1 i.2 = P.edge ∧
        ∃ a, P.length (P.pairing.edgeLabel i.1 a) < P.middle})
  (fun e => nomatch e)

abbrev arena.{u} : Arena where
  signature := signature.{u}
  Law R := ∀ P : Inputs.{u}, shape P → middleEdge P →
    Even (R.readout () P ())

theorem source_bridge.{u} : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P hs he
    letI := P.finite
    exact h P.pairing P.length P.middle hs P.edge he
  · intro h T finite p length middle hs edge he
    exact h ⟨T, finite, p, length, middle, edge⟩ hs he

theorem actual_positive.{u} : arena.{u}.Law actual.{u} := source_bridge.mp
  (@_root_.D5.S3.Geometry.Hyperideal.LowFaceAngleObstruction.genuine_occurrences_even.{u})

end Count

structure AngleInputs.{u} extends Inputs.{u} where
  angle : Occurrence T → ℝ

abbrev angleShape.{u} (P : AngleInputs.{u}) : Prop :=
  ∀ i : Occurrence P.T, P.pairing.edgeLabel i.1 i.2 = P.edge →
    ((∃ a, P.length (P.pairing.edgeLabel i.1 a) < P.middle) →
      Real.pi / 3 < P.angle i ∧ P.angle i < Real.pi / 2) ∧
    ((¬ ∃ a, P.length (P.pairing.edgeLabel i.1 a) < P.middle) → P.angle i = 0)

namespace Angle

abbrev sourceScope.{u} :=
  type_of% (@_root_.D5.S3.Geometry.Hyperideal.LowFaceAngleObstruction.middle_edge_angle_sum_ne_two_pi.{u})

abbrev signature.{u} : Signature where
  Params := AngleInputs.{u}
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u} : Realization signature.{u} := realize signature
  (fun _ P _ => by
    letI := P.finite
    exact ∑ i : {i : Occurrence P.T // P.pairing.edgeLabel i.1 i.2 = P.edge},
      P.angle i.1)
  (fun e => nomatch e)

abbrev arena.{u} : Arena where
  signature := signature.{u}
  Law R := ∀ P : AngleInputs.{u}, shape P.toInputs → middleEdge P.toInputs →
    angleShape P → R.readout () P () ≠ 2 * Real.pi

theorem source_bridge.{u} : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P hs he ha
    letI := P.finite
    exact h P.pairing P.length P.middle hs P.edge he P.angle ha
  · intro h T finite p length middle hs edge he angle ha
    exact h ⟨⟨T, finite, p, length, middle, edge⟩, angle⟩ hs he ha

theorem actual_positive.{u} : arena.{u}.Law actual.{u} := source_bridge.mp
  (@_root_.D5.S3.Geometry.Hyperideal.LowFaceAngleObstruction.middle_edge_angle_sum_ne_two_pi.{u})

end Angle

#print axioms Count.source_bridge
#print axioms Count.actual_positive
#print axioms Angle.source_bridge
#print axioms Angle.actual_positive

end Reg.D5.S3.Geometry.Hyperideal.LowFaceAngleObstruction
