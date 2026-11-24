import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAssignedOccupation
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic

/-! Dependent-family equality at a fixed charge before summing over the fibre. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.TwistedGround
open LatticeGeneratingFieldLocality LatticeHalfFock
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAssignedOccupation
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)
open ActualLeechHyperbolic (leechData leech_spec)
open FourPoint.OriginalFourMActualChart (Chart Puncture parameter)
open OriginalFourMFixedChargeWick (Mode)

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAssignedOccupation

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ {X : Type u} {n : X → ℕ} [Fintype X] [DecidableEq X]
      (D : LatticeData) (q : Charge D) (c : Chart) {x : ℝ} (_hx : 0 < x) (_hx₁ : x < 1)
      (_hc : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D)
      (slot : X → Puncture) (colour : X → Fin D.rank) (F : Finset (Index D))
      (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) (l : List X),
    R.readout () () (compactChargeTerm D slot colour c x q F hF l)
      (punctureChargeTerm D slot colour c x q F hF l)

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  let colour : Fin leechData.rank := Fin.cast leech_spec.1.symm 0
  let F : Finset (Index leechData) := {(colour, 0)}
  refine h (X := PUnit.{u+1}) (n := fun _ => 0) leechData 0 .D (x := 1 / 2)
    (by norm_num) (by norm_num) (Or.inr rfl) (fun _ => .P) (fun _ => colour) F
    (fun a => ?_) [PUnit.unit]
  have hi := a.2.isLt
  change a.2.val < 1 at hi
  have hz : a.2.val = 0 := by omega
  simpa [hz, F]

def family : Registration arena.{u} (type_of% (@compact_charge_eq_punctures.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@compact_charge_eq_punctures.{u}, complexFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@compact_charge_eq_punctures.{u}) (Realization complexSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAssignedOccupation.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAssignedOccupation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAssignedOccupation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAssignedOccupation
