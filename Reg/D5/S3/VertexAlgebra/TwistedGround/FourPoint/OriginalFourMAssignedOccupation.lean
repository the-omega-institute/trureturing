import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAssignedOccupation
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic

/-! Dependent-family readout for compactCovariance d symm. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.TwistedGround
open LatticeGeneratingFieldLocality LatticeHalfFock
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAssignedOccupation
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)
open ActualLeechHyperbolic (leechData leech_spec)
open FourPoint.OriginalFourMActualChart (Chart)
open OriginalGaussianSourceRestriction (CompactExternal)

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAssignedOccupation

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) {x : ℝ} (_hx : 0 < x) (_hx₁ : x < 1)
      (F : Finset (Index D)) (a b : CompactExternal D F ⊕ CompactExternal D F),
    R.readout () () (compactCovariance D .D x F a b) (compactCovariance D .D x F b a)

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  let oscillator : Index leechData := (Fin.cast leech_spec.1.symm 0, 0)
  let F : Finset (Index leechData) := {oscillator}
  have hi : oscillator ∈ F := Finset.mem_singleton_self _
  exact h leechData (x := 1 / 2) (by norm_num) (by norm_num) F
    (.inl (.inl ⟨oscillator, hi⟩)) (.inr (.inr ⟨oscillator, hi⟩))

def family : Registration arena (type_of% (@compactCovariance_d_symm)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@compactCovariance_d_symm, complexFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@compactCovariance_d_symm) (Realization complexSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAssignedOccupation.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAssignedOccupation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
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
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAssignedOccupation
