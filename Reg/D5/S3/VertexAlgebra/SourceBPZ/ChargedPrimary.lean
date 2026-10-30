import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.SourceBPZ.ChargedPrimary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Reg.D5.S3.VertexAlgebra.SourceBPZ.ChargedPrimary

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeAllStateField
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)
open scoped VertexOperator

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact Fin.elim0 i

namespace sourcePairing_charged_primary

def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (a : Charge D) (m : ℤ) (u v : Carrier D),
    R.readout () () (sourcePairing D ((Y D (Finsupp.single a 1))[[m]] u) v)
      (paritySign (chargeEnergy D a) * sourcePairing D u
        ((Y D (Finsupp.single a 1))[[2*chargeEnergy D a-m-2]] v))

theorem sourceBridge :
    (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.ChargedPrimary.sourcePairing_charged_primary)) ↔
      arena.Law complexEqual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h emptyLattice 0 0 0 0

def family : Registration arena
    (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.ChargedPrimary.sourcePairing_charged_primary)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.SourceBPZ.ChargedPrimary.sourcePairing_charged_primary,
    complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SourceBPZ.ChargedPrimary.sourcePairing_charged_primary)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.SourceBPZ.ChargedPrimary.sourcePairing_charged_primary "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.SourceBPZ.ChargedPrimary.sourcePairing_charged_primary.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.SourceBPZ.ChargedPrimary
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end sourcePairing_charged_primary
end Reg.D5.S3.VertexAlgebra.SourceBPZ.ChargedPrimary
