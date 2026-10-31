import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Reg.D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
open _root_.D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact Fin.elim0 i

namespace sourcePairing_rawCoeff
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (a : Charge D) (k : ℤ) (u v : Carrier D),
    R.readout () () (sourcePairing D (rawCoeff D a k u) v)
      (paritySign (bilinear D a a / 2) *
        sourcePairing D u (rawCoeff D a (-k-bilinear D a a) v))

theorem sourceBridge :
    (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose.sourcePairing_rawCoeff)) ↔
      arena.Law complexEqual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h emptyLattice 0 0 0 0

def family : Registration arena
    (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose.sourcePairing_rawCoeff)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp
    D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose.sourcePairing_rawCoeff,
    complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose.sourcePairing_rawCoeff)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose.sourcePairing_rawCoeff "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose.sourcePairing_rawCoeff.family
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
    owner := `D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose
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
end sourcePairing_rawCoeff
end Reg.D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose
