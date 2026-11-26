import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeOccurrenceReadout
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic

/-! Dependent-family readout for native occurrence readout. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.TwistedGround
open LatticeGeneratingFieldLocality LatticeHalfFock
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMNativeOccurrenceReadout
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)
open ActualLeechHyperbolic (leechData leech_spec)
open OriginalGaussianSourceRestriction (CompactExternal externalOccupation)
open OriginalChargedRowSource (affineMoment affineCoefficient)
open NativeAffineExternalCoefficient (jetOccupation)
open FactorialFockMetric (weight)

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeOccurrenceReadout

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ {X : Type u} [Fintype X] (D : LatticeData) (F : Finset (Index D))
      (K : Matrix (CompactExternal D F ⊕ CompactExternal D F)
        (CompactExternal D F ⊕ CompactExternal D F) ℂ)
      (μ : CompactExternal D F ⊕ CompactExternal D F → ℂ)
      (_hs : ∀ i j, K i j = K j i)
      (label : X → CompactExternal D F ⊕ CompactExternal D F) (l : List X),
    let left := (l.map label).filterMap Sum.getLeft?
    let right := (l.map label).filterMap Sum.getRight?
    let b := slotOccupation D F (left.filterMap Sum.getLeft?)
    let g := slotOccupation D F (left.filterMap Sum.getRight?)
    let d := slotOccupation D F (right.filterMap Sum.getLeft?)
    let e := slotOccupation D F (right.filterMap Sum.getRight?)
    R.readout () () (affineMoment (K.submatrix label label) (μ ∘ label) (jetOccupation l))
      ((weight b : ℂ) * (weight g : ℂ) * ((weight d : ℂ) * (weight e : ℂ)) *
        affineCoefficient K μ (externalOccupation D F b g d e))

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  let oscillator : Index leechData := (Fin.cast leech_spec.1.symm 0, 0)
  let F : Finset (Index leechData) := {oscillator}
  exact h (X := PUnit.{u+1}) leechData F 0 0 (fun _ _ => rfl)
    (fun _ => .inl (.inl ⟨oscillator, Finset.mem_singleton_self _⟩)) [PUnit.unit, PUnit.unit]

def family : Registration arena.{u} (type_of% (@native_occurrence_readout.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@native_occurrence_readout.{u}, complexFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_occurrence_readout.{u}) (Realization complexSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeOccurrenceReadout.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeOccurrenceReadout.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMNativeOccurrenceReadout
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeOccurrenceReadout
