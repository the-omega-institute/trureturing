import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open _root_.D5.S3.VertexAlgebra.LatticeInvolution
open _root_.D5.S3.VertexAlgebra.LatticeAllStateField
open _root_.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
open _root_.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact Fin.elim0 i

private def oneLattice : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact ⟨1, rfl⟩

namespace integerWick_creation
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (i : Fin D.rank) (k : ℕ) (p q : Oscillator D),
    R.readout () () (integerWick D (MvPolynomial.X (i,k) * p) q)
      (integerWick D p (-((k : ℂ)+1) • _root_.D5.S3.VertexAlgebra.LatticeActualAnnihilation.annihilate D i k q))

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_creation)) ↔ arena.Law complexEqual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h oneLattice ⟨0, by change 0 < 1; decide⟩ 0 0 0

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_creation)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_creation, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_creation)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_creation "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_creation.family
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
    owner := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
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
end integerWick_creation

namespace integerWick_lowering
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (i : Fin D.rank) (k : ℕ) (p q : Oscillator D),
    R.readout () () (integerWick D (-((k : ℂ)+1) • _root_.D5.S3.VertexAlgebra.LatticeActualAnnihilation.annihilate D i k p) q)
      (integerWick D p (MvPolynomial.X (i,k) * q))

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_lowering)) ↔ arena.Law complexEqual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h oneLattice ⟨0, by change 0 < 1; decide⟩ 0 0 0

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_lowering)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_lowering, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_lowering)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_lowering "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_lowering.family
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
    owner := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
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
end integerWick_lowering

namespace integerWick_symmetric
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (p q : Oscillator D),
    R.readout () () (integerWick D p q) (integerWick D q p)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_symmetric)) ↔ arena.Law complexEqual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h emptyLattice 0 0

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_symmetric)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_symmetric, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_symmetric)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_symmetric "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_symmetric.family
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
    owner := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end integerWick_symmetric

namespace sourcePairing_symmetric
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (u v : Carrier D),
    R.readout () () (sourcePairing D u v) (sourcePairing D v u)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_symmetric)) ↔ arena.Law complexEqual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h emptyLattice 0 0

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_symmetric)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_symmetric, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_symmetric)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_symmetric "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_symmetric.family
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
    owner := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end sourcePairing_symmetric

namespace sourcePairing_vacuum
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData),
    R.readout () () (sourcePairing D (vacuum D) (vacuum D)) 1

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_vacuum)) ↔ arena.Law complexEqual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h emptyLattice

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_vacuum)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_vacuum, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_vacuum)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_vacuum "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_vacuum.family
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
    owner := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end sourcePairing_vacuum

private theorem emptyUnit : IsUnit emptyLattice.G.det := by
  change IsUnit (0 : Matrix (Fin 0) (Fin 0) ℤ).det
  simp

namespace integerWick_nondegenerate
abbrev Form (D : LatticeData) := LinearMap.BilinForm ℂ (Oscillator D)
abbrev signature := Reg.Support.SingleDependentReadout.signature LatticeData Form Form
def actual : Realization signature := realize signature (fun _ _ B => B) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (_hu : IsUnit D.G.det),
    (R.readout () D (integerWick D)).Nondegenerate

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_nondegenerate)) ↔ arena.Law actual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact (h emptyLattice emptyUnit).ne_zero rfl
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨emptyLattice, 0, integerWick emptyLattice, ?_⟩
  change (0 : LinearMap.BilinForm ℂ _) ≠ _
  exact Ne.symm ((D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_nondegenerate emptyLattice emptyUnit).ne_zero)
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_nondegenerate)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_nondegenerate, rejected, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_nondegenerate) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_nondegenerate "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.integerWick_nondegenerate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end integerWick_nondegenerate

namespace sourcePairing_nondegenerate
abbrev Form (D : LatticeData) := LinearMap.BilinForm ℂ (Carrier D)
abbrev signature := Reg.Support.SingleDependentReadout.signature LatticeData Form Form
def actual : Realization signature := realize signature (fun _ _ B => B) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (_hu : IsUnit D.G.det),
    (R.readout () D (sourcePairing D)).Nondegenerate

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_nondegenerate)) ↔ arena.Law actual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact (h emptyLattice emptyUnit).ne_zero rfl
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨emptyLattice, 0, sourcePairing emptyLattice, ?_⟩
  change (0 : LinearMap.BilinForm ℂ _) ≠ _
  exact Ne.symm ((D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_nondegenerate emptyLattice emptyUnit).ne_zero)
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_nondegenerate)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_nondegenerate, rejected, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_nondegenerate) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_nondegenerate "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing.sourcePairing_nondegenerate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end sourcePairing_nondegenerate

end Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
