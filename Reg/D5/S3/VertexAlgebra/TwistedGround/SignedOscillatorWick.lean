import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFock
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.SignedOscillatorWick
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric (complexSignature complexEqual complexFalse complexEqualDependence complexNotEqual complexNotEqualDependence)
open scoped TensorProduct

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact Fin.elim0 i
private theorem emptyUnit : IsUnit emptyLattice.G.det := by
  change IsUnit (0 : Matrix (Fin 0) (Fin 0) ℤ).det
  simp
private def oneLattice : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact ⟨1, rfl⟩

namespace wick_creation
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (i : Fin D.rank) (k : ℕ) (p q : Oscillator D),
    R.readout () () (wick D (MvPolynomial.X (i,k) * p) q)
      (wick D p (-frequency (k : ℤ) • _root_.D5.S3.VertexAlgebra.LatticeActualAnnihilation.annihilate D i k q))
theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.SignedOscillatorWick.wick_creation)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h oneLattice ⟨0, by change 0 < 1; decide⟩ 0 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.SignedOscillatorWick.wick_creation)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.SignedOscillatorWick.wick_creation, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SignedOscillatorWick.wick_creation) (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SignedOscillatorWick.wick_creation "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick.wick_creation.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick
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
end wick_creation

namespace wick_lowering
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (i : Fin D.rank) (k : ℕ) (p q : Oscillator D),
    R.readout () () (wick D (-frequency (k : ℤ) • _root_.D5.S3.VertexAlgebra.LatticeActualAnnihilation.annihilate D i k p) q)
      (wick D p (MvPolynomial.X (i,k) * q))
theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.SignedOscillatorWick.wick_lowering)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h oneLattice ⟨0, by change 0 < 1; decide⟩ 0 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.SignedOscillatorWick.wick_lowering)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.SignedOscillatorWick.wick_lowering, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SignedOscillatorWick.wick_lowering) (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SignedOscillatorWick.wick_lowering "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick.wick_lowering.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick
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
end wick_lowering

namespace creation_translation_adjoint
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (a : Charge D) (n : ℤ) (p q : Oscillator D),
    R.readout () () (wick D (_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.halfCreationCoeff D a n * p) q)
      (wick D p (translatedCoeff D a n q))
theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.SignedOscillatorWick.creation_translation_adjoint)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h emptyLattice 0 0 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.SignedOscillatorWick.creation_translation_adjoint)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.SignedOscillatorWick.creation_translation_adjoint, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SignedOscillatorWick.creation_translation_adjoint) (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SignedOscillatorWick.creation_translation_adjoint "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick.creation_translation_adjoint.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick
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
end creation_translation_adjoint

namespace oscillator_coefficient_adjoint
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (a : Charge D) (e : ℤ) (p q : Oscillator D),
    R.readout () () (wick D (oscillatorCoefficient D a e p) q)
      (wick D p (oscillatorCoefficient D a (-e-2*chargeNorm D a) q))
theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.SignedOscillatorWick.oscillator_coefficient_adjoint)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h emptyLattice 0 0 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.SignedOscillatorWick.oscillator_coefficient_adjoint)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.SignedOscillatorWick.oscillator_coefficient_adjoint, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SignedOscillatorWick.oscillator_coefficient_adjoint) (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SignedOscillatorWick.oscillator_coefficient_adjoint "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick.oscillator_coefficient_adjoint.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick
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
end oscillator_coefficient_adjoint

namespace wick_nondegenerate
abbrev Params := LatticeData
abbrev Form (p : Params) := LinearMap.BilinForm ℂ (Oscillator p)
abbrev signature := Reg.Support.SingleDependentReadout.signature Params Form Form
def actual : Realization signature := realize signature (fun _ _ B => B) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det),
    (R.readout () D (wick D)).Nondegenerate

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.SignedOscillatorWick.wick_nondegenerate)) ↔ arena.Law actual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact (h emptyLattice emptyUnit).ne_zero rfl
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨emptyLattice, 0, wick emptyLattice, ?_⟩
  change (0 : LinearMap.BilinForm ℂ _) ≠ _
  exact Ne.symm ((D5.S3.VertexAlgebra.SignedOscillatorWick.wick_nondegenerate emptyLattice emptyUnit).ne_zero)
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.SignedOscillatorWick.wick_nondegenerate)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.SignedOscillatorWick.wick_nondegenerate, rejected, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SignedOscillatorWick.wick_nondegenerate) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SignedOscillatorWick.wick_nondegenerate "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick.wick_nondegenerate.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick
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
end wick_nondegenerate


end Reg.D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick
