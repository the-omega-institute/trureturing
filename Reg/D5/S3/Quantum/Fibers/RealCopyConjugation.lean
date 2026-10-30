import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.RealCopyConjugation
import Reg.Support.DependentFamily

/-! Source-family audit of actual density-state copy preparation. -/

set_option autoImplicit false
noncomputable section
open scoped MatrixOrder ComplexOrder

namespace Reg.D5.S3.Quantum.Fibers.RealCopyConjugation

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open _root_.D5.S3.Quantum.Fibers.RealCopyConjugation

universe u

abbrev signature : Signature where
  Params := (n : Type u) × Fintype n × DecidableEq n
  State p := @DensityState p.1 p.2.1 p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI : Fintype p.1 := p.2.1; letI : DecidableEq p.1 := p.2.2
    (k : ℕ) → DensityState (CopyIndex p.1 k)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p rho => @copies p.1 p.2.1 p.2.2 rho)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p rho =>
    @copies p.1 p.2.1 p.2.2 (Classical.choice ⟨rho⟩)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ p : signature.Params,
    letI : Fintype p.1 := p.2.1
    letI : DecidableEq p.1 := p.2.2
    ∀ rho sigma : DensityState p.1,
      (SameRealStatistics (R.readout () p rho 2) (R.readout () p sigma 2) ↔
        sigma = rho ∨ sigma = conjugate rho) ∧
      ((∀ k, 1 ≤ k → SameRealStatistics (R.readout () p rho k) (R.readout () p sigma k)) ↔
        sigma = rho ∨ sigma = conjugate rho) ∧
      (∀ k, 2 ≤ k → (SameRealStatistics (R.readout () p rho k) (R.readout () p sigma k) ↔
        sigma = rho ∨ sigma = conjugate rho)) ∧
      (conjugate rho = rho ↔ (stateMatrix rho).map Complex.im = 0) ∧
      (∀ k, 2 ≤ k → SameRealStatistics (R.readout () p rho k) (R.readout () p sigma k) →
        (stateMatrix sigma).rank = (stateMatrix rho).rank)

private theorem bridge : (type_of% (@real_copy_classification.{u})) ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p
    exact @h p.1 p.2.1 p.2.2
  · intro h n fn dn
    exact h ⟨n, fn, dn⟩

private def basisState (i : Fin 2) : DensityState (ULift.{u} (Fin 2)) := by
  let X : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) ℂ :=
    Matrix.diagonal (Pi.single (ULift.up i) 1)
  refine ⟨CStarMatrix.ofMatrix X, ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    apply Matrix.PosSemidef.nonneg
    apply Matrix.PosSemidef.diagonal
    intro j
    by_cases h : j = ULift.up i <;> simp [h]
  · change Matrix.trace X = 1
    simp [X, Matrix.trace_diagonal]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let p : signature.{u}.Params := ⟨ULift.{u} (Fin 2), inferInstance, inferInstance⟩
  have hs := (h p (basisState 0) (basisState 1)).1.mp (by intro E; rfl)
  rcases hs with hs | hs
  · have he := congrArg (fun r => stateMatrix r (ULift.up 0) (ULift.up 0)) hs
    norm_num [basisState, stateMatrix, Matrix.diagonal, Pi.single_apply] at he
  · have he := congrArg (fun r => stateMatrix r (ULift.up 0) (ULift.up 0)) hs
    norm_num [basisState, conjugate, stateMatrix, Matrix.diagonal, Pi.single_apply] at he

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let p : signature.{u}.Params := ⟨ULift.{u} (Fin 2), inferInstance, inferInstance⟩
  refine ⟨p, basisState 0, basisState 1, ?_⟩
  intro h
  have he := congrArg (fun f => stateMatrix (f 1) (ULift.up 0) (ULift.up 0)) h
  norm_num [actual, realize, copies, basisState, stateMatrix,
    Matrix.diagonal, Pi.single_apply] at he

def family : Registration arena.{u} (type_of% (@real_copy_classification.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@real_copy_classification.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@real_copy_classification.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.RealCopyConjugation.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.RealCopyConjugation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p rho => @copies p.1 p.2.1 p.2.2 rho) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.RealCopyConjugation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 3,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.Quantum.Fibers.RealCopyConjugation


namespace Reg.D5.S3.Quantum.Fibers.RealCopyConjugation.Image
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open _root_.D5.S3.Quantum.Fibers.RealCopyConjugation
open Set
open _root_.D5.S3.Quantum.Fibers.FiveModeRealResponse
open _root_.D5.S3.Quantum.Fibers.FiveModeRealWaitSpan

def basisState (i : Fin 5) : FiveModeState := by
  let X : Matrix (Fin 5) (Fin 5) ℂ := Matrix.diagonal (Pi.single i 1)
  refine ⟨CStarMatrix.ofMatrix X, ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    apply Matrix.PosSemidef.nonneg
    apply Matrix.PosSemidef.diagonal
    intro j
    by_cases h : j = i <;> simp [h]
  · change Matrix.trace X = 1
    simp [X, Matrix.trace_diagonal]

abbrev signature : Signature where
  Params := Unit
  State _ := FiveModeState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := symmetricSpace
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ rho => fiveModeRealCoordinate rho) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := Module.finrank ℝ (affineSpan ℝ fiveModePhysicalImage).direction = 14 ∧
    (∀ rho sigma : FiveModeState,
      SameRealStatistics rho sigma ↔ R.readout () () rho = R.readout () () sigma)
private theorem coordinate_distinct : fiveModeRealCoordinate (basisState 0) ≠
    fiveModeRealCoordinate (basisState 1) := by
  intro h
  have he := congrArg (fun x : symmetricSpace => x.1 0 0) h
  norm_num [fiveModeRealCoordinate, basisState, stateMatrix, Matrix.diagonal, Pi.single_apply] at he
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := (h.2 (basisState 0) (basisState 1)).mpr rfl
  exact coordinate_distinct ((five_mode_physical_image_dimension.2 _ _).mp hs)

def family : Registration arena (type_of% five_mode_physical_image_dimension) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨five_mode_physical_image_dimension, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨(), basisState 0, basisState 1, coordinate_distinct⟩

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    five_mode_physical_image_dimension (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.RealCopyConjugation.Image.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.RealCopyConjugation.Image.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ rho => fiveModeRealCoordinate rho) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.RealCopyConjugation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "arg", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Quantum.Fibers.RealCopyConjugation.Image
