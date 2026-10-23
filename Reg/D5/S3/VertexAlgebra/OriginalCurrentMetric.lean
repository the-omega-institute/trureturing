
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.OriginalCurrentMetric
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-!
Dependent-family realizations for positivity of k+1/2, nonvanishing of its
complex square root, and the square-root identity. The laws quantify over
every natural mode, with their complete original theorem telescopes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.VertexAlgebra.OriginalCurrentMetric
open _root_.D5.S3.VertexAlgebra.OriginalGram
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev realSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def realActual : Realization realSignature :=
  realize realSignature (fun _ _ k => modeReal k) (fun e => nomatch e)

def realRejected : Realization realSignature :=
  realize realSignature (fun _ _ _ => 0) (fun e => nomatch e)

def realArena : Arena where
  signature := realSignature
  Law R := ∀ k : ℕ, 0 < R.readout () () k

theorem realRejected_law : ¬ realArena.Law realRejected := by
  intro h
  have hzero : (0 : ℝ) < 0 := h 0
  exact (lt_irrefl 0) hzero

def realProof : Registration realArena (type_of% (@modeReal_pos)) where
  actual := realActual
  bridge := Iff.rfl
  variation := ⟨modeReal_pos, realRejected, realRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    realArena.Law realActual realRejected realRejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change (modeReal 0 : ℝ) ≠ modeReal 1
    norm_num [modeReal]

def modeReal_pos_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.VertexAlgebra.OriginalGram.modeReal_pos)
    (Realization realSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.OriginalCurrentMetric.modeReal_pos
  realizationName := `Reg.D5.S3.VertexAlgebra.OriginalCurrentMetric.realProof
  realizationSource := none
  generated := false
  arena := .source ⟨realArena⟩
  objectArena := .source ⟨realArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source realArena ⟨realProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature (fun _ _ k => modeReal k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.OriginalCurrentMetric
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "arg"], stateBinder := 0,
        functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev complexSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℂ)

def complexActual : Realization complexSignature :=
  realize complexSignature (fun _ _ k => modeScale k) (fun e => nomatch e)

def complexRejected : Realization complexSignature :=
  realize complexSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem complexActual_dependence : ObservationalDependence complexSignature complexActual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  change modeScale 0 ≠ modeScale 1
  intro h
  have hzero := modeScale_square 0
  have hone := modeScale_square 1
  rw [h, hone] at hzero
  norm_num at hzero

def nonzeroArena : Arena where
  signature := complexSignature
  Law R := ∀ k : ℕ, R.readout () () k ≠ 0

theorem nonzeroRejected_law : ¬ nonzeroArena.Law complexRejected := by
  intro h
  exact h 0 rfl

def nonzeroProof : Registration nonzeroArena (type_of% (@modeScale_ne_zero)) where
  actual := complexActual
  bridge := Iff.rfl
  variation := ⟨modeScale_ne_zero, complexRejected, nonzeroRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    nonzeroArena.Law complexActual complexRejected nonzeroRejected_law
  dependence := complexActual_dependence

def modeScale_ne_zero_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.VertexAlgebra.OriginalGram.modeScale_ne_zero)
    (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.OriginalCurrentMetric.modeScale_ne_zero
  realizationName := `Reg.D5.S3.VertexAlgebra.OriginalCurrentMetric.nonzeroProof
  realizationSource := none
  generated := false
  arena := .source ⟨nonzeroArena⟩
  objectArena := .source ⟨nonzeroArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nonzeroArena ⟨nonzeroProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature (fun _ _ k => modeScale k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.OriginalCurrentMetric
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "fn", "arg"], stateBinder := 0,
        functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def squareArena : Arena where
  signature := complexSignature
  Law R := ∀ k : ℕ, R.readout () () k * R.readout () () k = (k : ℂ) + 1 / 2

theorem squareRejected_law : ¬ squareArena.Law complexRejected := by
  intro h
  have hzero := h 0
  norm_num [complexRejected, realize] at hzero

def squareProof : Registration squareArena (type_of% (@modeScale_square)) where
  actual := complexActual
  bridge := Iff.rfl
  variation := ⟨modeScale_square, complexRejected, squareRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    squareArena.Law complexActual complexRejected squareRejected_law
  dependence := complexActual_dependence

def modeScale_square_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.VertexAlgebra.OriginalGram.modeScale_square)
    (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.OriginalCurrentMetric.modeScale_square
  realizationName := `Reg.D5.S3.VertexAlgebra.OriginalCurrentMetric.squareProof
  realizationSource := none
  generated := false
  arena := .source ⟨squareArena⟩
  objectArena := .source ⟨squareArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source squareArena ⟨squareProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature (fun _ _ k => modeScale k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.OriginalCurrentMetric
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "fn", "arg", "fn", "arg"], stateBinder := 0,
        functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "fn", "arg", "arg"], stateBinder := 0,
        functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.OriginalCurrentMetric
