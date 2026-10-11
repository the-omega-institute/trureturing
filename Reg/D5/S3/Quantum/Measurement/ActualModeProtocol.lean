import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.ActualModeProtocol
import Reg.Support.DependentFamily

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped NNReal
open D5.S3.Quantum.Measurement.ActualModeProtocol
open D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw (actualWait)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Measurement.ActualModeProtocol

structure Parameters where
  Index : Type
  finite : Fintype Index
  decEq : DecidableEq Index

def signature : Signature where
  Params := Parameters
  State p := Matrix p.Index p.Index ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p X => letI := p.finite; (Matrix.trace (X : Matrix p.Index p.Index ℂ) : ℂ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (hK : K.IsHermitian) (t : ℝ≥0) (X : Matrix ι ι ℂ),
    Matrix.trace (waitState K t X) =
      R.readout () ⟨ι, inferInstance, inferInstance⟩ X

theorem actual_law : arena.Law actual := by
  intro ι _ _ K hK t X
  exact waitState_trace K hK t X

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h (ι := Unit) 0 (by simp) 0 1
  simp [rejected, realize, waitState, actualWait, Matrix.trace] at h0

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji ((show j = i by cases j; cases i; rfl))).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Unit, inferInstance, inferInstance⟩, (0 : Matrix Unit Unit ℂ),
    (1 : Matrix Unit Unit ℂ), ?_⟩
  simp [actual, realize, Matrix.trace]
  exact (zero_ne_one : (0 : ℂ) ≠ 1)

def evidence : Registration arena
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (K : Matrix ι ι ℂ) (hK : K.IsHermitian) (t : ℝ≥0) (X : Matrix ι ι ℂ),
      Matrix.trace (waitState K t X) = Matrix.trace X) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof


def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurement.ActualModeProtocol.waitState_trace)
    (type_of% (realize signature (fun _ p X => letI := p.finite; (Matrix.trace (X : Matrix p.Index p.Index ℂ) : ℂ))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Measurement.ActualModeProtocol.waitState_trace.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Measurement.ActualModeProtocol.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p X => letI := p.finite; (Matrix.trace (X : Matrix p.Index p.Index ℂ) : ℂ))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.ActualModeProtocol,
    definition := none,
    coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"],
      stateBinder := 6, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration

end Reg.D5.S3.Quantum.Measurement.ActualModeProtocol
