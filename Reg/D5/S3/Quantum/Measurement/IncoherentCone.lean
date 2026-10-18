import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.IncoherentCone
import Reg.Support.DependentFamily

/-! Full-source dependent-family audit of matrix readouts. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.IncoherentCone
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.IncoherentCone

@[reducible] def signature : Signature where
  Params := ℕ
  State n := Matrix (Fin n) (Fin n) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (Fin n) (Fin n) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ A => A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}, A.PosSemidef →
    ∀ j : Fin n, (A j j).re ≤ RHLinalg.rtrace (R.readout () n A)

private theorem actual_law : arena.Law actual := by
  intro n A hA j
  exact psd_diag_le_trace hA j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (A := (1 : Matrix (Fin 1) (Fin 1) ℂ)) Matrix.PosSemidef.one 0
  norm_num [rejected, realize, RHLinalg.rtrace, Matrix.trace] at hh
  change (1 : ℝ) ≤ 0 at hh
  exact (not_le_of_gt zero_lt_one) hh

def family : Registration arena (type_of% (@psd_diag_le_trace)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i; cases j
      exact (hji rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    change ObservationalDependence signature actual
    intro i
    exact ⟨1, 0, 1, zero_ne_one⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@psd_diag_le_trace) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.IncoherentCone.psdDiagUnit
  realizationName := `Reg.D5.S3.Quantum.Measurement.IncoherentCone.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.IncoherentCone
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Measurement.IncoherentCone
