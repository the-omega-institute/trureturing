import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity
import Reg.Support.DependentFamily

/-! Full-source dependent-family audit of matrix readouts. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity

@[reducible] def signature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Matrix (Fin d) (Fin d) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ E => E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (E rho : Matrix (Fin d) (Fin d) ℂ),
    E.PosSemidef → rho.PosSemidef → (E * rho).trace = 0 →
    LinearMap.range rho.toEuclideanLin ≤ LinearMap.ker (R.readout () d E).toEuclideanLin

private theorem actual_law : arena.Law actual := by
  intro d E rho hE hRho hTrace
  exact zero_trace_support E rho hE hRho hTrace

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (d := 1) 0 1 Matrix.PosSemidef.zero Matrix.PosSemidef.one (by simp)
  simpa [rejected, realize, Matrix.toEuclideanLin] using hh

def family : Registration arena (type_of% (@zero_trace_support)) where
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
    (@zero_trace_support) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity.zeroTraceSupportUnit
  realizationName := `Reg.D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ E => E) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity
