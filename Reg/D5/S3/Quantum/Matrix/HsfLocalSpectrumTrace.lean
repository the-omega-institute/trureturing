import D5.S3.Quantum.Matrix.HsfLocalSpectrumTrace
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Full-telescope source-binding attempt for actual CFC trace normalization.
Source-selection reconstruction and the escape coordinate remain unresolved
under https://github.com/the-omega-institute/trureturing/issues/23103.
This attempt does not assert declared_validated. -/

set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix.HsfLocalSpectrumTrace
open _root_.D5.S3.Quantum.Matrix.RpowPencilTaylor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Reg.D5.S3.Quantum.Matrix.HsfLocalSpectrumTrace
noncomputable section
universe u

private abbrev signature : Signature where
  Params := Unit
  State _ := (ℂ × ℂ) × (ℂ × ℂ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1.1 = s.1.2 ∧ s.2.1 = s.2.2) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ {n : Type u} [Fintype n] [DecidableEq n] {Y K : Matrix n n ℂ},
    Y.PosDef → K.IsHermitian →
    let P := CFC.rpow Y (1 / 3 : ℝ)
    let B := jetCoeff (fun t : ℝ => P⁻¹ * CFC.rpow (Y + t • K) (2 / 3 : ℝ) * P⁻¹)
    let Q := K * (P⁻¹) ^ 3
    F.readout () () ((Matrix.trace (B 2) - Matrix.trace (B 1 * B 1) / 2,
      -Matrix.trace (Q ^ 2) / 3), (Matrix.trace (B 3) - Matrix.trace (B 1 * B 2) +
      Matrix.trace (B 1 * B 1 * B 1) / 3, 2 * Matrix.trace (Q ^ 3) / 9))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (n := ULift.{u} Unit) (Y := 1) (K := 0) Matrix.PosDef.one
    (by simp : (0 : Matrix _ _ ℂ).IsHermitian)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), ((0, 0), (0, 0)), ((0, 1), (0, 0)), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfLocalSpectrumTrace.actual_trace_normalization.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfLocalSpectrumTrace.actual_trace_normalization.{u},
    rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.HsfLocalSpectrumTrace.actual_trace_normalization.{u})
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfLocalSpectrumTrace.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfLocalSpectrumTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ s => s.1.1 = s.1.2 ∧ s.2.1 = s.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end
end Reg.D5.S3.Quantum.Matrix.HsfLocalSpectrumTrace
