import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.PauliFunding.ParityTraceComparison
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Matrix.PauliFunding.ParityTraceComparison
open _root_.D5.S3.Quantum.Matrix.PauliFunding
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
set_option autoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Mat (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ W j => _root_.Matrix.trace (W ^ (2 * j))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(2 : ℝ) • (1 : Mat), 0, 1, ?_⟩
  intro he
  norm_num [actual, realize, _root_.Matrix.smul_pow, _root_.Matrix.trace_fin_two] at he

namespace Formula

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (W : Mat) (α β : ℝ), 0 ≤ β →
    _root_.Matrix.trace W = 2 * α → _root_.Matrix.det W = -β →
    ∀ j : ℕ, R.readout () W j = evenMoment α β j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh 0 0 0 le_rfl (by simp) (by simp) 1
  norm_num [rejected, realize, evenMoment] at he

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.PauliFunding.even_trace_formula)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.PauliFunding.even_trace_formula, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.PauliFunding.even_trace_formula) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.ParityTraceComparison.Formula.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.ParityTraceComparison.Formula.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ W j => _root_.Matrix.trace (W ^ (2 * j))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.PauliFunding.ParityTraceComparison
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Formula

namespace Comparison

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (W : Mat) (α β c : ℝ), 0 ≤ α → 0 ≤ β → 0 ≤ c →
    _root_.Matrix.trace W = 2 * α → _root_.Matrix.det W = -β →
    c ^ 2 - 2 * α * c - β ≤ 0 → ∀ j : ℕ, c ^ (2 * j) ≤ R.readout () W j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh 0 0 0 0 le_rfl le_rfl le_rfl (by simp) (by simp) (by simp) 1
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.PauliFunding.even_trace_comparison)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.PauliFunding.even_trace_comparison, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.PauliFunding.even_trace_comparison) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.ParityTraceComparison.Comparison.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.ParityTraceComparison.Comparison.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ W j => _root_.Matrix.trace (W ^ (2 * j))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.PauliFunding.ParityTraceComparison
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Comparison

namespace Strict

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (W : Mat) (α β c : ℝ), 0 ≤ α → 0 ≤ β → 0 ≤ c →
    _root_.Matrix.trace W = 2 * α → _root_.Matrix.det W = -β →
    c ^ 2 - 2 * α * c - β < 0 → ∀ j : ℕ, 1 ≤ j → c ^ (2 * j) < R.readout () W j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh parity 0 1 0 le_rfl (by norm_num) le_rfl
    (by norm_num [parity, _root_.Matrix.trace_fin_two])
    (by norm_num [parity, _root_.Matrix.det_fin_two]) (by norm_num) 1 le_rfl
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.PauliFunding.even_trace_strict)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.PauliFunding.even_trace_strict, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.PauliFunding.even_trace_strict) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.ParityTraceComparison.Strict.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.ParityTraceComparison.Strict.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ W j => _root_.Matrix.trace (W ^ (2 * j))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.PauliFunding.ParityTraceComparison
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Strict

end
end Reg.D5.S3.Quantum.Matrix.PauliFunding.ParityTraceComparison
