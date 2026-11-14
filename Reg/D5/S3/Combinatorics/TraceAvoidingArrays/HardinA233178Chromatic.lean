import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Chromatic
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Chromatic
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Chromatic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Column → ℤ) (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ w n => dotProduct w (v n)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ w n => actual.readout () w n + if n = 11 then 1 else 0)
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : Column → ℤ) (n : ℕ), R.readout () w (n+11) =
      6 * R.readout () w (n+10) + 31 * R.readout () w (n+9) -
      97 * R.readout () w (n+8) - 163 * R.readout () w (n+7) +
      417 * R.readout () w (n+6) + 93 * R.readout () w (n+5) -
      514 * R.readout () w (n+4) + 192 * R.readout () w (n+3) +
      72 * R.readout () w (n+2) - 36 * R.readout () w (n+1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := result (fun _ => 0) 0
  have hb := h (fun _ => 0) 0
  norm_num [rejected, actual, realize, dotProduct] at hb
set_option maxRecDepth 30000 in
private theorem actual_dependence :
    actual.readout () (fun p => if p = 0 then 1 else 0) 0 ≠
    actual.readout () (fun p => if p = 0 then 1 else 0) 1 := by
  change dotProduct (fun p : Column => if p = 0 then (1 : ℤ) else 0) (v 0) ≠
    dotProduct (fun p : Column => if p = 0 then (1 : ℤ) else 0) (v 1)
  simp only [dotProduct, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  decide +kernel

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(fun p => if p = 0 then 1 else 0), 0, 1, actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Chromatic.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Chromatic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ w n => dotProduct w (v n)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Chromatic
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Chromatic
