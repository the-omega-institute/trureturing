import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Normalization
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Normalization
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Normalization
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge (rowWeight)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun k => Fin k → Fin 3) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ k q => 4 * (rowWeight (false, false) q +
    rowWeight (false, false) (fun j => swap (q j)))) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ k q => actual.readout () k q + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (q : Fin k → Fin 3), R.readout () k q =
    2^k * (1 + absent q 1 + absent q 2 + 5 * (absent q 1 * absent q 2))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0 (fun j => Fin.elim0 j)
  norm_num [rejected, actual, realize, rowWeight, absent] at h0
def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
    norm_num [actual, realize, rowWeight,
      _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge.labelWeight,
      _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge.labelAdvance, swap, Equiv.swap_apply_def]
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Normalization.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Normalization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k q => 4 * (rowWeight (false, false) q +
    rowWeight (false, false) (fun j => swap (q j)))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Normalization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Normalization
