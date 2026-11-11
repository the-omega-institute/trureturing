import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRep
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound four-slot registrations with literal unknown residuals. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRep
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRep
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer (Col cls representatives)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

namespace RepresentativeRows
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 14)
    (fun _ => Fin 14) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ i s => Q i s) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ i s => Q i s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ i s : Fin 14,
      (∑ c : Col, if compatible (representatives i) c ∧ cls c = s then (1 : ℤ) else 0) =
        R.readout () i s
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := representative_rows 0 0
  have hb := h 0 0
  change (∑ c : Col, if compatible (representatives 0) c ∧
    cls c = 0 then (1 : ℤ) else 0) = Q 0 0 + 1 at hb
  linarith only [ha, hb]
def family : Registration arena (type_of% @representative_rows) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@representative_rows, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 4, ?_⟩
    change (2 : ℤ) ≠ 0
    norm_num
def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@representative_rows) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRep.RepresentativeRows.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRep.RepresentativeRows.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ i s => Q i s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRep
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end RepresentativeRows

namespace QuotientRows
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Col
    (fun _ => Fin 14) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ b s => Q (cls b) s) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ b s => Q (cls b) s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (b : Col) (s : Fin 14),
      (∑ c : Col, if compatible b c ∧ cls c = s then (1 : ℤ) else 0) =
        R.readout () b s
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := quotient_rows (0, 0, 0, 0) 0
  have hb := h (0, 0, 0, 0) 0
  change (∑ c : Col, if compatible (0, 0, 0, 0) c ∧
    cls c = 0 then (1 : ℤ) else 0) = Q (cls (0, 0, 0, 0)) 0 + 1 at hb
  linarith only [ha, hb]
def family : Registration arena (type_of% @quotient_rows) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quotient_rows, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(0, 0, 0, 0), 0, 4, ?_⟩
    change (2 : ℤ) ≠ 0
    norm_num
def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@quotient_rows) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRep.QuotientRows.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRep.QuotientRows.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ b s => Q (cls b) s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRep
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end QuotientRows

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRep
