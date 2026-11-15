import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact readout laws preserve the complete telescopes of the strip identities. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Rows
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Rows
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000
namespace Equality
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Equiv.Perm (Fin 3))
    (fun _ => Row 6) (fun _ => Fin 122)
def actual : Realization signature :=
  realize signature (fun _ e r => classify (relabel e r)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ (e : Equiv.Perm (Fin 3)) (r : Row 6), R.readout () e r = classify r) ∧
    (∀ r : Row 6, ∃ e : Equiv.Perm (Fin 3), relabel e r = representatives (classify r))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.1 (Equiv.refl _) (fun _ => 0)
  change (1 : Fin 122) = 0 at hb
  exact (by decide : (1 : Fin 122) ≠ 0) hb
def family : Registration arena (type_of% @equality_classes) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@equality_classes, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨Equiv.refl _, (fun _ => 0), ![0, 0, 0, 0, 0, 1], ?_⟩
    change (0 : Fin 122) ≠ 1
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@equality_classes) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Rows.Equality.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Rows.Equality.family
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
    (fun _ e r => classify (relabel e r)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Rows
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Equality
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Rows
