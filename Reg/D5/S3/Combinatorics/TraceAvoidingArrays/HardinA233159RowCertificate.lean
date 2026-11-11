import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159RowCertificate
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact readout laws preserve the complete telescopes of the strip identities. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159RowCertificate
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159RowCertificate
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Rows
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000
namespace Certificate
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 122) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ s => weights s) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ s => actual.readout () () s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ r : Row 6, ∀ s : Fin 122,
      (∑ c : Row 6, if columnCompatible r c ∧ classify c = s then (1 : ℤ) else 0) =
        quotient (classify r) s) ∧
    (∀ s : Fin 122, (∑ c : Row 6, if classify c = s then (1 : ℤ) else 0) =
      R.readout () () s) ∧
    (∀ (v : Fin 122 → ℤ) (i : Fin 122),
      quotient.mulVec v i = ((successors i).map v).sum)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2.1 0
  have ha := quotient_certificate.2.1 0
  change _ = actual.readout () () 0 + 1 at hb
  change _ = actual.readout () () 0 at ha
  have hc := ha.symm.trans hb
  exact (by omega : ∀ z : ℤ, z ≠ z + 1) _ hc

def family : Registration arena (type_of% @quotient_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quotient_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (3 : ℤ) ≠ 6
    omega


def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@quotient_certificate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159RowCertificate.Certificate.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159RowCertificate.Certificate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => weights s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159RowCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Certificate

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159RowCertificate
