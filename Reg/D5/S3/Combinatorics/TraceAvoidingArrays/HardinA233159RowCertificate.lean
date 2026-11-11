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
  _root_.Reg.Support.SingleDependentReadout.signature (Row 6) (fun _ => Fin 122) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ r s =>
    ∑ c : Row 6, if columnCompatible r c ∧ classify c = s then (1 : ℤ) else 0)
      (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ r s => actual.readout () r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ r : Row 6, ∀ s : Fin 122,
      R.readout () r s = quotient (classify r) s) ∧
    (∀ s : Fin 122, (∑ c : Row 6, if classify c = s then (1 : ℤ) else 0) =
      weights s) ∧
    (∀ (v : Fin 122 → ℤ) (i : Fin 122),
      quotient.mulVec v i = ((successors i).map v).sum)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.1 (fun _ => 0) 0
  have ha := quotient_certificate.1 (fun _ => 0) 0
  change actual.readout () (fun _ => 0) 0 + 1 = _ at hb
  change actual.readout () (fun _ => 0) 0 = _ at ha
  have hc := hb.trans ha.symm
  exact (by omega : ∀ z : ℤ, z + 1 ≠ z) _ hc
def family : Registration arena (type_of% @quotient_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quotient_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(fun _ => 0), 0, 4, ?_⟩
    have h0 := quotient_certificate.1 (fun _ => 0) 0
    have h1 := quotient_certificate.1 (fun _ => 0) 4
    change actual.readout () (fun _ => 0) 0 = _ at h0
    change actual.readout () (fun _ => 0) 4 = _ at h1
    rw [h0, h1]
    change (2 : ℤ) ≠ 0
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
  readout := some (realize signature (fun _ r s =>
      ∑ c : Row 6, if columnCompatible r c ∧ classify c = s then (1 : ℤ) else 0)
        (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159RowCertificate
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
end Certificate

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159RowCertificate
