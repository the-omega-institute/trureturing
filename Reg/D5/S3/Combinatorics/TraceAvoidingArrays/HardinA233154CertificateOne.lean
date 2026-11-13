import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154CertificateOne
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Rows
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact readout laws preserve the complete telescopes of the strip identities. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154CertificateOne
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154CertificateOne
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Rows
open LeanInformationAudit
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000

namespace Block
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 729) (fun _ => Fin 16) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ a s => classCount (decode 7 (⟨3*a.val+1, by omega⟩ : Fin 2187)) s) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ a s => actual.readout () a s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ a : Fin 729, rowLegal (decode 7 (⟨3*a.val+1, by omega⟩ : Fin 2187)) → ∀ s : Fin 16,
    R.readout () a s = quotient (classify (decode 7 (⟨3*a.val+1, by omega⟩ : Fin 2187))) s
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hr : rowLegal (decode 7 (⟨3*(0 : Fin 729).val+1, by omega⟩ : Fin 2187)) := by
    decide +kernel
  have hb := h 0 hr 0
  have ha := row_counts 0 hr 0
  change actual.readout () 0 0 + 1 = _ at hb
  change actual.readout () 0 0 = _ at ha
  have hc := hb.trans ha.symm
  exact (by omega : ∀ z : ℤ, z + 1 ≠ z) _ hc
def family : Registration arena (type_of% @row_counts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@row_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 2, ?_⟩
    have hr : rowLegal (decode 7 (⟨3*(0 : Fin 729).val+1, by omega⟩ : Fin 2187)) := by
      decide +kernel
    have h0 := row_counts 0 hr 0
    have h1 := row_counts 0 hr 2
    change actual.readout () 0 0 = _ at h0
    change actual.readout () 0 2 = _ at h1
    rw [h0, h1]
    change (5 : ℤ) ≠ 3
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@row_counts) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154CertificateOne.Block.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154CertificateOne.Block.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a s => classCount (decode 7 (⟨3*a.val+1, by omega⟩ : Fin 2187)) s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154CertificateOne
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Block
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154CertificateOne
