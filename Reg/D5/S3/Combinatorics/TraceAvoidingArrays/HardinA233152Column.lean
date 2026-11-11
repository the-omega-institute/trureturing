import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233152Column
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact readout laws preserve the complete telescopes of the strip identities. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233152Column
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233152Column
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
attribute [local irreducible] T5
namespace Certificate
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Row 5) (fun _ => Fin 3) (fun _ => ℤ)
def actual : Realization signature := by
  classical
  exact realize signature (fun _ r s =>
    ∑ c : Row 5, if rowLegal c ∧ compatible r c ∧ classify c = s then (1 : ℤ) else 0)
      (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ r s => actual.readout () r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ r : Row 5, rowLegal r → ∀ s : Fin 3,
      R.readout () r s = quotient (classify r) s) ∧
    (∀ s : Fin 3, (∑ c : Row 5, if rowLegal c ∧ classify c = s then (1 : ℤ) else 0) =
      weights s) ∧
    (quotient ^ (1+2)).mulVec (1 : Fin 3 → ℤ) =
      ∑ j : Fin 2, (![-18, 15] : Fin 2 → ℤ) j •
        (quotient ^ (1+j.val)).mulVec (1 : Fin 3 → ℤ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hr : rowLegal (fun _ : Fin 5 => (0 : Fin 3)) := by decide +kernel
  have hb := h.1 (fun _ => 0) hr 0
  have ha := finite_certificate.1 (fun _ => 0) hr 0
  change actual.readout () (fun _ => 0) 0 + 1 = _ at hb
  change actual.readout () (fun _ => 0) 0 = _ at ha
  omega
def family : Registration arena (type_of% @finite_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(fun _ => 0), 0, 1, ?_⟩
    have hr : rowLegal (fun _ : Fin 5 => (0 : Fin 3)) := by decide +kernel
    have h0 := finite_certificate.1 (fun _ => 0) hr 0
    have h1 := finite_certificate.1 (fun _ => 0) hr 1
    change actual.readout () (fun _ => 0) 0 = _ at h0
    change actual.readout () (fun _ => 0) 1 = _ at h1
    rw [h0, h1]
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233152Column.Certificate.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233152Column.Certificate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (by classical; exact realize signature (fun _ r s => ∑ c : Row 5, if rowLegal c ∧ compatible r c ∧ classify c = s then (1 : ℤ) else 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233152Column
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Certificate

namespace Recurrence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (T5 n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (T5 n : ℤ) + if n = 3 then 1 else 0)
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+3) =
    15 * R.readout () () (n+2) - 18 * R.readout () () (n+1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  have ha := result 0
  change (T5 3 : ℤ) + 1 = _ at hb
  simp only [rejected, realize] at hb
  norm_num at hb ha
  omega
def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    have h1 : T5 1 = 48 := by unfold T5; decide +kernel
    have h2 := count_transfer 5 3 classify quotient weights
      finite_certificate.1 finite_certificate.2.1 0
    change (T5 1 : ℤ) ≠ (T5 2 : ℤ)
    change (T5 2 : ℤ) = _ at h2
    norm_num [quotient, weights, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h2
    exact_mod_cast (by omega : T5 1 ≠ T5 2)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233152Column.Recurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233152Column.Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (T5 n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233152Column
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Recurrence
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233152Column
