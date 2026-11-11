import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Column
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Rows
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact readout laws preserve the complete telescopes of the strip identities. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Column
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Column
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Rows
open LeanInformationAudit
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] T7
namespace Certificate
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Row 7) (fun _ => Fin 16) (fun _ => ℤ)
def actual : Realization signature := by
  classical
  exact realize signature (fun _ r s =>
    ∑ c : Row 7, if rowLegal c ∧ compatible r c ∧ classify c = s then (1 : ℤ) else 0)
      (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ r s => actual.readout () r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ r : Row 7, rowLegal r → ∀ s : Fin 16,
      R.readout () r s = quotient (classify r) s) ∧
    (∀ s : Fin 16, (∑ c : Row 7, if rowLegal c ∧ classify c = s then (1 : ℤ) else 0) =
      weights s) ∧
    (quotient ^ (1+4)).mulVec (1 : Fin 16 → ℤ) =
      ∑ j : Fin 4, (![-810, 972, -351, 42] : Fin 4 → ℤ) j •
        (quotient ^ (1+j.val)).mulVec (1 : Fin 16 → ℤ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hr : rowLegal (fun _ : Fin 7 => (0 : Fin 3)) := by decide +kernel
  have hb := h.1 (fun _ => 0) hr 0
  have ha := finite_certificate.1 (fun _ => 0) hr 0
  change actual.readout () (fun _ => 0) 0 + 1 = _ at hb
  change actual.readout () (fun _ => 0) 0 = _ at ha
  have hc := hb.trans ha.symm
  exact (by omega : ∀ z : ℤ, z + 1 ≠ z) _ hc
def family : Registration arena (type_of% @finite_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(fun _ => 0), 0, 2, ?_⟩
    have hr : rowLegal (fun _ : Fin 7 => (0 : Fin 3)) := by decide +kernel
    have h0 := finite_certificate.1 (fun _ => 0) hr 0
    have h1 := finite_certificate.1 (fun _ => 0) hr 2
    change actual.readout () (fun _ => 0) 0 = _ at h0
    change actual.readout () (fun _ => 0) 2 = _ at h1
    rw [h0, h1]
    change (5 : ℤ) ≠ 3
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Column.Certificate.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Column.Certificate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Column
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
  realize signature (fun _ _ n => (T7 n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (T7 n : ℤ) + if n = 5 then 1 else 0)
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+5) =
    42 * R.readout () () (n+4) - 351 * R.readout () () (n+3) +
      972 * R.readout () () (n+2) - 810 * R.readout () () (n+1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  have ha := result 0
  change (T7 5 : ℤ) + 1 = _ at hb
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
    have h1 : T7 1 = 192 := by unfold T7; decide +kernel
    have h2 := count_transfer 7 16 classify quotient weights
      finite_certificate.1 finite_certificate.2.1 0
    change (T7 1 : ℤ) ≠ (T7 2 : ℤ)
    change (T7 2 : ℤ) = _ at h2
    have hv : dotProduct weights
        ((quotient ^ 1).mulVec (1 : Fin 16 → ℤ)) = 5832 := by decide +kernel
    change (T7 2 : ℤ) = dotProduct weights
      ((quotient ^ 1).mulVec (1 : Fin 16 → ℤ)) at h2
    rw [hv] at h2
    exact_mod_cast (by omega : T7 1 ≠ T7 2)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Column.Recurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Column.Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Column
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
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Column
