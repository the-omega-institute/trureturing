import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233156Row
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact readout laws preserve the complete telescopes of the strip identities. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233156Row
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233156Row
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000
namespace Certificate
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Row 3) (fun _ => Fin 5) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ r s =>
    ∑ c : Row 3, if columnCompatible r c ∧ classify c = s then (1 : ℤ) else 0)
      (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ r s => actual.readout () r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ r : Row 3, ∀ s : Fin 5,
      R.readout () r s = quotient (classify r) s) ∧
    (∀ s : Fin 5, (∑ c : Row 3, if classify c = s then (1 : ℤ) else 0) =
      weights s) ∧
    (quotient ^ (2+2)).mulVec (1 : Fin 5 → ℤ) =
      ∑ j : Fin 2, (![-2, 5] : Fin 2 → ℤ) j •
        (quotient ^ (2+j.val)).mulVec (1 : Fin 5 → ℤ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.1 (fun _ => 0) 0
  have ha := finite_certificate.1 (fun _ => 0) 0
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
    refine ⟨(fun _ => 0), 0, 4, ?_⟩
    have h0 := finite_certificate.1 (fun _ => 0) 0
    have h1 := finite_certificate.1 (fun _ => 0) 4
    change actual.readout () (fun _ => 0) 0 = _ at h0
    change actual.readout () (fun _ => 0) 4 = _ at h1
    rw [h0, h1]
    change (2 : ℤ) ≠ 0
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233156Row.Certificate.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233156Row.Certificate.family
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
      ∑ c : Row 3, if columnCompatible r c ∧ classify c = s then (1 : ℤ) else 0)
        (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233156Row
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

namespace Recurrence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (U3 n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (U3 n : ℤ) + if n = 5 then 1 else 0)
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+5) = 5 * R.readout () () (n+4) - 2 * R.readout () () (n+3)
private theorem rejected_law : ¬ arena.Law rejected := by
  have obstruction (u : ℕ → ℤ)
      (hu : ∀ n, u (n+5) = 5 * u (n+4) - 2 * u (n+3))
      (hb : ∀ n, (u (n+5) + if n+5 = 5 then 1 else 0) = 5 * (u (n+4) + if n+4 = 5 then 1 else 0) - 2 * (u (n+3) + if n+3 = 5 then 1 else 0)) : False := by
    have h0 := hu 0
    have h1 := hb 0
    norm_num at h0 h1
    linarith only [h0, h1]
  exact obstruction (fun n => (U3 n : ℤ)) result
def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    have h0 : U3 0 = 1 := by decide +kernel
    have h1 : U3 1 = 27 := by decide +kernel
    change (U3 0 : ℤ) ≠ (U3 1 : ℤ)
    rw [h0, h1]
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233156Row.Recurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233156Row.Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (U3 n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233156Row
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Recurrence
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233156Row
