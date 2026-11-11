import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Row
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact readout laws preserve the complete telescopes of the strip identities. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Row
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Row
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
    (quotient ^ (6+9)).mulVec (1 : Fin 122 → ℤ) =
      ∑ j : Fin 9, (![-4128, 17216, -27636, 21056, -6705, -573, 1038, -283, 30] : Fin 9 → ℤ) j •
        (quotient ^ (6+j.val)).mulVec (1 : Fin 122 → ℤ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2.1 0
  have ha := finite_certificate.2.1 0
  change _ = actual.readout () () 0 + 1 at hb
  change _ = actual.readout () () 0 at ha
  have hc := ha.symm.trans hb
  exact (by omega : ∀ z : ℤ, z ≠ z + 1) _ hc

def family : Registration arena (type_of% @finite_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (3 : ℤ) ≠ 6
    omega


def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Row.Certificate.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Row.Certificate.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Row
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

namespace Recurrence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (U6 n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (U6 n : ℤ) + if n = 16 then 1 else 0)
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+16) = 30 * R.readout () () (n+15) - 283 * R.readout () () (n+14) + 1038 * R.readout () () (n+13) - 573 * R.readout () () (n+12) - 6705 * R.readout () () (n+11) + 21056 * R.readout () () (n+10) - 27636 * R.readout () () (n+9) + 17216 * R.readout () () (n+8) - 4128 * R.readout () () (n+7)
private theorem rejected_law : ¬ arena.Law rejected := by
  have obstruction (u : ℕ → ℤ)
      (hu : ∀ n, u (n+16) = 30 * u (n+15) - 283 * u (n+14) + 1038 * u (n+13) - 573 * u (n+12) - 6705 * u (n+11) + 21056 * u (n+10) - 27636 * u (n+9) + 17216 * u (n+8) - 4128 * u (n+7))
      (hb : ∀ n, (u (n+16) + if n+16 = 16 then 1 else 0) = 30 * (u (n+15) + if n+15 = 16 then 1 else 0) - 283 * (u (n+14) + if n+14 = 16 then 1 else 0) + 1038 * (u (n+13) + if n+13 = 16 then 1 else 0) - 573 * (u (n+12) + if n+12 = 16 then 1 else 0) - 6705 * (u (n+11) + if n+11 = 16 then 1 else 0) + 21056 * (u (n+10) + if n+10 = 16 then 1 else 0) - 27636 * (u (n+9) + if n+9 = 16 then 1 else 0) + 17216 * (u (n+8) + if n+8 = 16 then 1 else 0) - 4128 * (u (n+7) + if n+7 = 16 then 1 else 0)) : False := by
    have h0 := hu 0
    have h1 := hb 0
    norm_num at h0 h1
    linarith only [h0, h1]
  exact obstruction (fun n => (U6 n : ℤ)) result
def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    have h0 : U6 0 = 1 := by decide +kernel
    have h1 : U6 1 = 729 := by decide +kernel
    change (U6 0 : ℤ) ≠ (U6 1 : ℤ)
    rw [h0, h1]
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Row.Recurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Row.Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (U6 n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Row
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
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233159Row
