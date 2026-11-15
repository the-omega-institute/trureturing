import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRecurrence
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferBase
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound four-slot registrations with literal unknown residuals. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRecurrence
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRecurrence
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
attribute [local irreducible] L

namespace Recurrence
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (L n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (L n : ℤ) + if n = 9 then 1 else 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+9) + 6 =
      10 * (R.readout () () (n+8) + 6) - 24 * (R.readout () () (n+7) + 6) +
        21 * (R.readout () () (n+6) + 6) - 6 * (R.readout () () (n+5) + 6)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := recurrence 0
  have hb := h 0
  change ((L 9 : ℤ) + 1) + 6 =
    10 * ((L 8 : ℤ) + 0 + 6) - 24 * ((L 7 : ℤ) + 0 + 6) +
      21 * ((L 6 : ℤ) + 0 + 6) - 6 * ((L 5 : ℤ) + 0 + 6) at hb
  linarith only [ha, hb]
def family : Registration arena (type_of% @recurrence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@recurrence, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 2, 3, ?_⟩
    have h2 : (L 2 : ℤ) = 384 :=
      _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferBase.initial_values 0
    have h3 : (L 3 : ℤ) = 2592 :=
      _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferBase.initial_values 1
    change (L 2 : ℤ) ≠ (L 3 : ℤ)
    omega
def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@recurrence) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRecurrence.Recurrence.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRecurrence.Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (L n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRecurrence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Recurrence

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRecurrence
