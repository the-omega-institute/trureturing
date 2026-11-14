import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferBase
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound four-slot registrations with literal unknown residuals. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferBase
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferBase
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
attribute [local irreducible] L

namespace InitialValues
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (L n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (L n : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : Fin 8, R.readout () () (k.val+2) =
      ![384, 2592, 17496, 121176, 842616, 5871528, 40931568, 285366888] k
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha : (L 2 : ℤ) = 384 := initial_values 0
  have hb := h 0
  change (L 2 : ℤ) + 1 = 384 at hb
  linarith only [ha, hb]
def family : Registration arena (type_of% @initial_values) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@initial_values, rejected, rejected_law⟩
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
    (@initial_values) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferBase.InitialValues.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferBase.InitialValues.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferBase
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
end InitialValues

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferBase
