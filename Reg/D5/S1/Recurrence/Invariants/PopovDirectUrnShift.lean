import D5.S1.Recurrence.Invariants.PopovDirectUrnShift
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
namespace Reg.D5.S1.Recurrence.Invariants.PopovDirectUrnShift

open _root_.PopovUrnShift
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ) (fun _ => ℕ) (fun _ => ℕ)

abbrev actual : Realization signature :=
  realize signature (fun _ p k => S p.1 (p.2 + p.1) k) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ}, 0 < m → ∀ n k : ℕ,
    R.readout () ⟨m, n⟩ k =
      ∑ j ∈ Finset.range (n + 1), n.choose j * m ^ (n - j) * S m j ((k : ℤ) - m)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have eq := h (m := 1) (by decide) 0 1
  change 0 = ∑ j ∈ Finset.range (0 + 1), (0 : ℕ).choose j * 1 ^ (0 - j) *
    S 1 j ((1 : ℤ) - 1) at eq
  have hne : ¬ (0 = ∑ j ∈ Finset.range (0 + 1), (0 : ℕ).choose j * 1 ^ (0 - j) *
    S 1 j ((1 : ℤ) - 1)) := by decide
  exact hne eq

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  change S 1 1 0 ≠ S 1 1 1
  decide

def family : Registration arena (type_of% (@shift_7_2)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨shift_7_2, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@shift_7_2) (Realization signature) Type Unit where
  unitName := `PopovUrnShift.shift_7_2.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Invariants.PopovDirectUrnShift.family
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
    (fun _ p k => S p.1 (p.2 + p.1) k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Invariants.PopovDirectUrnShift
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Recurrence.Invariants.PopovDirectUrnShift
