import D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

noncomputable section

namespace Reg.D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity

open _root_.D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

abbrev actual : Realization signature :=
  realize signature (fun _ _ n => count n) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℕ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (¬ MatrixFamily (fun n => (R.readout () () n : ℤ))) ∧
    (∀ a : ℕ → ℤ, ClosedFamily a ↔ MatrixFamily a) ∧
    (∀ a : ℕ → ℤ, ArbitraryFamily a ↔ MatrixFamily a) ∧
    (¬ ArbitraryFamily (fun n => (count n : ℤ))) ∧
    (∀ n, count n = Fintype.card (HalvingCompositions n)) ∧ count 0 = 1

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have hex : ∃ x y : ℕ, count x ≠ count y := by
    by_contra h
    push_neg at h
    apply result.1
    refine ⟨1, by decide, fun _ _ => (count 0 : ℤ), 1, 1, ?_, ?_, ?_⟩
    · intro n
      exact congrArg Int.ofNat (h 0 n)
    · intro n
      simp only [Matrix.one_mulVec]
    · intro n
      simp only [Matrix.one_mulVec]
  obtain ⟨x, y, hxy⟩ := hex
  exact ⟨(), x, y, hxy⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h.1
  refine ⟨1, by decide, fun _ _ => (0 : ℤ), 1, 1, ?_, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    simp only [Matrix.one_mulVec]
  · intro n
    simp only [Matrix.one_mulVec]

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@result) (Realization signature) Type Unit where
  unitName := `D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity.result.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => count n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "arg", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
