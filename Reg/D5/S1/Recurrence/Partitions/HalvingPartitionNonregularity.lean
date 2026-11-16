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

namespace Ring
universe u

structure RingParams where
  Carrier : Type u
  ring : CommRing Carrier
  nontrivial : Nontrivial Carrier

abbrev signature : Signature where
  Params := RingParams.{u}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.Carrier
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u} :=
  realize signature (fun _ p n => letI := p.ring; (count n : p.Carrier))
    (fun e => nomatch e)

abbrev rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.ring; (0 : p.Carrier))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law W := ∀ (R : Type u) (hR : CommRing R) (hN : Nontrivial R),
    letI := hR
    ¬ _root_.D5.S1.Recurrence.BinaryDecimation.MatrixFamily
      (W.readout () ⟨R, hR, hN⟩)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hn := h (ULift.{u} ℤ) inferInstance inferInstance
  apply hn
  refine ⟨1, by decide, fun _ _ => 0, 1, 1, ?_, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    simp only [Matrix.one_mulVec]
  · intro n
    simp only [Matrix.one_mulVec]

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  have hex : ∃ x y : ℕ, (count x : ULift.{u} ℤ) ≠ (count y : ULift.{u} ℤ) := by
    by_contra hn
    push_neg at hn
    apply nonregularity_over (ULift.{u} ℤ)
    refine ⟨1, by decide, fun _ _ => (count 0 : ULift.{u} ℤ), 1, 1, ?_, ?_, ?_⟩
    · intro n
      exact hn 0 n
    · intro n
      simp only [Matrix.one_mulVec]
    · intro n
      simp only [Matrix.one_mulVec]
  obtain ⟨x, y, hxy⟩ := hex
  exact ⟨⟨ULift.{u} ℤ, inferInstance, inferInstance⟩, x, y, hxy⟩

def family : Registration arena.{u} (type_of% (@nonregularity_over.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nonregularity_over, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,u+1,0,0,u,0,0}
    (@nonregularity_over.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity.nonregularity_over.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity.Ring.family
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
    (fun _ p n => letI := p.ring; (count n : p.Carrier)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Ring

end Reg.D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
