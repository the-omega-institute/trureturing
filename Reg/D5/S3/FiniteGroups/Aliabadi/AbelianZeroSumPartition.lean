import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.Aliabadi.AbelianZeroSumPartition
import Reg.Support.UniverseSingleReadout
import Mathlib.Algebra.Group.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.Aliabadi.AbelianZeroSumPartition
open scoped BigOperators Classical

noncomputable section
universe u v

namespace Reg.D5.S3.FiniteGroups.Aliabadi.AbelianZeroSumPartition

structure LabelData where
  G : Type u
  groupG : AddCommGroup G
  finiteG : Finite G
  I : Type v
  a : I → G

namespace Extraction

abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature
  LabelData.{u,v} (fun p => Finset p.I) (fun _ => Prop)

def actual : Realization signature.{u,v} := realize signature
  (fun _ p t => by letI := p.groupG; exact ∑ i ∈ t, p.a i = 0)
  (fun e => nomatch e)

def rejected : Realization signature.{u,v} := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ (G : Type u) [gg : AddCommGroup G] [fg : Finite G]
    (I : Type v) (a : I → G) (s : Finset I),
    2 * Nat.card G - 1 ≤ s.card →
      ∃ t ⊆ s, t.card = Nat.card G ∧ r.readout () ⟨G,gg,fg,I,a⟩ t

private theorem bridge :
    (type_of% (@exists_zero_sum_card.{u,v})) ↔ arena.{u,v}.Law actual := by
  constructor
  · intro h G gg fg I a s hs
    exact h a s hs
  · intro h G gg fg I a s hs
    exact h G I a s hs

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨t, _, _, hf⟩ := h (ULift.{u} PUnit) (ULift.{v} PUnit)
    (fun _ => 0) {⟨PUnit.unit⟩} (by simp [Nat.card_eq_fintype_card])
  exact hf

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  let p : LabelData.{u,v} := ⟨ULift.{u} (ZMod 2), inferInstance, inferInstance,
    ULift.{v} PUnit, fun _ => 1⟩
  refine ⟨p, ∅, {⟨PUnit.unit⟩}, ?_⟩
  change (∑ j ∈ (∅ : Finset (ULift.{v} PUnit)), (1 : ULift.{u} (ZMod 2)) = 0) ≠
    (∑ j ∈ ({⟨PUnit.unit⟩} : Finset (ULift.{v} PUnit)), (1 : ULift.{u} (ZMod 2)) = 0)
  simp

def family : Registration arena.{u,v} (type_of% (@exists_zero_sum_card.{u,v})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @exists_zero_sum_card.{u,v}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_zero_sum_card.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.Aliabadi.AbelianZeroSumPartition.exists_zero_sum_card.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.Aliabadi.AbelianZeroSumPartition.Extraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.Aliabadi.AbelianZeroSumPartition
    definition := none
    coordinates := #[0,1,2,3,4]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","arg","body","arg","arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Extraction

structure PartitionData extends LabelData.{u,v} where
  m : ℕ

namespace Partition

abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature
  PartitionData.{u,v} (fun p => Fin p.m → Finset p.I) (fun _ => Prop)

def actual : Realization signature.{u,v} := realize signature
  (fun _ p B => by letI := p.groupG; exact ∀ j, ∑ i ∈ B j, p.a i = 0)
  (fun e => nomatch e)

def rejected : Realization signature.{u,v} := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ (G : Type u) [gg : AddCommGroup G] [fg : Finite G]
    (I : Type v) (a : I → G) (s : Finset I) (m : ℕ),
    s.card = m * Nat.card G → (∑ i ∈ s, a i = 0) →
      ∃ B : Fin m → Finset I,
        (∀ j, B j ⊆ s) ∧ Pairwise (fun j k => Disjoint (B j) (B k)) ∧
        (Finset.univ.biUnion B = s) ∧ (∀ j, (B j).card = Nat.card G) ∧
        r.readout () ⟨⟨G,gg,fg,I,a⟩,m⟩ B

private theorem bridge :
    (type_of% (@exists_zero_sum_partition.{u,v})) ↔ arena.{u,v}.Law actual := by
  constructor
  · intro h G gg fg I a s m hc hz
    exact h a s m hc hz
  · intro h G gg fg I a s m hc hz
    exact h G I a s m hc hz

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨B, _, _, _, _, hf⟩ := h (ULift.{u} PUnit) (ULift.{v} PUnit)
    (fun _ => 0) {⟨PUnit.unit⟩} 1 (by simp [Nat.card_eq_fintype_card]) (by simp)
  exact hf

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  let p : PartitionData.{u,v} := ⟨⟨ULift.{u} (ZMod 2), inferInstance, inferInstance,
    ULift.{v} PUnit, fun _ => 1⟩, 1⟩
  refine ⟨p, (fun _ => ∅), (fun _ => {⟨PUnit.unit⟩}), ?_⟩
  change (∀ j : Fin 1, ∑ i ∈ (∅ : Finset (ULift.{v} PUnit)),
    (1 : ULift.{u} (ZMod 2)) = 0) ≠
    (∀ j : Fin 1, ∑ i ∈ ({⟨PUnit.unit⟩} : Finset (ULift.{v} PUnit)),
    (1 : ULift.{u} (ZMod 2)) = 0)
  simp

def family : Registration arena.{u,v} (type_of% (@exists_zero_sum_partition.{u,v})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @exists_zero_sum_partition.{u,v}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_zero_sum_partition.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.Aliabadi.AbelianZeroSumPartition.exists_zero_sum_partition.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.Aliabadi.AbelianZeroSumPartition.Partition.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.Aliabadi.AbelianZeroSumPartition
    definition := none
    coordinates := #[0,1,2,3,4,6]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","arg","body","arg","arg","arg","arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Partition
end Reg.D5.S3.FiniteGroups.Aliabadi.AbelianZeroSumPartition
