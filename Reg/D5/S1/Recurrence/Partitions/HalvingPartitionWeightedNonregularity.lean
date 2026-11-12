import D5.S1.Recurrence.Partitions.HalvingPartitionWeightedNonregularity
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
namespace Reg.D5.S1.Recurrence.Partitions.HalvingPartitionWeightedNonregularity
open _root_.D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
open _root_.D5.S1.Recurrence.BinaryDecimation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u

structure Params where
  Carrier : Type u
  ring : CommRing Carrier
  nontrivial : Nontrivial Carrier
  weight : Carrier

abbrev signature : Signature where
  Params := Params.{u}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.Carrier
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u} :=
  realize signature (fun _ p n => letI := p.ring; weightedCount p.weight n)
    (fun e => nomatch e)

abbrev rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.ring; (0 : p.Carrier))
    (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  have hex : ∃ x y : ℕ,
      weightedCount (0 : ULift.{u} ℤ) x ≠ weightedCount (0 : ULift.{u} ℤ) y := by
    by_contra hn
    push_neg at hn
    apply weighted_nonregularity (0 : ULift.{u} ℤ)
    refine ⟨1, by decide, fun _ _ => weightedCount (0 : ULift.{u} ℤ) 0, 1, 1, ?_, ?_, ?_⟩
    · intro n
      exact hn 0 n
    · intro n
      simp only [Matrix.one_mulVec]
    · intro n
      simp only [Matrix.one_mulVec]
  obtain ⟨x, y, hxy⟩ := hex
  exact ⟨⟨ULift.{u} ℤ, inferInstance, inferInstance, 0⟩, x, y, hxy⟩

namespace Binary
abbrev arena : Arena where
  signature := signature.{u}
  Law W := ∀ {R : Type u} [hR : CommRing R] [hN : Nontrivial R] (t : R),
    ¬ MatrixFamily (W.readout () ⟨R, hR, hN, t⟩)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hn := h (0 : ULift.{u} ℤ)
  apply hn
  refine ⟨1, by decide, fun _ _ => 0, 1, 1, ?_, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    simp only [Matrix.one_mulVec]
  · intro n
    simp only [Matrix.one_mulVec]

def family : Registration arena.{u} (type_of% (@weighted_nonregularity.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weighted_nonregularity, rejected, rejected_law⟩
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
    (@weighted_nonregularity.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S1.Recurrence.Partitions.HalvingPartitionWeightedNonregularity.weighted_nonregularity.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Partitions.HalvingPartitionWeightedNonregularity.Binary.family
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
    (fun _ p n => letI := p.ring; weightedCount p.weight n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Partitions.HalvingPartitionWeightedNonregularity
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Binary

namespace PowerBase
abbrev arena : Arena where
  signature := signature.{u}
  Law W := ∀ {R : Type u} [hR : CommRing R] [hN : Nontrivial R]
    (t : R) (h : ℕ) (_hh : 1 ≤ h),
    ¬ BaseFamily (2 ^ h) (W.readout () ⟨R, hR, hN, t⟩)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hn := h (0 : ULift.{u} ℤ) 1 (by decide)
  apply hn
  refine ⟨Unit, inferInstance, fun _ _ => 0, (), fun _ _ _ => 0, ?_, ?_⟩
  · intro n
    rfl
  · intro r i n
    simp

def family : Registration arena.{u} (type_of% (@weighted_powerBase_nonregularity.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weighted_powerBase_nonregularity, rejected, rejected_law⟩
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
    (@weighted_powerBase_nonregularity.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S1.Recurrence.Partitions.HalvingPartitionWeightedNonregularity.weighted_powerBase_nonregularity.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Partitions.HalvingPartitionWeightedNonregularity.PowerBase.family
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
    (fun _ p n => letI := p.ring; weightedCount p.weight n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Partitions.HalvingPartitionWeightedNonregularity
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end PowerBase

end Reg.D5.S1.Recurrence.Partitions.HalvingPartitionWeightedNonregularity
