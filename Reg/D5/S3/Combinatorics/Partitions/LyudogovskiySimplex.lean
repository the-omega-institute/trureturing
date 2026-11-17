import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.Combinatorics.Partitions.LyudogovskiyTransfers
import D5.S3.Combinatorics.Partitions.LyudogovskiySimplex

/-! Source-bound audits retain the complete transfer and whole-question laws. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex

namespace Threshold

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ n => maxDimension n) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ n => maxDimension n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ r : ℕ, threshold r = triangular r + 1 ∧
      IsLeast {n : ℕ | 0 < n ∧ (layer r n).Nonempty} (triangular r + 1)) ∧
    (∀ n : ℕ, 0 < n → R.readout () () n =
      ((Finset.range (n + 1)).filter (fun r => triangular r + 1 ≤ n)).sup id)

private theorem source_bridge : (type_of% threshold_result) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have good := threshold_result.2 1 (by decide)
  have bad := h.2 1 (by decide)
  change maxDimension 1 + 1 = _ at bad
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 1, 2, ?_⟩
  change maxDimension 1 ≠ maxDimension 2
  have h1 : maxDimension 1 = 0 := (threshold_result.2 1 (by decide)).trans (by decide)
  have h2 : maxDimension 2 = 1 := (threshold_result.2 2 (by decide)).trans (by decide)
  omega

def familyRegistration : Registration arena (type_of% threshold_result) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp threshold_result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    threshold_result (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.threshold_result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.Threshold.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
    definition := some {
      owner := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
      name := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.ThresholdClaim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Threshold

namespace FirstOccurrence

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (n : ℕ) → Finset (Nat.Partition n)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ r => firstFamily r) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : ℕ, 2 ≤ r →
    layer r (threshold r) = R.readout () () r (threshold r) ∧
    layer r (triangular r + 1) = R.readout () () r (triangular r + 1) ∧
    (R.readout () () r (threshold r)).card = r + 1

private theorem source_bridge : (type_of% first_occurrence_result) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 2 (by decide)).2.2
  change (∅ : Finset (Nat.Partition (threshold 2))).card = 2 + 1 at bad
  simp at bad

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 2, ?_⟩
  change firstFamily 0 ≠ firstFamily 2
  intro he
  have ht := (threshold_result.1 2).1
  norm_num [triangular] at ht
  have hz : firstFamily 0 (threshold 2) = ∅ := by
    rw [ht]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hc := (Finset.mem_filter.mp hp).2.2
    simp only [staircase, Finset.range_zero, Finset.product_eq_sprod, Finset.empty_product,
      Finset.filter_empty, Finset.sdiff_empty] at hc
    change (YoungDiagram.ofPartition p).card = 1 at hc
    rw [YoungDiagram.card_ofPartition] at hc
    omega
  have hh := congrArg (fun f : (n : ℕ) → Finset (Nat.Partition n) =>
    (f (threshold 2)).card) he
  have hc := (first_occurrence_result 2 (by decide)).2.2
  rw [hz, Finset.card_empty, hc] at hh
  omega

def familyRegistration : Registration arena (type_of% first_occurrence_result) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp first_occurrence_result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    first_occurrence_result (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.first_occurrence_result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.FirstOccurrence.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
    definition := some {
      owner := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
      name := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.FirstOccurrenceClaim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "arg", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end FirstOccurrence

end Reg.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
