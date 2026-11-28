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

namespace CliqueLeLocal

abbrev signature : Signature where
  Params := ℕ
  State n := Finset (Nat.Partition n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ C => C.card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ n _ => maxDimension n + 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (C : Finset (Nat.Partition n)),
    (graph n).IsClique (C : Set _) → ∀ (p : Nat.Partition n), p ∈ C →
    R.readout () n C - 1 ≤ localDimension p

private theorem source_bridge : (type_of% (@clique_le_local)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let p := Nat.Partition.indiscrete 1
  have tooLarge := law {p} (by simp) p (Finset.mem_singleton_self p)
  change maxDimension 1 + 2 - 1 ≤ localDimension p at tooLarge
  have upper : localDimension p ≤ maxDimension 1 := Finset.le_sup (Finset.mem_univ p)
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨1, ∅, {Nat.Partition.indiscrete 1}, ?_⟩
  change (∅ : Finset (Nat.Partition 1)).card ≠ ({Nat.Partition.indiscrete 1} : Finset _).card
  simp

def familyRegistration : Registration arena (type_of% (@clique_le_local)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@clique_le_local), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@clique_le_local) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.clique_le_local.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.CliqueLeLocal.familyRegistration
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
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end CliqueLeLocal

namespace CliqueStarOrTop

abbrev signature : Signature where
  Params := ℕ
  State n := Finset (Nat.Partition n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Set (Nat.Partition n)
  Anchor := Empty
  finiteAnchor := inferInstance


def actual : Realization signature :=
  realize signature (fun _ n C => (C : Set (Nat.Partition n))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 0 < n → ∀ C : Finset (Nat.Partition n),
    (graph n).IsClique (R.readout () n C) → 2 ≤ C.card →
    (∃ X : YoungDiagram, X.card = n - 1 ∧
      ∀ p ∈ C, X ≤ YoungDiagram.ofPartition p) ∨
    (∃ U : YoungDiagram, U.card = n + 1 ∧
      ∀ p ∈ C, YoungDiagram.ofPartition p ≤ U)

private theorem source_bridge : (type_of% (@clique_star_or_top)) ↔ arena.Law actual := Iff.rfl

private def row : YoungDiagram := YoungDiagram.ofRowLens [4] (by decide)
private def column : YoungDiagram := YoungDiagram.ofRowLens [1, 1, 1, 1] (by decide)

private def p : Nat.Partition 4 := row.toPartition (by decide)
private def q : Nat.Partition 4 := column.toPartition (by decide)

private theorem p_diagram : YoungDiagram.ofPartition p = row := YoungDiagram.ofPartition_toPartition _
private theorem q_diagram : YoungDiagram.ofPartition q = column := YoungDiagram.ofPartition_toPartition _

private theorem distinct : p ≠ q := by
  intro hpq
  have h : row = column := p_diagram.symm.trans ((congrArg YoungDiagram.ofPartition hpq).trans q_diagram)
  exact (by decide : row.cells ≠ column.cells) (congrArg YoungDiagram.cells h)

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro law
  let C : Finset (Nat.Partition 4) := {p, q}
  have hp : p ∈ C := by simp [C]
  have hq : q ∈ C := by simp [C]
  have size : 2 ≤ C.card := by simp [C, distinct]
  rcases law (n := 4) (by decide) C (by change (graph 4).IsClique ∅; simp) size with ⟨X, hX, hsub⟩ | ⟨U, hU, hsuper⟩
  · have hp' := hsub p hp
    have hq' := hsub q hq
    rw [p_diagram] at hp'
    rw [q_diagram] at hq'
    have bound := Finset.card_le_card
      (show X.cells ⊆ (row ⊓ column).cells from le_inf hp' hq')
    change X.card ≤ (row ⊓ column).card at bound
    have actualCard : (row ⊓ column).card = 1 := by decide
    omega
  · have hp' := hsuper p hp
    have hq' := hsuper q hq
    rw [p_diagram] at hp'
    rw [q_diagram] at hq'
    have bound := Finset.card_le_card
      (show (row ⊔ column).cells ⊆ U.cells from sup_le hp' hq')
    change (row ⊔ column).card ≤ U.card at bound
    have actualCard : (row ⊔ column).card = 7 := by decide
    omega

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  let p := Nat.Partition.indiscrete 1
  let empty : Finset (Nat.Partition 1) := ∅
  let singleton : Finset (Nat.Partition 1) := {p}
  refine ⟨1, empty, singleton, ?_⟩
  change (empty : Set (Nat.Partition 1)) ≠ (singleton : Set (Nat.Partition 1))
  intro equal
  have member : p ∈ (singleton : Set (Nat.Partition 1)) := by simp [singleton]
  rw [← equal] at member
  simp [empty] at member

def familyRegistration : Registration arena (type_of% (@clique_star_or_top)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@clique_star_or_top), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@clique_star_or_top) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.clique_star_or_top.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.CliqueStarOrTop.familyRegistration
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
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "domain", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end CliqueStarOrTop

end Reg.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex

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

namespace Reg.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex

namespace MemStaircase

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ c => Prod.fst c) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r : ℕ) (c : ℕ × ℕ), c ∈ staircase r ↔ R.readout () () c + c.2 < r

private theorem source_bridge : (type_of% mem_staircase) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h 1 (1, 0)
  have member := bad.mpr (by decide)
  exact (by decide : ¬ (1 + 0 < 1)) ((mem_staircase 1 (1, 0)).mp member)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  change 0 ≠ 1
  exact Nat.zero_ne_one

def familyRegistration : Registration arena (type_of% mem_staircase) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp mem_staircase, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    mem_staircase (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.mem_staircase.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.MemStaircase.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => Prod.fst c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end MemStaircase

namespace ExpandedCard

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ r e => (expandedStaircase r e).card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ r e : ℕ, R.readout () r e = triangular r + e

private theorem source_bridge : (type_of% expanded_card) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h 0 1
  change 0 = triangular 0 + 1 at bad
  exact (by decide : 0 ≠ triangular 0 + 1) bad

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨0, 0, 1, ?_⟩
  change (expandedStaircase 0 0).card ≠ (expandedStaircase 0 1).card
  rw [expanded_card, expanded_card]
  omega

def familyRegistration : Registration arena (type_of% expanded_card) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp expanded_card, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    expanded_card (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.expanded_card.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.ExpandedCard.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r e => (expandedStaircase r e).card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end ExpandedCard

namespace MaximumAtThreshold

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r => maxDimension (triangular r + 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : ℕ, R.readout () () r = r

private theorem source_bridge : (type_of% maximum_at_threshold) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h 1
  change 0 = 1 at bad
  exact Nat.zero_ne_one bad

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change maxDimension (triangular 0 + 1) ≠ maxDimension (triangular 1 + 1)
  rw [maximum_at_threshold, maximum_at_threshold]
  exact Nat.zero_ne_one

def familyRegistration : Registration arena (type_of% maximum_at_threshold) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp maximum_at_threshold, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    maximum_at_threshold (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.maximum_at_threshold.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.MaximumAtThreshold.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => maxDimension (triangular r + 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end MaximumAtThreshold

end Reg.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
