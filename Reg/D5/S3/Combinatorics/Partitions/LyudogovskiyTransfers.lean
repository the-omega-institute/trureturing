import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Partitions.LyudogovskiyTransfers

/-! Source-bound audit of the complete transfer/intersection equivalence. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.Partitions.LyudogovskiyTransfers
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex

abbrev signature : Signature where
  Params := Σ n : ℕ, Nat.Partition n
  State np := Nat.Partition np.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ np q => (YoungDiagram.ofPartition np.2 ⊓ YoungDiagram.ofPartition q).card)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ np q => (YoungDiagram.ofPartition np.2 ⊓ YoungDiagram.ofPartition q).card + 1)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (n : ℕ), 0 < n → ∀ (p q : Nat.Partition n),
    UnitTransfer p q ↔ readout.readout () ⟨n,p⟩ q = n - 1

private theorem source_bridge : (type_of% (@transfer_iff_intersection)) ↔ arena.Law actual :=
  Iff.rfl

private def two : Nat.Partition 2 := Nat.Partition.indiscrete 2

private def ones : Nat.Partition 2 where
  parts := {1,1}
  parts_pos := by simp
  parts_sum := by decide

private theorem edge : UnitTransfer two ones := by
  refine ⟨?_, 0, 1, 0, ?_, ?_⟩
  · intro h
    have hh := congrArg (fun p : Nat.Partition 2 => p.parts.card) h
    norm_num [two, ones] at hh
  · simp [two, Nat.Partition.indiscrete, Nat.Partition.ofSums, part]
  · simp [ones, part]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hg := (transfer_iff_intersection (by decide) two ones).mp edge
  have hb := (h 2 (by decide) two ones).mp edge
  change (YoungDiagram.ofPartition two ⊓ YoungDiagram.ofPartition ones).card + 1 = 2 - 1 at hb
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨2,two⟩, two, ones, ?_⟩
  change (YoungDiagram.ofPartition two ⊓ YoungDiagram.ofPartition two).card ≠
    (YoungDiagram.ofPartition two ⊓ YoungDiagram.ofPartition ones).card
  rw [inf_idem, YoungDiagram.card_ofPartition,
    (transfer_iff_intersection (by decide) two ones).mp edge]
  decide

def familyRegistration : Registration arena (type_of% (@transfer_iff_intersection)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@transfer_iff_intersection), rejected, rejected_law⟩
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
    (@transfer_iff_intersection) (type_of% (realize signature actual.readout actual.anchor))
    Unit Unit where
  unitName := `D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.transfer_iff_intersection.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.LyudogovskiyTransfers.familyRegistration
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
    owner := `D5.S3.Combinatorics.Partitions.LyudogovskiyTransfers
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Reg.D5.S3.Combinatorics.Partitions.LyudogovskiyTransfers
