import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Partitions.LyudogovskiyDimensionJump

/-! Source-bound readout of the first endpoint dimension in the universal edge inequality. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.Partitions.LyudogovskiyDimensionJump
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
open _root_.D5.S3.Combinatorics.Partitions.LyudogovskiyDimensionJump

abbrev signature : Signature where
  Params := ℕ
  State := Nat.Partition
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => localDimension p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ p => localDimension p + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ (n : ℕ), 0 < n → ∀ p q : Nat.Partition n, (graph n).Adj p q →
      |(R.readout () n p : ℤ) - (localDimension q : ℤ)| ≤ 2) ∧
    (∀ (k : ℕ), 4 ≤ k → ∃ p q : Nat.Partition (3 * k - 1),
      (YoungDiagram.ofPartition p).rowLens = [k, k, k - 2, 1] ∧
      (YoungDiagram.ofPartition q).rowLens = [k, k, k - 1] ∧
      (graph (3 * k - 1)).Adj p q ∧ localDimension p = 4 ∧ localDimension q = 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, q, _, _, hadj, hp, hq⟩ := result.2 4 (by decide)
  have bad := h.1 11 (by decide) p q hadj
  change |((localDimension p + 1 : ℕ) : ℤ) - (localDimension q : ℤ)| ≤ 2 at bad
  norm_num [hp, hq] at bad

private theorem source_bridge : (type_of% result) ↔ arena.Law actual := Iff.rfl

private theorem dimension_dependence : ObservationalDependence signature actual := by
  simp only [ObservationalDependence, actual, realize, signature]
  intro i
  obtain ⟨p, q, _, _, _, hp, hq⟩ := result.2 4 (by decide)
  refine ⟨(3 * 4 - 1 : ℕ), p, q, ?_⟩
  rw [hp, hq]
  decide

set_option maxHeartbeats 1000000 in
def familyRegistration : Registration arena (type_of% result) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dimension_dependence

set_option maxHeartbeats 1000000 in
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    result (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := `D5.S3.Combinatorics.Partitions.LyudogovskiyDimensionJump.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.LyudogovskiyDimensionJump.familyRegistration
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
    owner := `D5.S3.Combinatorics.Partitions.LyudogovskiyDimensionJump
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Reg.D5.S3.Combinatorics.Partitions.LyudogovskiyDimensionJump
