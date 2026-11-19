import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Polyomino.Figure26Prismaticity
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Polyomino.Figure26Prismaticity

open _root_.D5.S3.Combinatorics.Polyomino.Figure26Prismaticity
open _root_.D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory (Point)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The original anchor is the state. The displayed panel fixes all operands
of the word observation except that anchor. -/
abbrev signature : Signature where
  Params := Unit
  State _ := Point
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Word
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena (P : Fin 4 → Point) (B : Finset Point) : Arena where
  signature := signature
  Law r :=
    (IsPolyhex (offsets P) ∧ (offsets P).card = 4 ∧
      IsPolyhex B ∧ B.card = 28 ∧ (anchors P B).card = 16 ∧
      (∀ w : Word, ((anchors P B).filter
        fun t => r.readout () () t = w).card = 1)) ∧
    IsDense P 16 B

abbrev actual (P : Fin 4 → Point) (color : Point → Bool) : Realization signature :=
  realize signature (fun _ _ t => wordAt P color t) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => (false, false, false, false)) (fun e => nomatch e)

private theorem rejected_law (P : Fin 4 → Point) (B : Finset Point) :
    ¬ (arena P B).Law rejected := by
  intro h
  have bad := h.1.2.2.2.2.2 (true, false, false, false)
  have hzero : (anchors P B).filter
      (fun t => rejected.readout () () t = (true, false, false, false)) = ∅ := by
    ext t
    simp [rejected, realize]
  change ((anchors P B).filter
      (fun t => rejected.readout () () t = (true, false, false, false))).card = 1 at bad
  simp [hzero] at bad

def leftArena : Arena := arena leftIssuePattern leftIssueBoard

def leftSource :
    Registration leftArena (type_of% @left_issue_prismatic) where
  actual := realize signature (fun _ _ t => wordAt leftIssuePattern leftIssueColor t)
    (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨left_issue_prismatic, rejected,
    rejected_law leftIssuePattern leftIssueBoard⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law leftIssuePattern leftIssueBoard⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro _
    refine ⟨(), (-5, 1), (-5, 2), ?_⟩
    change wordAt leftIssuePattern leftIssueColor (-5, 1) ≠
      wordAt leftIssuePattern leftIssueColor (-5, 2)
    decide +kernel

noncomputable def leftRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@left_issue_prismatic) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Polyomino.Figure26Prismaticity.leftUnit
  realizationName := `Reg.D5.S3.Combinatorics.Polyomino.Figure26Prismaticity.leftSource
  realizationSource := none
  generated := false
  arena := .source ⟨leftArena⟩
  objectArena := .source ⟨leftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source leftArena ⟨leftSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => wordAt leftIssuePattern leftIssueColor t)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Polyomino.Figure26Prismaticity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "arg", "arg", "arg", "arg", "arg", "body",
        "fn", "arg", "arg", "fn", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def rightArena : Arena := arena rightIssuePattern rightIssueBoard

def rightSource :
    Registration rightArena (type_of% @right_issue_prismatic) where
  actual := realize signature (fun _ _ t => wordAt rightIssuePattern rightIssueColor t)
    (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨right_issue_prismatic, rejected,
    rejected_law rightIssuePattern rightIssueBoard⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law rightIssuePattern rightIssueBoard⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro _
    refine ⟨(), (-6, -1), (-5, -2), ?_⟩
    change wordAt rightIssuePattern rightIssueColor (-6, -1) ≠
      wordAt rightIssuePattern rightIssueColor (-5, -2)
    decide +kernel

noncomputable def rightRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@right_issue_prismatic) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Polyomino.Figure26Prismaticity.rightUnit
  realizationName := `Reg.D5.S3.Combinatorics.Polyomino.Figure26Prismaticity.rightSource
  realizationSource := none
  generated := false
  arena := .source ⟨rightArena⟩
  objectArena := .source ⟨rightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rightArena ⟨rightSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => wordAt rightIssuePattern rightIssueColor t)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Polyomino.Figure26Prismaticity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "arg", "arg", "arg", "arg", "arg", "body",
        "fn", "arg", "arg", "fn", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.Polyomino.Figure26Prismaticity
