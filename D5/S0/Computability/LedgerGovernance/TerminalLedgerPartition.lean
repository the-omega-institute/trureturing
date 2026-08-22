/- GID: D5/S0/Computability/LedgerGovernance/TerminalLedgerPartition
   generality: G
   mirror-B: D5/B/S0/Computability/LedgerGovernance/TerminalLedgerPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Terminal grades partition the semantic ledger into migrated, wall, and resident sets. -/

/- Library-search audit trail (2026-08-22):
   * Exact repository hit `TerminalGradeDecomposition.terminal_grade_three_way_decomposition`
     exposes the canonical migrated and resident sets, their cover equality, and pairwise
     disjointness. The public theorem below imports and applies that result directly. -/

import D5.S0.Computability.TerminalGradeDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Computability.LedgerGovernance.TerminalLedgerPartition

open D5.S0.Computability.TerminalGradeDecomposition
open D5.S0.History.LedgerLimit

/-- Under finite revision and guarded-wall consistency, the unique terminal grading partitions
the semantic ledger into the terminal-positive migrated set, the wall, and the remaining
resident set, with all three parts pairwise disjoint. -/
theorem terminal_ledger_three_way_partition
    {Statement Grade : Type*} [Countable Statement] [Finite Grade] [PartialOrder Grade]
    (history : LedgerHistory Statement Grade)
    (repairClause : forall statement,
      (revisionTimesFrom (history.enrolledAt statement) (history.grade statement)).Finite)
    (positiveGrades : Set Grade)
    (semantic wall gatekeepers : Set Statement)
    (wall_semantic : wall ⊆ semantic)
    (forbidden : Nat -> Statement -> Prop)
    (gatekeepers_positive : forall t g,
      g ∈ gatekeepers -> history.grade g t ∈ positiveGrades)
    (joint_positive_forbidden : forall t w,
      w ∈ wall -> history.grade w t ∈ positiveGrades ->
        (forall g, g ∈ gatekeepers -> history.grade g t ∈ positiveGrades) -> forbidden t w)
    (consistent : forall t w, w ∈ wall -> Not (forbidden t w)) :
    ∃! terminalGrade : Statement -> Grade,
      (forall statement, exists cutoff,
        history.enrolledAt statement <= cutoff /\
          forall t, cutoff <= t -> history.grade statement t = terminalGrade statement) /\
      (let migrated := {statement ∈ semantic | terminalGrade statement ∈ positiveGrades}
       let resident := semantic \ (migrated ∪ wall)
       semantic = migrated ∪ wall ∪ resident /\
         Disjoint migrated wall /\
         Disjoint migrated resident /\
         Disjoint wall resident) := by
  exact terminal_grade_three_way_decomposition history repairClause positiveGrades
    semantic wall gatekeepers wall_semantic forbidden gatekeepers_positive
    joint_positive_forbidden consistent

/-- A constant Boolean ledger checks that all decomposition hypotheses are jointly satisfiable. -/
example :
    let history : LedgerHistory Bool Bool :=
      { enrolledAt := fun _ => 0, grade := fun statement _ => statement }
    let positiveGrades : Set Bool := {true}
    let semantic : Set Bool := Set.univ
    let wall : Set Bool := {false}
    let gatekeepers : Set Bool := {true}
    let forbidden : Nat -> Bool -> Prop := fun _ statement => statement = false ∧ statement = true
    (forall statement,
      (revisionTimesFrom (history.enrolledAt statement) (history.grade statement)).Finite) /\
    wall ⊆ semantic /\
    (forall t g, g ∈ gatekeepers -> history.grade g t ∈ positiveGrades) /\
    (forall t w, w ∈ wall -> history.grade w t ∈ positiveGrades ->
      (forall g, g ∈ gatekeepers -> history.grade g t ∈ positiveGrades) -> forbidden t w) /\
    (forall t w, w ∈ wall -> Not (forbidden t w)) := by
  dsimp
  constructor
  · intro statement
    simp [revisionTimesFrom]
  constructor
  · intro statement _
    trivial
  constructor
  · intro _ statement hgatekeeper
    exact hgatekeeper
  constructor
  · intro _ statement hwall hpositive _
    exact ⟨hwall, hpositive⟩
  · intro _ statement _ hforbidden
    exact Bool.noConfusion (hforbidden.1.symm.trans hforbidden.2)

end D5.S0.Computability.LedgerGovernance.TerminalLedgerPartition
