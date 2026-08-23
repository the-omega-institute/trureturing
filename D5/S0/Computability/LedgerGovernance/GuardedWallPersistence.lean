/- GID: D5/S0/Computability/LedgerGovernance/GuardedWallPersistence
   generality: G
   mirror-B: D5/B/S0/Computability/LedgerGovernance/GuardedWallPersistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A guarded wall remains non-positive at finite and terminal ledger times. -/

/- Library-search audit trail (2026-08-22):
   * Exact repository hit `GuardedWall.wall_never_positive` proves the finite-time clause.
   * Exact repository hit `LedgerLimit.ledger_limit_exists_unique` constructs the unique
     terminal grade.
   * Searches for a public theorem combining both clauses returned no hit; the terminal wall fact
     appears only as a private proof step in `TerminalGradeDecomposition`. -/

import D5.S0.Computability.GuardedWall
import D5.S0.History.LedgerLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Computability.LedgerGovernance.GuardedWallPersistence

open D5.S0.Computability.GuardedWall
open D5.S0.History.LedgerLimit

/-- Gatekeeper positivity, a joint-forbidden declaration, and consistency keep every wall
statement outside the positive grades at every finite time. Under the finite-revision repair
clause, the unique terminal grading keeps the same wall outside the positive grades. -/
theorem guarded_wall_persists_in_ledger_limit
    {Statement Grade : Type*} [Countable Statement] [Finite Grade] [PartialOrder Grade]
    (history : LedgerHistory Statement Grade)
    (repairClause : forall statement,
      (revisionTimesFrom (history.enrolledAt statement) (history.grade statement)).Finite)
    (positiveGrades : Set Grade)
    (wall gatekeepers : Set Statement)
    (forbidden : Nat -> Statement -> Prop)
    (gatekeepers_positive : forall t g,
      g ∈ gatekeepers -> history.grade g t ∈ positiveGrades)
    (joint_positive_forbidden : forall t w,
      w ∈ wall -> history.grade w t ∈ positiveGrades ->
        (forall g, g ∈ gatekeepers -> history.grade g t ∈ positiveGrades) -> forbidden t w)
    (consistent : forall t w, w ∈ wall -> Not (forbidden t w)) :
    (forall t w, w ∈ wall -> history.grade w t ∉ positiveGrades) /\
      ∃! terminalGrade : Statement -> Grade,
        (forall statement, exists cutoff,
          history.enrolledAt statement <= cutoff /\
            forall t, cutoff <= t -> history.grade statement t = terminalGrade statement) /\
        forall w, w ∈ wall -> terminalGrade w ∉ positiveGrades := by
  have wallNeverPositive := wall_never_positive
    (positive := fun t statement => history.grade statement t ∈ positiveGrades)
    wall gatekeepers forbidden gatekeepers_positive joint_positive_forbidden consistent
  refine ⟨wallNeverPositive, ?_⟩
  obtain ⟨terminalGrade, stable, terminalUnique⟩ :=
    ledger_limit_exists_unique history repairClause
  refine ⟨terminalGrade, ⟨stable, ?_⟩, ?_⟩
  · intro statement hwall hterminal
    obtain ⟨cutoff, _, stableAfter⟩ := stable statement
    exact wallNeverPositive cutoff statement hwall
      (by simpa [stableAfter cutoff le_rfl] using hterminal)
  · intro other otherProperties
    exact terminalUnique other otherProperties.1

/-- A constant Boolean ledger checks that all source hypotheses are jointly satisfiable. -/
example :
    let history : LedgerHistory Bool Bool :=
      { enrolledAt := fun _ => 0, grade := fun statement _ => statement }
    let positiveGrades : Set Bool := {true}
    let wall : Set Bool := {false}
    let gatekeepers : Set Bool := {true}
    let forbidden : Nat -> Bool -> Prop := fun _ statement => statement = false ∧ statement = true
    (forall statement,
      (revisionTimesFrom (history.enrolledAt statement) (history.grade statement)).Finite) /\
    (forall t g, g ∈ gatekeepers -> history.grade g t ∈ positiveGrades) /\
    (forall t w, w ∈ wall -> history.grade w t ∈ positiveGrades ->
      (forall g, g ∈ gatekeepers -> history.grade g t ∈ positiveGrades) -> forbidden t w) /\
    (forall t w, w ∈ wall -> Not (forbidden t w)) := by
  dsimp
  constructor
  · intro statement
    simp [revisionTimesFrom]
  constructor
  · intro _ statement hgatekeeper
    exact hgatekeeper
  constructor
  · intro _ statement hwall hpositive _
    exact ⟨hwall, hpositive⟩
  · intro _ statement _ hforbidden
    exact Bool.noConfusion (hforbidden.1.symm.trans hforbidden.2)

end D5.S0.Computability.LedgerGovernance.GuardedWallPersistence
