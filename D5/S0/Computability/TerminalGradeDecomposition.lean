/- GID: D5/S0/Computability/TerminalGradeDecomposition
   generality: G
   mirror-B: D5/B/S0/Computability/TerminalGradeDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Terminal grades partition semantic statements into migrated, wall, and resident parts. -/

import D5.S0.Computability.GuardedWall
import D5.S0.History.LedgerLimit

namespace D5.S0.Computability.TerminalGradeDecomposition

open D5.S0.Computability.GuardedWall
open D5.S0.History.LedgerLimit

/-- A finitely revised ledger has a unique terminal grading. If a guarded wall lies in the
semantic domain, its gatekeepers remain positive, joint positivity is forbidden, and forbidden
configurations never occur, then the semantic domain is the disjoint union of terminal-positive
statements, the wall, and all remaining semantic statements. -/
theorem terminal_grade_three_way_decomposition
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
  obtain ⟨terminalGrade, stable, terminalUnique⟩ :=
    ledger_limit_exists_unique history repairClause
  have wallTerminal : forall statement, statement ∈ wall ->
      terminalGrade statement ∉ positiveGrades := by
    have wallNeverPositive := wall_never_positive
      (positive := fun t statement => history.grade statement t ∈ positiveGrades)
      wall gatekeepers forbidden gatekeepers_positive joint_positive_forbidden consistent
    intro statement hwall hterminal
    obtain ⟨cutoff, _, stableAfter⟩ := stable statement
    exact wallNeverPositive cutoff statement hwall
      (by simpa [stableAfter cutoff le_rfl] using hterminal)
  let migrated := {statement ∈ semantic | terminalGrade statement ∈ positiveGrades}
  let resident := semantic \ (migrated ∪ wall)
  have covers : semantic = migrated ∪ wall ∪ resident := by
    ext statement
    constructor
    · intro hsemantic
      by_cases hmigrated : statement ∈ migrated
      · exact Or.inl (Or.inl hmigrated)
      by_cases hwall : statement ∈ wall
      · exact Or.inl (Or.inr hwall)
      · exact Or.inr ⟨hsemantic, by
          rintro (hmigrated' | hwall')
          · exact hmigrated hmigrated'
          · exact hwall hwall'⟩
    · rintro ((hmigrated | hwall) | hresident)
      · exact hmigrated.1
      · exact wall_semantic hwall
      · exact hresident.1
  have migratedWall : Disjoint migrated wall := Set.disjoint_left.2 (by
    intro statement hmigrated hwall
    exact wallTerminal statement hwall hmigrated.2)
  have migratedResident : Disjoint migrated resident := Set.disjoint_left.2 (by
    intro statement hmigrated hresident
    exact hresident.2 (Or.inl hmigrated))
  have wallResident : Disjoint wall resident := Set.disjoint_left.2 (by
    intro statement hwall hresident
    exact hresident.2 (Or.inr hwall))
  refine ⟨terminalGrade, ⟨stable, ?_⟩, ?_⟩
  · change semantic = migrated ∪ wall ∪ resident /\
      Disjoint migrated wall /\
      Disjoint migrated resident /\
      Disjoint wall resident
    exact ⟨covers, migratedWall, migratedResident, wallResident⟩
  · intro other otherProperties
    exact terminalUnique other otherProperties.1

/-- Checked evidence that the statement domain is inhabited. -/
example : Bool := false

/-- A constant Boolean ledger witnesses simultaneous satisfiability of the repair, wall,
gatekeeper, forbidden-configuration, and consistency assumptions. -/
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

end D5.S0.Computability.TerminalGradeDecomposition
