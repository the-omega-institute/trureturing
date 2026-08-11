/- GID: D5/S0/History/LedgerLimit
   generality: G
   mirror-B: D5/B/S0/History/LedgerLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finitely revised ledger has a unique pointwise terminal grading. -/

import Mathlib.Order.Filter.Cofinite

namespace D5.S0.History.LedgerLimit

/-- A ledger history presents every eventually enrolled statement together with
its enrollment time and its grade at each clock tick. Values before enrollment
are ignored. -/
structure LedgerHistory (Statement Grade : Type*) where
  enrolledAt : Statement -> Nat
  grade : Statement -> Nat -> Grade

/-- Statements enrolled by time `t`. Enrollment times make these sets
append-only by construction. -/
def LedgerHistory.statementsAt {Statement Grade : Type*}
    (history : LedgerHistory Statement Grade) (t : Nat) : Set Statement :=
  {statement | history.enrolledAt statement <= t}

/-- The clock ticks at which a grade changes after the statement is enrolled. -/
def revisionTimesFrom {Grade : Type*} (start : Nat) (grades : Nat -> Grade) : Set Nat :=
  {t | start <= t /\ grades (t + 1) ≠ grades t}

/-- A grade track has a terminal value after `start` when it is constant from
some later clock tick onward. -/
def HasTerminalValueAfter {Grade : Type*} (start : Nat) (grades : Nat -> Grade) : Prop :=
  exists terminal cutoff, start <= cutoff /\ forall t, cutoff <= t -> grades t = terminal

theorem statementsAt_mono {Statement Grade : Type*}
    (history : LedgerHistory Statement Grade) {t u : Nat} (htu : t <= u) :
    history.statementsAt t <= history.statementsAt u := by
  intro statement enrolled
  exact enrolled.trans htu

/-- The repair clause: finitely many post-enrollment revisions force the grade
track to stabilize. -/
theorem finite_revisions_have_terminal_value {Grade : Type*}
    (start : Nat) (grades : Nat -> Grade)
    (finiteRevisions : (revisionTimesFrom start grades).Finite) :
    HasTerminalValueAfter start grades := by
  have noRevisions : ∀ᶠ t in Filter.atTop, t ∉ revisionTimesFrom start grades := by
    rw [← Nat.cofinite_eq_atTop]
    exact finiteRevisions.eventually_cofinite_notMem
  rw [Filter.eventually_atTop] at noRevisions
  obtain ⟨bound, noRevisions⟩ := noRevisions
  let cutoff := max start bound
  refine ⟨grades cutoff, cutoff, le_max_left _ _, ?_⟩
  intro t hcutoff
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hcutoff
  clear hcutoff
  induction offset with
  | zero => rfl
  | succ offset ih =>
      rw [Nat.add_succ]
      have hstep : grades (cutoff + offset + 1) = grades (cutoff + offset) := by
        by_contra changed
        apply noRevisions (cutoff + offset)
        · exact (le_max_right start bound).trans
            (Nat.le_add_right (max start bound) offset)
        · exact ⟨(le_max_left start bound).trans (Nat.le_add_right cutoff offset), changed⟩
      exact hstep.trans ih

/-- An eventually constant grade track has only one possible terminal value. -/
theorem terminal_value_unique {Grade : Type*} {start : Nat} {grades : Nat -> Grade}
    {left right : Grade}
    (leftTerminal : exists cutoff, start <= cutoff /\
      forall t, cutoff <= t -> grades t = left)
    (rightTerminal : exists cutoff, start <= cutoff /\
      forall t, cutoff <= t -> grades t = right) :
    left = right := by
  obtain ⟨leftCutoff, _, leftStable⟩ := leftTerminal
  obtain ⟨rightCutoff, _, rightStable⟩ := rightTerminal
  let cutoff := max leftCutoff rightCutoff
  exact (leftStable cutoff (le_max_left _ _)).symm.trans
    (rightStable cutoff (le_max_right _ _))

/-- Theorem 7.2: for a countable ledger graded in a finite partial order, the
repair clause determines a unique terminal grading on all eventually enrolled
statements. -/
theorem ledger_limit_exists_unique
    {Statement Grade : Type*} [Countable Statement] [Finite Grade] [PartialOrder Grade]
    (history : LedgerHistory Statement Grade)
    (repairClause : forall statement,
      (revisionTimesFrom (history.enrolledAt statement) (history.grade statement)).Finite) :
    ∃! terminalGrade : Statement -> Grade,
      forall statement, exists cutoff,
        history.enrolledAt statement <= cutoff /\
          forall t, cutoff <= t -> history.grade statement t = terminalGrade statement := by
  classical
  have eachStatement : forall statement,
      HasTerminalValueAfter (history.enrolledAt statement) (history.grade statement) :=
    fun statement => finite_revisions_have_terminal_value
      (history.enrolledAt statement) (history.grade statement) (repairClause statement)
  choose terminalGrade cutoff enrolled stable using eachStatement
  refine ⟨terminalGrade, fun statement =>
    ⟨cutoff statement, enrolled statement, stable statement⟩, ?_⟩
  intro other otherStable
  funext statement
  exact terminal_value_unique
    (leftTerminal := otherStable statement)
    (rightTerminal :=
      ⟨cutoff statement, enrolled statement, stable statement⟩)

/-- A two-grade track that changes at every clock tick. -/
def alternatingGrade : Nat -> Bool
  | 0 => false
  | t + 1 => !(alternatingGrade t)

private theorem alternatingGrade_changes (t : Nat) :
    alternatingGrade (t + 1) ≠ alternatingGrade t := by
  cases value : alternatingGrade t <;> simp [alternatingGrade, value]

/-- The repair clause cannot be dropped: permanent two-grade oscillation has
no terminal value. -/
theorem alternating_grade_has_no_terminal_value :
    ¬ HasTerminalValueAfter 0 alternatingGrade := by
  rintro ⟨terminal, cutoff, _, stable⟩
  apply alternatingGrade_changes cutoff
  exact (stable (cutoff + 1) (Nat.le_succ cutoff)).trans
    (stable cutoff le_rfl).symm

/-- Equivalently, the alternating counterexample has infinitely many revision
times, so it lies exactly outside the repair clause. -/
theorem alternating_revision_times_infinite :
    (revisionTimesFrom 0 alternatingGrade).Infinite := by
  intro finiteRevisions
  exact alternating_grade_has_no_terminal_value
    (finite_revisions_have_terminal_value 0 alternatingGrade finiteRevisions)

end D5.S0.History.LedgerLimit
