/- GID: D5/S0/History/LedgerLimit
   generality: G
   mirror-B: D5/B/S0/History/LedgerLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finitely revised ledger has a unique pointwise terminal grading. -/

import Mathlib.Order.Filter.Cofinite
import OmegaInit.Data.Nat.Basic

/-! Terminal values and pointwise limits of finitely revised ledger histories. -/

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

/-- The strict clock and equality formulation of stabilization to a specified value. -/
noncomputable def StrictTerminalValueAfter {Grade : Type u}
    (start : Omega.Nat) (grades : Omega.Nat → Grade) (terminal : Grade) : Prop :=
  Omega.Exists (fun cutoff => Omega.And (Omega.Nat.le start cutoff)
    (∀ t, Omega.Nat.le cutoff t → Omega.Eq (grades t) terminal))

/-- An eventually constant grade track has only one possible terminal value. -/
theorem terminal_value_unique {Grade : Type u} {start : Omega.Nat} {grades : Omega.Nat → Grade}
    {left right : Grade}
    (leftTerminal : StrictTerminalValueAfter start grades left)
    (rightTerminal : StrictTerminalValueAfter start grades right) : Omega.Eq left right :=
  leftTerminal.elim (fun leftCutoff leftTail =>
    rightTerminal.elim (fun rightCutoff rightTail =>
      (Omega.Nat.le_total leftCutoff rightCutoff).elim
        (fun h => (leftTail.right rightCutoff h).symm.trans
          (rightTail.right rightCutoff (Omega.Nat.le_refl rightCutoff)))
        (fun h => (leftTail.right leftCutoff (Omega.Nat.le_refl leftCutoff)).symm.trans
          (rightTail.right leftCutoff h))))

private noncomputable def toStdNat : Omega.Nat → Nat := Omega.Nat.rec 0 (fun _ n => n.succ)

private def toStrictNat : Nat → Omega.Nat := Nat.rec .zero (fun _ n => n.succ)

private theorem toStdNat_toStrictNat (n : Nat) : toStdNat (toStrictNat n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

private theorem toStdNat_le {a b : Omega.Nat} (h : Omega.Nat.le a b) :
    toStdNat a ≤ toStdNat b := by
  induction a generalizing b with
  | zero => exact Nat.zero_le _
  | succ a ih =>
      induction b with
      | zero => exact Omega.False.elim (Omega.Nat.not_succ_le_zero a h)
      | succ b _ => exact Nat.succ_le_succ (ih (Omega.Nat.le_of_succ_le_succ h))

private theorem toStrictNat_le {a b : Nat} (h : a ≤ b) :
    Omega.Nat.le (toStrictNat a) (toStrictNat b) := by
  induction h with
  | refl => exact Omega.Nat.le_refl _
  | step _ ih => exact Omega.Nat.le.step ih

private theorem strictTerminalValue_of_standard {Grade : Type*} {start : Nat}
    {grades : Nat → Grade} {terminal : Grade}
    (h : ∃ cutoff, start ≤ cutoff ∧ ∀ t, cutoff ≤ t → grades t = terminal) :
    StrictTerminalValueAfter (toStrictNat start) (fun t => grades (toStdNat t)) terminal := by
  obtain ⟨cutoff, enrolled, tail⟩ := h
  refine Omega.Exists.intro (toStrictNat cutoff) (Omega.And.intro (toStrictNat_le enrolled) ?_)
  intro t ht
  have bound : cutoff ≤ toStdNat t := by simpa only [toStdNat_toStrictNat] using toStdNat_le ht
  exact (tail (toStdNat t) bound) ▸ Omega.rfl

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
  have same := terminal_value_unique (strictTerminalValue_of_standard (otherStable statement))
    (strictTerminalValue_of_standard ⟨cutoff statement, enrolled statement, stable statement⟩)
  exact Omega.Eq.rec rfl same

/-- A two-grade track that changes at every clock tick. -/
def alternatingGrade : Nat -> Bool
  | 0 => false
  | t + 1 => !(alternatingGrade t)

private noncomputable def flipGrade : Omega.Bool → Omega.Bool := Omega.Bool.rec .true .false

/-- A strict Boolean track obtained by flipping the preceding grade at each successor. -/
noncomputable def strictAlternatingGrade : Omega.Nat → Omega.Bool :=
  Omega.Nat.rec .false (fun _ grade => flipGrade grade)

private theorem alternatingGrade_changes (t : Omega.Nat) :
    Omega.Not (Omega.Eq (strictAlternatingGrade t.succ) (strictAlternatingGrade t)) :=
  have trueNeFalse : Omega.Not (Omega.Eq Omega.Bool.true Omega.Bool.false) :=
    fun h => Omega.Eq.subst (motive := Omega.Bool.rec Omega.False Omega.True) h Omega.True.intro
  Omega.Bool.rec (motive := fun b => Omega.Not (Omega.Eq (flipGrade b) b))
    trueNeFalse (fun h => trueNeFalse h.symm) (strictAlternatingGrade t)

/-- The repair clause cannot be dropped: permanent two-grade oscillation has
no terminal value. -/
theorem alternating_grade_has_no_terminal_value :
    Omega.Not (Omega.Exists (StrictTerminalValueAfter .zero strictAlternatingGrade)) :=
  fun terminal => terminal.elim (fun _ stability =>
    stability.elim (fun cutoff tail => alternatingGrade_changes cutoff
      ((tail.right cutoff.succ (Omega.Nat.le.step (Omega.Nat.le_refl cutoff))).trans
        (tail.right cutoff (Omega.Nat.le_refl cutoff)).symm)))

private def toStrictBool : Bool → Omega.Bool := Bool.rec .false .true

private theorem strictAlternatingGrade_eq (n : Omega.Nat) :
    strictAlternatingGrade n = toStrictBool (alternatingGrade (toStdNat n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change flipGrade (strictAlternatingGrade n) =
        toStrictBool (!(alternatingGrade (toStdNat n)))
      rw [ih]
      cases alternatingGrade (toStdNat n) <;> rfl

/-- Equivalently, the alternating counterexample has infinitely many revision
times, so it lies exactly outside the repair clause. -/
theorem alternating_revision_times_infinite :
    (revisionTimesFrom 0 alternatingGrade).Infinite := by
  intro finiteRevisions
  obtain ⟨terminal, cutoff, enrolled, stable⟩ :=
    finite_revisions_have_terminal_value 0 alternatingGrade finiteRevisions
  have strictTail := strictTerminalValue_of_standard
    (grades := fun t => toStrictBool (alternatingGrade t)) (terminal := toStrictBool terminal)
    ⟨cutoff, enrolled, fun t ht => congrArg toStrictBool (stable t ht)⟩
  apply Omega.False.elim
  apply alternating_grade_has_no_terminal_value
  refine Omega.Exists.intro (toStrictBool terminal) (strictTail.elim fun strictCutoff tail => ?_)
  refine Omega.Exists.intro strictCutoff (Omega.And.intro tail.left fun t ht => ?_)
  rw [strictAlternatingGrade_eq]
  exact tail.right t ht

end D5.S0.History.LedgerLimit
