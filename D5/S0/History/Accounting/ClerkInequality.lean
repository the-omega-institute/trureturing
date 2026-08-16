/- GID: D5/S0/History/Accounting/ClerkInequality
   generality: G
   mirror-B: D5/B/S0/History/Accounting/ClerkInequality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Permanent records force two lower bounds on the semantic ledger. -/

import D5.S0.History.LedgerLimit
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-16):
   * Pinned Mathlib and Loogle both returned the exact declaration
     `Finset.sum_range_succ`; it is imported explicitly and applied in the two
     cumulative-count inductions below.
   * Repository searches for clerk inequalities, permanent-record accounting,
     migration counts, and both displayed lower bounds found no existing result.
     `D5/S0/History/LedgerLimit` supplies the existing append-only ledger carrier,
     which the accounting certificate below extends.
   * LeanSearch's query endpoint returned HTTP 404. -/

namespace D5.S0.History.Accounting.ClerkInequality

open D5.S0.History.LedgerLimit

/-- A finite counting certificate on an append-only ledger. `semanticAt t`
contains exactly the enrolled statements outside the distinguished theorem
grades. `migrationsAt t` contains exactly the statements entering those grades
at the next tick. Records created at tick `t` are newly enrolled, remain in every
later semantic snapshot, and satisfy the per-migration quota `r`. -/
structure ClerkHistory (Statement Grade : Type*) (r : Nat)
    extends LedgerHistory Statement Grade where
  theoremGrade : Grade -> Prop
  semanticAt : Nat -> Finset Statement
  semanticAt_spec : forall t statement,
    statement ∈ semanticAt t ↔
      enrolledAt statement <= t /\ ¬ theoremGrade (grade statement t)
  migrationsAt : Nat -> Finset Statement
  migrationsAt_spec : forall t statement,
    statement ∈ migrationsAt t ↔
      enrolledAt statement <= t /\
        (¬ theoremGrade (grade statement t)) /\
        theoremGrade (grade statement (t + 1))
  recordsAt : Nat -> Finset Statement
  recordNew : forall t statement, statement ∈ recordsAt t -> t < enrolledAt statement
  recordPermanent : forall t statement, statement ∈ recordsAt t ->
    forall u, t + 1 <= u -> statement ∈ semanticAt u
  recordQuota : forall t, r * (migrationsAt t).card <= (recordsAt t).card

/-- The total number of migrations strictly before tick `t`. -/
def cumulativeMigrations {Statement Grade : Type*} {r : Nat}
    (history : ClerkHistory Statement Grade r) (t : Nat) : Nat :=
  ∑ i ∈ Finset.range t, (history.migrationsAt i).card

/-- The total number of records created strictly before tick `t`. -/
def cumulativeRecordCount {Statement Grade : Type*} {r : Nat}
    (history : ClerkHistory Statement Grade r) (t : Nat) : Nat :=
  ∑ i ∈ Finset.range t, (history.recordsAt i).card

/-- All record statements created strictly before tick `t`. -/
noncomputable def cumulativeRecords {Statement Grade : Type*} {r : Nat}
    (history : ClerkHistory Statement Grade r) : Nat -> Finset Statement
  | 0 => ∅
  | t + 1 => by
      classical
      exact cumulativeRecords history t ∪ history.recordsAt t

private theorem mem_cumulativeRecords
    {Statement Grade : Type*} {r : Nat}
    (history : ClerkHistory Statement Grade r) (t : Nat) (statement : Statement) :
    statement ∈ cumulativeRecords history t ↔
      exists i, i < t /\ statement ∈ history.recordsAt i := by
  classical
  induction t with
  | zero => simp [cumulativeRecords]
  | succ t ih =>
      rw [cumulativeRecords, Finset.mem_union]
      constructor
      · rintro (oldRecord | newRecord)
        · obtain ⟨i, hi, record⟩ := ih.mp oldRecord
          exact ⟨i, hi.trans (Nat.lt_succ_self t), record⟩
        · exact ⟨t, Nat.lt_succ_self t, newRecord⟩
      · rintro ⟨i, hi, record⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with earlier | rfl
        · exact Or.inl (ih.mpr ⟨i, earlier, record⟩)
        · exact Or.inr record

private theorem cumulativeRecords_subset_semantic
    {Statement Grade : Type*} {r : Nat}
    (history : ClerkHistory Statement Grade r) (t : Nat) :
    cumulativeRecords history t ⊆ history.semanticAt t := by
  classical
  intro statement member
  obtain ⟨i, hi, record⟩ := (mem_cumulativeRecords history t statement).mp member
  exact history.recordPermanent i statement record t (by omega)

private theorem cumulativeRecords_disjoint_recordsAt
    {Statement Grade : Type*} {r : Nat}
    (history : ClerkHistory Statement Grade r) (t : Nat) :
    Disjoint (cumulativeRecords history t) (history.recordsAt t) := by
  classical
  rw [Finset.disjoint_left]
  intro statement oldRecord newRecord
  have oldSemantic := cumulativeRecords_subset_semantic history t oldRecord
  have enrolled : history.enrolledAt statement <= t :=
    (history.semanticAt_spec t statement).mp oldSemantic |>.1
  have fresh := history.recordNew t statement newRecord
  omega

private theorem cumulativeRecords_card
    {Statement Grade : Type*} {r : Nat}
    (history : ClerkHistory Statement Grade r) (t : Nat) :
    (cumulativeRecords history t).card = cumulativeRecordCount history t := by
  classical
  induction t with
  | zero => simp [cumulativeRecords, cumulativeRecordCount]
  | succ t ih =>
      rw [cumulativeRecords, Finset.card_union_of_disjoint
        (cumulativeRecords_disjoint_recordsAt history t), ih]
      simpa only [cumulativeRecordCount, Finset.sum_range_succ]

private theorem cumulative_record_quota
    {Statement Grade : Type*} {r : Nat}
    (history : ClerkHistory Statement Grade r) (t : Nat) :
    r * cumulativeMigrations history t <= cumulativeRecordCount history t := by
  induction t with
  | zero => simp [cumulativeMigrations, cumulativeRecordCount]
  | succ t ih =>
      rw [cumulativeMigrations, cumulativeRecordCount,
        Finset.sum_range_succ, Finset.sum_range_succ, Nat.mul_add]
      exact Nat.add_le_add ih (history.recordQuota t)

private theorem semantic_step_bound
    {Statement Grade : Type*} {r : Nat}
    (history : ClerkHistory Statement Grade r) (hr : 1 <= r) (t : Nat) :
    (history.semanticAt t).card + (r - 1) * (history.migrationsAt t).card <=
      (history.semanticAt (t + 1)).card := by
  classical
  have migrationSubset : history.migrationsAt t ⊆ history.semanticAt t := by
    intro statement migrating
    rw [history.semanticAt_spec]
    have migrationData := (history.migrationsAt_spec t statement).mp migrating
    exact ⟨migrationData.1, migrationData.2.1⟩
  have survivorsSubset :
      history.semanticAt t \ history.migrationsAt t ⊆ history.semanticAt (t + 1) := by
    intro statement surviving
    obtain ⟨oldMember, notMigrating⟩ := Finset.mem_sdiff.mp surviving
    rw [history.semanticAt_spec]
    have oldSemantic := (history.semanticAt_spec t statement).mp oldMember
    refine ⟨oldSemantic.1.trans (Nat.le_succ t), ?_⟩
    intro nextTheorem
    apply notMigrating
    rw [history.migrationsAt_spec]
    exact ⟨oldSemantic.1, oldSemantic.2, nextTheorem⟩
  have newRecordsSubset :
      history.recordsAt t ⊆ history.semanticAt (t + 1) := by
    intro statement record
    exact history.recordPermanent t statement record (t + 1) (Nat.le_refl (t + 1))
  have survivorRecordDisjoint :
      Disjoint (history.semanticAt t \ history.migrationsAt t) (history.recordsAt t) := by
    rw [Finset.disjoint_left]
    intro statement surviving record
    have oldMember := (Finset.mem_sdiff.mp surviving).1
    have enrolled : history.enrolledAt statement <= t :=
      (history.semanticAt_spec t statement).mp oldMember |>.1
    have fresh := history.recordNew t statement record
    omega
  have unionSubset :
      (history.semanticAt t \ history.migrationsAt t) ∪ history.recordsAt t ⊆
        history.semanticAt (t + 1) :=
    Finset.union_subset survivorsSubset newRecordsSubset
  have unionCard := Finset.card_le_card unionSubset
  rw [Finset.card_union_of_disjoint survivorRecordDisjoint,
    Finset.card_sdiff_of_subset migrationSubset] at unionCard
  have quota := history.recordQuota t
  have splitQuota :
      r * (history.migrationsAt t).card =
        (r - 1) * (history.migrationsAt t).card + (history.migrationsAt t).card := by
    calc
      r * (history.migrationsAt t).card =
          ((r - 1) + 1) * (history.migrationsAt t).card := by
            congr 1
            omega
      _ = (r - 1) * (history.migrationsAt t).card +
          (history.migrationsAt t).card := by
            rw [Nat.add_mul, Nat.one_mul]
  rw [splitQuota] at quota
  omega

/-- The clerk inequalities. If every migration creates at least `r >= 1` fresh
permanent records, then the semantic ledger contains at least `r` times the
cumulative migrations and at least its initial size plus `r - 1` times them. -/
theorem clerk_inequality {Statement Grade : Type*} {r : Nat}
    (history : ClerkHistory Statement Grade r) (hr : 1 <= r) (t : Nat) :
    r * cumulativeMigrations history t <= (history.semanticAt t).card /\
      (history.semanticAt 0).card + (r - 1) * cumulativeMigrations history t <=
        (history.semanticAt t).card := by
  constructor
  · exact (cumulative_record_quota history t).trans
      ((cumulativeRecords_card history t).symm ▸
        Finset.card_le_card (cumulativeRecords_subset_semantic history t))
  · induction t with
    | zero => simp [cumulativeMigrations]
    | succ t ih =>
        rw [cumulativeMigrations, Finset.sum_range_succ, Nat.mul_add]
        have ih' :
            (history.semanticAt 0).card +
                (r - 1) * (∑ i ∈ Finset.range t, (history.migrationsAt i).card) <=
              (history.semanticAt t).card := by
          simpa only [cumulativeMigrations] using ih
        have hstep := semantic_step_bound history hr t
        omega

/-- A concrete empty ledger supplies a checked inhabitant of the accounting
domain and shows that the theorem's hypotheses are jointly satisfiable. -/
def emptyClerkHistory : ClerkHistory Unit Unit 1 where
  enrolledAt := fun _ => 0
  grade := fun _ _ => ()
  theoremGrade := fun _ => True
  semanticAt := fun _ => ∅
  semanticAt_spec := by simp
  migrationsAt := fun _ => ∅
  migrationsAt_spec := by simp
  recordsAt := fun _ => ∅
  recordNew := by simp
  recordPermanent := by simp
  recordQuota := by simp

example : Nonempty (ClerkHistory Unit Unit 1) := ⟨emptyClerkHistory⟩

example (t : Nat) :
    1 * cumulativeMigrations emptyClerkHistory t <=
        (emptyClerkHistory.semanticAt t).card /\
      (emptyClerkHistory.semanticAt 0).card +
          (1 - 1) * cumulativeMigrations emptyClerkHistory t <=
        (emptyClerkHistory.semanticAt t).card :=
  clerk_inequality emptyClerkHistory (by omega) t

end D5.S0.History.Accounting.ClerkInequality

#print axioms D5.S0.History.Accounting.ClerkInequality.clerk_inequality
