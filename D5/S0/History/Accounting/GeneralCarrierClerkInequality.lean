/- GID: D5/S0/History/Accounting/GeneralCarrierClerkInequality
   generality: G
   mirror-B: D5/B/S0/History/Accounting/GeneralCarrierClerkInequality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fresh permanent records bound arbitrary semantic snapshots in ENat. -/

import D5.S0.History.LedgerLimit
import D5.S0.History.Accounting.ClerkInequality
import Mathlib.Data.Set.Card.Arithmetic

/-! General-carrier clerk accounting, derived in this repository. The existing
LedgerHistory supplies enrollment and grading; ClerkHistory supplies the finite
specialization. Semantic, migration, and record snapshots below may be infinite.
The proof uses Mathlib's disjoint-union encard identities and finite-sum API.
Provenance: the clerk accounting axiom in the interface-philosophy source.
The finite owner is recovered from this theorem, without using its proof. -/

namespace D5.S0.History.Accounting.GeneralCarrierClerkInequality

open D5.S0.History.LedgerLimit
open scoped BigOperators

/-- The accounting certificate on arbitrary sets over the existing ledger
history. Records are fresh at creation and permanently semantic thereafter. -/
structure SetClerkHistory (Statement Grade : Type*) (r : Nat)
    extends LedgerHistory Statement Grade where
  theoremGrade : Grade -> Prop
  semanticAt : Nat -> Set Statement
  semanticAt_spec : forall t statement,
    statement ∈ semanticAt t ↔
      enrolledAt statement <= t /\ ¬ theoremGrade (grade statement t)
  migrationsAt : Nat -> Set Statement
  migrationsAt_spec : forall t statement,
    statement ∈ migrationsAt t ↔
      enrolledAt statement <= t /\ ¬ theoremGrade (grade statement t) /\
        theoremGrade (grade statement (t + 1))
  recordsAt : Nat -> Set Statement
  recordNew : forall t statement, statement ∈ recordsAt t -> t < enrolledAt statement
  recordPermanent : forall t statement, statement ∈ recordsAt t ->
    forall u, t + 1 <= u -> statement ∈ semanticAt u
  recordQuota : forall t, (r : ENat) * (migrationsAt t).encard <= (recordsAt t).encard

/-- Migration events strictly before the indicated tick, including infinite
numbers of events at any one tick. -/
noncomputable def cumulativeMigrations {Statement Grade : Type*} {r : Nat}
    (history : SetClerkHistory Statement Grade r) (t : Nat) : ENat :=
  ∑ i ∈ Finset.range t, (history.migrationsAt i).encard

/-- One tick of accounting, using no subtraction of infinite cardinalities. -/
theorem semantic_step_bound {Statement : Type*}
    (semantic migrating records next : Set Statement) (r : Nat) (hr : 1 <= r)
    (hm : migrating ⊆ semantic) (hs : semantic \ migrating ⊆ next)
    (hn : records ⊆ next) (hd : Disjoint (semantic \ migrating) records)
    (hq : (r : ENat) * migrating.encard <= records.encard) :
    semantic.encard + ((r - 1 : Nat) : ENat) * migrating.encard <= next.encard := by
  calc
    semantic.encard + ((r - 1 : Nat) : ENat) * migrating.encard =
        (semantic \ migrating).encard + (r : ENat) * migrating.encard := by
      rw [← Set.encard_sdiff_add_encard_of_subset hm]
      have hr' : r = (r - 1) + 1 := by omega
      conv_rhs => rw [hr', Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      ac_rfl
    _ <= (semantic \ migrating).encard + records.encard := add_le_add_right hq _
    _ = ((semantic \ migrating) ∪ records).encard := (Set.encard_union_eq hd).symm
    _ <= next.encard := Set.encard_le_encard (Set.union_subset hs hn)

/-- Disjoint records for a finite family of ticks can themselves be infinite. -/
theorem finite_family_record_bound {Statement : Type*} {n : Nat}
    (records migrating : Fin n -> Set Statement) (semantic : Set Statement) (r : Nat)
    (hd : Pairwise (fun i j => Disjoint (records i) (records j)))
    (hp : forall i, records i ⊆ semantic)
    (hq : forall i, (r : ENat) * (migrating i).encard <= (records i).encard) :
    (r : ENat) * (∑ i, (migrating i).encard) <= semantic.encard := by
  calc
    (r : ENat) * (∑ i, (migrating i).encard) =
        ∑ i, (r : ENat) * (migrating i).encard := Finset.mul_sum ..
    _ <= ∑ i, (records i).encard := Finset.sum_le_sum (fun i _ => hq i)
    _ = (⋃ i, records i).encard := by
      simpa only [finsum_eq_sum_of_fintype] using (Set.encard_iUnion_of_finite hd).symm
    _ <= semantic.encard := Set.encard_le_encard (Set.iUnion_subset hp)

/-- Freshness makes the record batches disjoint, while permanence places all
earlier batches in the current semantic snapshot. This is the cumulative
general-set record bound used by the first clerk inequality. -/
theorem cumulative_record_bound {Statement Grade : Type*} {r : Nat}
    (history : SetClerkHistory Statement Grade r) (t : Nat) :
    (∑ i ∈ Finset.range t, (history.recordsAt i).encard) <=
      (history.semanticAt t).encard := by
  have orderedDisjoint : forall i j, i < j ->
      Disjoint (history.recordsAt i) (history.recordsAt j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro statement earlier later
    have semantic := history.recordPermanent i statement earlier j (Nat.succ_le_of_lt hij)
    have enrolled := ((history.semanticAt_spec j statement).mp semantic).1
    exact (Nat.not_lt_of_ge enrolled) (history.recordNew j statement later)
  have disjoint : Pairwise (fun i j : Fin t =>
      Disjoint (history.recordsAt i) (history.recordsAt j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne (Fin.val_injective.ne hij) with hlt | hgt
    · exact orderedDisjoint i j hlt
    · exact (orderedDisjoint j i hgt).symm
  have permanent : forall i : Fin t, history.recordsAt i ⊆ history.semanticAt t := by
    intro i statement record
    exact history.recordPermanent i statement record t (Nat.succ_le_of_lt i.isLt)
  have bound := finite_family_record_bound
    (fun i : Fin t => history.recordsAt i) (fun i : Fin t => history.recordsAt i)
    (history.semanticAt t) 1 disjoint permanent (by simp)
  simp only [Nat.cast_one, one_mul] at bound
  rw [Fin.sum_univ_eq_sum_range (fun i => (history.recordsAt i).encard)] at bound
  exact bound

/-- Finite tick induction in ENat does not require any snapshot to be finite. -/
theorem cumulative_step_bound (semantic migration : Nat -> ENat) (r n : Nat)
    (step : forall i, semantic i + ((r - 1 : Nat) : ENat) * migration i <= semantic (i + 1)) :
    semantic 0 + ((r - 1 : Nat) : ENat) * (∑ i ∈ Finset.range n, migration i)
      <= semantic n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ← add_assoc]
      exact (add_le_add_left ih _).trans (step n)

private theorem history_step_bound {Statement Grade : Type*} {r : Nat}
    (history : SetClerkHistory Statement Grade r) (hr : 1 <= r) (t : Nat) :
    (history.semanticAt t).encard + ((r - 1 : Nat) : ENat) *
      (history.migrationsAt t).encard <= (history.semanticAt (t + 1)).encard := by
  apply semantic_step_bound (history.semanticAt t) (history.migrationsAt t)
    (history.recordsAt t) (history.semanticAt (t + 1)) r hr
  · intro statement migrating
    have data := (history.migrationsAt_spec t statement).mp migrating
    exact (history.semanticAt_spec t statement).mpr ⟨data.1, data.2.1⟩
  · intro statement surviving
    have data := (history.semanticAt_spec t statement).mp surviving.1
    apply (history.semanticAt_spec (t + 1) statement).mpr
    refine ⟨data.1.trans (Nat.le_succ t), ?_⟩
    intro nextTheorem
    exact surviving.2 ((history.migrationsAt_spec t statement).mpr
      ⟨data.1, data.2, nextTheorem⟩)
  · intro statement record
    exact history.recordPermanent t statement record (t + 1) le_rfl
  · apply Set.disjoint_left.mpr
    intro statement surviving record
    have enrolled := ((history.semanticAt_spec t statement).mp surviving.1).1
    exact (Nat.not_lt_of_ge enrolled) (history.recordNew t statement record)
  · exact history.recordQuota t

/-- Both clerk inequalities for every finite tick, allowing infinite semantic
snapshots, migration sets, and record batches. No countability, finite grading,
order on grades, or upper-closure assumption is needed for these bounds. -/
theorem clerk_inequality {Statement Grade : Type*} {r : Nat}
    (history : SetClerkHistory Statement Grade r) (hr : 1 <= r) (t : Nat) :
    (r : ENat) * cumulativeMigrations history t <= (history.semanticAt t).encard /\
      (history.semanticAt 0).encard + ((r - 1 : Nat) : ENat) *
        cumulativeMigrations history t <= (history.semanticAt t).encard := by
  constructor
  · calc
      (r : ENat) * cumulativeMigrations history t =
          ∑ i ∈ Finset.range t, (r : ENat) * (history.migrationsAt i).encard :=
        Finset.mul_sum ..
      _ <= ∑ i ∈ Finset.range t, (history.recordsAt i).encard :=
        Finset.sum_le_sum (fun i _ => history.recordQuota i)
      _ <= (history.semanticAt t).encard := cumulative_record_bound history t
  · exact cumulative_step_bound (fun i => (history.semanticAt i).encard)
      (fun i => (history.migrationsAt i).encard) r t (history_step_bound history hr)

/-- Coerce the frozen finite certificate into its arbitrary-set counterpart. -/
def ofFinite {Statement Grade : Type*} {r : Nat}
    (history : ClerkInequality.ClerkHistory Statement Grade r) :
    SetClerkHistory Statement Grade r where
  toLedgerHistory := history.toLedgerHistory
  theoremGrade := history.theoremGrade
  semanticAt := fun t => history.semanticAt t
  semanticAt_spec := history.semanticAt_spec
  migrationsAt := fun t => history.migrationsAt t
  migrationsAt_spec := history.migrationsAt_spec
  recordsAt := fun t => history.recordsAt t
  recordNew := history.recordNew
  recordPermanent := history.recordPermanent
  recordQuota := by
    intro t
    simpa using (Nat.cast_le.mpr (history.recordQuota t) :
      ((r * (history.migrationsAt t).card : Nat) : ENat) <=
        ((history.recordsAt t).card : ENat))

/-- The exact two Nat conclusions of the frozen finite owner, now obtained
from the general-carrier theorem through the finite-set coercion. -/
theorem finite_clerk_inequality {Statement Grade : Type*} {r : Nat}
    (history : ClerkInequality.ClerkHistory Statement Grade r) (hr : 1 <= r) (t : Nat) :
    r * ClerkInequality.cumulativeMigrations history t <= (history.semanticAt t).card /\
      (history.semanticAt 0).card + (r - 1) *
        ClerkInequality.cumulativeMigrations history t <= (history.semanticAt t).card := by
  have general := clerk_inequality (ofFinite history) hr t
  simp only [cumulativeMigrations, ofFinite, Set.encard_coe_eq_coe_finsetCard] at general
  have totals : (∑ i ∈ Finset.range t, ((history.migrationsAt i).card : ENat)) =
      (ClerkInequality.cumulativeMigrations history t : ENat) := by
    simp only [ClerkInequality.cumulativeMigrations, Nat.cast_sum]
  rw [totals] at general
  constructor
  · exact_mod_cast general.1
  · exact_mod_cast general.2

example : Nonempty (SetClerkHistory Unit Unit 1) :=
  ⟨ofFinite ClerkInequality.emptyClerkHistory⟩

example : 1 <= (1 : Nat) := le_rfl

end D5.S0.History.Accounting.GeneralCarrierClerkInequality

#print axioms D5.S0.History.Accounting.GeneralCarrierClerkInequality.clerk_inequality
#print axioms D5.S0.History.Accounting.GeneralCarrierClerkInequality.finite_clerk_inequality
