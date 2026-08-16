/- GID: D5/S3/Observer/Separation/FiniteFutureCongruence
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/FiniteFutureCongruence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite future refinement stabilizes at the maximal invariant observation congruence. -/

import D5.S1.Dynamics.KnasterTarski
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Function.Iterate

/- Library-search audit trail (2026-08-16):
   * The repository theorem `knaster_tarski_extremal_fixed_points` is the exact
     fixed-point extremality result needed below and is imported and applied.
   * Loogle query `OrderHom.gfp` returned Mathlib's exact `OrderHom.gfp`,
     `OrderHom.map_gfp`, and `OrderHom.isGreatest_gfp` declarations underlying
     that repository theorem.
   * Loogle searches for finite antitone-relation stabilization and for a
     finite-supremum separation-time package found no exact result.
   * LeanSearch's shaped greatest-fixed-point query returned an HTML search
     page but no matching theorem result. Repository and pinned-Mathlib shape
     searches found no theorem combining every clause proved here. -/

namespace D5.S3.Observer.Separation.FiniteFutureCongruence

/-- A binary relation represented as a set of ordered state pairs. -/
abbrev StateRelation (Y : Type*) := Set (Y × Y)

/-- The observation after exactly `k` update steps. -/
def observedAt {Y O : Type*} (tau : Y -> Y) (q : Y -> O)
    (k : Nat) (y : Y) : O :=
  q ((tau^[k]) y)

/-- States having equal observations through the stated finite horizon. -/
def finiteFutureRelation {Y O : Type*} (tau : Y -> Y) (q : Y -> O)
    (horizon : Nat) : StateRelation Y :=
  {pair | forall k, k ≤ horizon ->
    observedAt tau q k pair.1 = observedAt tau q k pair.2}

/-- States having equal observations at every finite future time. -/
def infiniteFutureRelation {Y O : Type*} (tau : Y -> Y) (q : Y -> O) :
    StateRelation Y :=
  {pair | forall k,
    observedAt tau q k pair.1 = observedAt tau q k pair.2}

/-- Equality of the current observation. -/
def observationKernel {Y O : Type*} (q : Y -> O) : StateRelation Y :=
  {pair | q pair.1 = q pair.2}

/-- Retain the current observation kernel and pull a relation back one step. -/
def refinementOperator {Y O : Type*} (tau : Y -> Y) (q : Y -> O) :
    StateRelation Y →o StateRelation Y where
  toFun relation :=
    {pair | q pair.1 = q pair.2 /\ (tau pair.1, tau pair.2) ∈ relation}
  monotone' := by
    intro first second h pair hp
    exact ⟨hp.1, h hp.2⟩

/-- The first time at which a pair can be separated, or zero if it never is. -/
noncomputable def separationTime {Y O : Type*} (tau : Y -> Y) (q : Y -> O)
    (pair : Y × Y) : Nat := by
  classical
  exact if h : exists k,
    observedAt tau q k pair.1 ≠ observedAt tau q k pair.2 then
      Nat.find h
    else
      0

/-- The latest first-separation time among all pairs of a finite carrier. -/
noncomputable def stabilizationIndex {Y O : Type*} [Fintype Y]
    (tau : Y -> Y) (q : Y -> O) : Nat :=
  Finset.univ.sup (separationTime tau q)

private theorem separation_time_spec {Y O : Type*} (tau : Y -> Y) (q : Y -> O)
    (pair : Y × Y)
    (h : exists k,
      observedAt tau q k pair.1 ≠ observedAt tau q k pair.2) :
    observedAt tau q (separationTime tau q pair) pair.1 ≠
      observedAt tau q (separationTime tau q pair) pair.2 := by
  classical
  simp only [separationTime, dif_pos h]
  exact Nat.find_spec h

private theorem separation_time_le_stabilization {Y O : Type*} [Fintype Y]
    (tau : Y -> Y) (q : Y -> O) (pair : Y × Y) :
    separationTime tau q pair ≤ stabilizationIndex tau q := by
  exact Finset.le_sup (Finset.mem_univ pair)

theorem finite_relation_succ {Y O : Type*} (tau : Y -> Y) (q : Y -> O)
    (m : Nat) :
    finiteFutureRelation tau q (m + 1) =
      refinementOperator tau q (finiteFutureRelation tau q m) := by
  ext pair
  change
    (forall k, k ≤ m + 1 ->
      observedAt tau q k pair.1 = observedAt tau q k pair.2) ↔
    q pair.1 = q pair.2 /\
      (forall k, k ≤ m ->
        observedAt tau q k (tau pair.1) = observedAt tau q k (tau pair.2))
  constructor
  · intro h
    constructor
    · simpa [observedAt] using h 0 (Nat.zero_le _)
    · intro k hk
      simpa [observedAt, Function.iterate_succ_apply] using
        h (k + 1) (Nat.add_le_add_right hk 1)
  · rintro ⟨hcurrent, hfuture⟩ k hk
    cases k with
    | zero => simpa [observedAt] using hcurrent
    | succ k =>
        have hk' : k ≤ m := Nat.le_of_succ_le_succ (by simpa using hk)
        simpa [observedAt, Function.iterate_succ_apply] using hfuture k hk'

theorem finite_relation_zero {Y O : Type*} (tau : Y -> Y) (q : Y -> O) :
    finiteFutureRelation tau q 0 = observationKernel q := by
  ext pair
  change
    (forall k, k ≤ 0 ->
      observedAt tau q k pair.1 = observedAt tau q k pair.2) ↔
    q pair.1 = q pair.2
  constructor
  · intro h
    simpa [observedAt] using h 0 le_rfl
  · intro h k hk
    have : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    simpa [observedAt] using h

theorem infinite_relation_as_intersection {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) :
    infiniteFutureRelation tau q = ⋂ m, finiteFutureRelation tau q m := by
  ext pair
  simp only [infiniteFutureRelation, Set.mem_iInter, finiteFutureRelation]
  constructor
  · intro h m k hk
    exact h k
  · intro h k
    exact h k k le_rfl

theorem infinite_relation_stabilizes {Y O : Type*} [Fintype Y]
    (tau : Y -> Y) (q : Y -> O) :
    infiniteFutureRelation tau q =
      finiteFutureRelation tau q (stabilizationIndex tau q) := by
  ext pair
  change
    (forall k, observedAt tau q k pair.1 = observedAt tau q k pair.2) ↔
      forall k, k ≤ stabilizationIndex tau q ->
        observedAt tau q k pair.1 = observedAt tau q k pair.2
  constructor
  · intro h k hk
    exact h k
  · intro h k
    by_contra hne
    have hseparates : exists n,
        observedAt tau q n pair.1 ≠ observedAt tau q n pair.2 :=
      ⟨k, hne⟩
    exact separation_time_spec tau q pair hseparates
      (h (separationTime tau q pair)
        (separation_time_le_stabilization tau q pair))

theorem infinite_relation_equivalence {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) :
    Equivalence (fun y y' => (y, y') ∈ infiniteFutureRelation tau q) := by
  constructor
  · intro y k
    rfl
  · intro y y' h k
    exact (h k).symm
  · intro y y' y'' hxy hyz k
    exact (hxy k).trans (hyz k)

theorem infinite_relation_below_kernel {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) :
    infiniteFutureRelation tau q ≤ observationKernel q := by
  intro pair h
  simpa [observationKernel, observedAt] using h 0

theorem infinite_relation_invariant {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) :
    forall pair, pair ∈ infiniteFutureRelation tau q ->
      (tau pair.1, tau pair.2) ∈ infiniteFutureRelation tau q := by
  intro pair h k
  simpa [observedAt, Function.iterate_succ_apply] using h (k + 1)

theorem relation_le_infinite {Y O : Type*} (tau : Y -> Y) (q : Y -> O)
    (relation : StateRelation Y)
    (belowKernel : relation ≤ observationKernel q)
    (invariant : forall pair, pair ∈ relation ->
      (tau pair.1, tau pair.2) ∈ relation) :
    relation ≤ infiniteFutureRelation tau q := by
  intro pair hp k
  have hiter : ((tau^[k]) pair.1, (tau^[k]) pair.2) ∈ relation := by
    induction k with
    | zero => simpa using hp
    | succ k ih =>
        simpa only [Function.iterate_succ_apply'] using invariant _ ih
  simpa [observationKernel, observedAt] using belowKernel hiter

/-- Once two consecutive finite relations agree, that relation already equals
the infinite-future relation. -/
theorem finite_relation_eq_infinite_of_stable {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) (n : Nat)
    (stable : finiteFutureRelation tau q n =
      finiteFutureRelation tau q (n + 1)) :
    finiteFutureRelation tau q n = infiniteFutureRelation tau q := by
  apply le_antisymm
  · apply relation_le_infinite tau q (finiteFutureRelation tau q n)
    · intro pair hp
      simpa [observationKernel, observedAt] using hp 0 (Nat.zero_le n)
    · intro pair hp
      have hpNext : pair ∈ finiteFutureRelation tau q (n + 1) := by
        rw [← stable]
        exact hp
      have hpRefined : pair ∈
          refinementOperator tau q (finiteFutureRelation tau q n) := by
        rw [← finite_relation_succ tau q n]
        exact hpNext
      exact hpRefined.2
  · intro pair hp k hk
    exact hp k

/-- The explicit latest first-separation index is the least index at which two
consecutive finite relations can agree. -/
theorem stabilization_index_le_of_stable {Y O : Type*} [Fintype Y]
    (tau : Y -> Y) (q : Y -> O) (n : Nat)
    (stable : finiteFutureRelation tau q n =
      finiteFutureRelation tau q (n + 1)) :
    stabilizationIndex tau q ≤ n := by
  classical
  apply Finset.sup_le
  intro pair hpair
  by_cases hseparates : exists k,
      observedAt tau q k pair.1 ≠ observedAt tau q k pair.2
  · by_contra hnotle
    have hnlt : n < separationTime tau q pair := Nat.lt_of_not_ge hnotle
    have hfinite : pair ∈ finiteFutureRelation tau q n := by
      intro k hk
      have hklt : k < separationTime tau q pair := lt_of_le_of_lt hk hnlt
      have hnot :
          ¬ observedAt tau q k pair.1 ≠ observedAt tau q k pair.2 := by
        apply Nat.find_min hseparates
        simpa [separationTime, hseparates] using hklt
      by_contra hneq
      exact hnot hneq
    have hinfinite : pair ∈ infiniteFutureRelation tau q := by
      rw [← finite_relation_eq_infinite_of_stable tau q n stable]
      exact hfinite
    exact separation_time_spec tau q pair hseparates
      (hinfinite (separationTime tau q pair))
  · simp [separationTime, hseparates]

theorem infinite_relation_eq_gfp {Y O : Type*} (tau : Y -> Y) (q : Y -> O) :
    infiniteFutureRelation tau q = (refinementOperator tau q).gfp := by
  let operator := refinementOperator tau q
  have hfixed : operator (infiniteFutureRelation tau q) =
      infiniteFutureRelation tau q := by
    ext pair
    change
      (q pair.1 = q pair.2 /\
        forall k,
          observedAt tau q k (tau pair.1) = observedAt tau q k (tau pair.2)) ↔
      forall k, observedAt tau q k pair.1 = observedAt tau q k pair.2
    constructor
    · rintro ⟨hcurrent, hfuture⟩ k
      cases k with
      | zero => simpa [observedAt] using hcurrent
      | succ k =>
          simpa [observedAt, Function.iterate_succ_apply] using hfuture k
    · intro h
      exact ⟨by simpa [observedAt] using h 0,
        fun k => by
          simpa [observedAt, Function.iterate_succ_apply] using h (k + 1)⟩
  have hExtrema :=
    D5.S1.Dynamics.KnasterTarski.knaster_tarski_extremal_fixed_points operator
  apply le_antisymm
  · exact hExtrema.2.2 hfixed
  · apply relation_le_infinite tau q operator.gfp
    · intro pair hp
      have hp' : pair ∈ operator operator.gfp := by
        rw [hExtrema.2.1]
        exact hp
      exact hp'.1
    · intro pair hp
      have hp' : pair ∈ operator operator.gfp := by
        rw [hExtrema.2.1]
        exact hp
      exact hp'.2

/-- The complete collection of finite-refinement, stabilization, congruence,
and greatest-fixed-point clauses. -/
structure FiniteFutureCongruenceLaws {Y O : Type*} [Fintype Y]
    (tau : Y -> Y) (q : Y -> O) : Prop where
  recursion : forall m,
    finiteFutureRelation tau q (m + 1) =
      refinementOperator tau q (finiteFutureRelation tau q m)
  base : finiteFutureRelation tau q 0 = observationKernel q
  intersection : infiniteFutureRelation tau q =
    ⋂ m, finiteFutureRelation tau q m
  finiteStabilization : infiniteFutureRelation tau q =
    finiteFutureRelation tau q (stabilizationIndex tau q)
  equivalence : Equivalence
    (fun y y' => (y, y') ∈ infiniteFutureRelation tau q)
  belowKernel : infiniteFutureRelation tau q ≤ observationKernel q
  invariant : forall pair, pair ∈ infiniteFutureRelation tau q ->
    (tau pair.1, tau pair.2) ∈ infiniteFutureRelation tau q
  maximal : forall relation : StateRelation Y,
    relation ≤ observationKernel q ->
    (forall pair, pair ∈ relation -> (tau pair.1, tau pair.2) ∈ relation) ->
    relation ≤ infiniteFutureRelation tau q
  greatestFixedPoint : infiniteFutureRelation tau q =
    (refinementOperator tau q).gfp

/-- Finite future refinement stabilizes at the largest observation-kernel
equivalence preserved by the update, namely the refinement operator's greatest
fixed point. -/
theorem finite_future_maximal_congruence {Y O : Type*} [Fintype Y]
    (tau : Y -> Y) (q : Y -> O) :
    FiniteFutureCongruenceLaws tau q := by
  exact {
    recursion := finite_relation_succ tau q
    base := finite_relation_zero tau q
    intersection := infinite_relation_as_intersection tau q
    finiteStabilization := infinite_relation_stabilizes tau q
    equivalence := infinite_relation_equivalence tau q
    belowKernel := infinite_relation_below_kernel tau q
    invariant := infinite_relation_invariant tau q
    maximal := relation_le_infinite tau q
    greatestFixedPoint := infinite_relation_eq_gfp tau q
  }

/-- The theorem's finite-domain hypotheses and nontrivial conclusion have a
concrete two-state witness. -/
example :
    let tau : Bool -> Bool := Bool.not
    let q : Bool -> Bool := id
    FiniteFutureCongruenceLaws tau q /\
      (false, true) ∉ infiniteFutureRelation tau q := by
  dsimp
  exact ⟨finite_future_maximal_congruence Bool.not id,
    fun h => Bool.noConfusion (h 0)⟩

end D5.S3.Observer.Separation.FiniteFutureCongruence
