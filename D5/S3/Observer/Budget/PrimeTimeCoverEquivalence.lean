/- GID: D5/S3/Observer/Budget/PrimeTimeCoverEquivalence
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/PrimeTimeCoverEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Timed injectivity equals prefix cover, with all required degenerate cases audited. -/

import D5.S3.Observer.Budget.MinimumCompleteSetCover
import D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/- Library-search audit trail (2026-08-25):
   * Exact D5 hit `finite_budget_injective_iff_cover` supplies the cover equivalence;
     the proof below applies it to finite observer-time coordinates rather than reproving it.
   * Exact D5 hit `completeItinerary` supplies every iterated readout without a second trace.
   * `FinitePrimeTimeTomography` and `DependentFinitePrimeTimeTomography` only extract some
     finite separating window; neither states the fixed-budget, fixed-prefix equivalence here.
   * The FPOD digest index leaves theorem 27.1 residual-open. Pinned-Mathlib searches found
     `Function.iterate`, `Finset.product`, `Finset.range`, and `Set.iUnion`, but no exact
     theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.PrimeTimeCoverEquivalence

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.Observer.Budget.MinimumCompleteSetCover
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

universe u v w

/-- The readout of observer `i` after the state has evolved for `n` steps. -/
def timedReadout {ι : Type u} {X : Type v} {V : ι → Type w}
    (F : X → X) (q : ∀ i, X → V i) (coordinate : ι × Nat) : X → V coordinate.1 :=
  fun x => completeItinerary F (q coordinate.1) x coordinate.2

/-- The distinct ordered state pairs separated by observer `i` at time `n`. -/
def timedSeparationSet {ι : Type u} {X : Type v} {V : ι → Type w}
    (F : X → X) (q : ∀ i, X → V i) (i : ι) (n : Nat) : Set (X × X) :=
  observerSeparationSet (timedReadout F q) (i, n)

/-- The selected observer-time coordinates through and including depth `m`. -/
def timePrefixCoordinates {ι : Type u} (J : Finset ι) (m : Nat) : Finset (ι × Nat) :=
  J.product (Finset.range (m + 1))

/-- The dependent joint readout over all selected coordinates through depth `m`. -/
def timePrefixReadout {ι : Type u} {X : Type v} {V : ι → Type w}
    (F : X → X) (q : ∀ i, X → V i) (J : Finset ι) (m : Nat) :
    X → ∀ coordinate : {candidate // candidate ∈ timePrefixCoordinates J m},
      V coordinate.1.1 :=
  jointReadout fun coordinate => timedReadout F q coordinate.1

/-- The union of all separation sets selected by `i ∈ J` and `n ≤ m`. -/
def timePrefixCover {ι : Type u} {X : Type v} {V : ι → Type w}
    (F : X → X) (q : ∀ i, X → V i) (J : Finset ι) (m : Nat) : Set (X × X) :=
  ⋃ i, ⋃ _ : i ∈ J, ⋃ n, ⋃ _ : n ≤ m, timedSeparationSet F q i n

/-- A selected observer family through a fixed time depth is injective exactly when its
timed separation sets cover every distinct ordered state pair. No finiteness assumption on
the state or observer type is needed for this fixed finite budget. -/
theorem prime_time_budget_injective_iff_cover
    {ι : Type u} {X : Type v} {V : ι → Type w}
    (F : X → X) (q : ∀ i, X → V i) (J : Finset ι) (m : Nat) :
    Function.Injective (timePrefixReadout F q J m) ↔
      timePrefixCover F q J m = statePairUniverse X := by
  classical
  have cover_eq :
      (⋃ coordinate, ⋃ _ : coordinate ∈ timePrefixCoordinates J m,
          observerSeparationSet (timedReadout F q) coordinate) =
        timePrefixCover F q J m := by
    ext pair
    constructor
    · intro covered
      obtain ⟨coordinate, covered⟩ := Set.mem_iUnion.mp covered
      obtain ⟨coordinateMem, separated⟩ := Set.mem_iUnion.mp covered
      simp only [timePrefixCoordinates, Finset.mem_product, Finset.mem_range,
        Nat.lt_succ_iff] at coordinateMem
      refine Set.mem_iUnion.mpr ⟨coordinate.1, ?_⟩
      refine Set.mem_iUnion.mpr ⟨coordinateMem.1, ?_⟩
      refine Set.mem_iUnion.mpr ⟨coordinate.2, ?_⟩
      refine Set.mem_iUnion.mpr ⟨coordinateMem.2, ?_⟩
      simpa only [timedSeparationSet] using separated
    · intro covered
      obtain ⟨i, covered⟩ := Set.mem_iUnion.mp covered
      obtain ⟨hi, covered⟩ := Set.mem_iUnion.mp covered
      obtain ⟨n, covered⟩ := Set.mem_iUnion.mp covered
      obtain ⟨hn, separated⟩ := Set.mem_iUnion.mp covered
      refine Set.mem_iUnion.mpr ⟨(i, n), ?_⟩
      refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
      · simp only [timePrefixCoordinates, Finset.mem_product, Finset.mem_range,
          Nat.lt_succ_iff, hi, hn, and_self]
      · simpa only [timedSeparationSet] using separated
  unfold timePrefixReadout
  rw [finite_budget_injective_iff_cover, cover_eq]
#print axioms prime_time_budget_injective_iff_cover

private theorem time_prefix_cover_zero
    {ι : Type u} {X : Type v} {V : ι → Type w}
    (F : X → X) (q : ∀ i, X → V i) (J : Finset ι) :
    timePrefixCover F q J 0 =
      ⋃ i, ⋃ _ : i ∈ J, observerSeparationSet q i := by
  ext pair
  constructor
  · intro covered
    obtain ⟨i, covered⟩ := Set.mem_iUnion.mp covered
    obtain ⟨hi, covered⟩ := Set.mem_iUnion.mp covered
    obtain ⟨n, covered⟩ := Set.mem_iUnion.mp covered
    obtain ⟨hn, separated⟩ := Set.mem_iUnion.mp covered
    have n_zero : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    refine Set.mem_iUnion.mpr ⟨hi, ?_⟩
    simpa [timedSeparationSet, timedReadout, completeItinerary] using separated
  · intro separated
    obtain ⟨i, separated⟩ := Set.mem_iUnion.mp separated
    obtain ⟨hi, separated⟩ := Set.mem_iUnion.mp separated
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    refine Set.mem_iUnion.mpr ⟨hi, ?_⟩
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    refine Set.mem_iUnion.mpr ⟨Nat.le_refl 0, ?_⟩
    simpa [timedSeparationSet, timedReadout, completeItinerary] using separated

private theorem state_pair_universe_empty_iff_subsingleton (X : Type v) :
    statePairUniverse X = ∅ ↔ Subsingleton X := by
  constructor
  · intro emptyUniverse
    constructor
    intro x y
    by_contra distinct
    have pairMem : (x, y) ∈ statePairUniverse X := distinct
    rw [emptyUniverse] at pairMem
    exact pairMem
  · intro subsingleton
    ext pair
    constructor
    · intro distinct
      exact distinct (subsingleton.elim pair.1 pair.2)
    · intro emptyMem
      exact emptyMem.elim

-- Degenerate audit: at `m = 0`, the theorem is exactly the untimed budget theorem.
example {ι : Type u} {X : Type v} {V : ι → Type w}
    (F : X → X) (q : ∀ i, X → V i) (J : Finset ι) :
    Function.Injective (timePrefixReadout F q J 0) ↔
      Function.Injective
        (jointReadout (fun i : {candidate // candidate ∈ J} => q i.1)) := by
  rw [prime_time_budget_injective_iff_cover, finite_budget_injective_iff_cover,
    time_prefix_cover_zero]

-- Degenerate audit: an empty budget is complete exactly on a subsingleton state type.
example {ι : Type u} {X : Type v} {V : ι → Type w}
    (F : X → X) (q : ∀ i, X → V i) (m : Nat) :
    Function.Injective (timePrefixReadout F q (∅ : Finset ι) m) ↔ Subsingleton X := by
  rw [prime_time_budget_injective_iff_cover]
  have emptyCover : timePrefixCover F q (∅ : Finset ι) m = ∅ := by
    simp [timePrefixCover]
  rw [emptyCover, eq_comm, state_pair_universe_empty_iff_subsingleton]

-- Degenerate audit: the empty state type is separated by every timed budget.
example {ι : Type u} {V : ι → Type w}
    (F : Empty → Empty) (q : ∀ i, Empty → V i) (J : Finset ι) (m : Nat) :
    Function.Injective (timePrefixReadout F q J m) ∧
      timePrefixCover F q J m = statePairUniverse Empty := by
  have injective : Function.Injective (timePrefixReadout F q J m) := by
    intro x _ _
    exact x.elim
  exact ⟨injective, (prime_time_budget_injective_iff_cover F q J m).mp injective⟩

-- Degenerate audit: the singleton state type is separated by every timed budget.
example {ι : Type u} {V : ι → Type w}
    (F : Unit → Unit) (q : ∀ i, Unit → V i) (J : Finset ι) (m : Nat) :
    Function.Injective (timePrefixReadout F q J m) ∧
      timePrefixCover F q J m = statePairUniverse Unit := by
  have injective : Function.Injective (timePrefixReadout F q J m) := by
    intro x y _
    exact Subsingleton.elim x y
  exact ⟨injective, (prime_time_budget_injective_iff_cover F q J m).mp injective⟩

-- Degenerate audit: identity dynamics repeats the untimed separation set at every depth.
example {ι : Type u} {X : Type v} {V : ι → Type w}
    (q : ∀ i, X → V i) (i : ι) (n : Nat) :
    timedSeparationSet (id : X → X) q i n = observerSeparationSet q i := by
  ext pair
  simp [timedSeparationSet, timedReadout, completeItinerary, observerSeparationSet]

-- Degenerate audit: after one constant update, no observer separates any state pair.
example {ι : Type u} {X : Type v} {V : ι → Type w}
    (fixed : X) (q : ∀ i, X → V i) (i : ι) :
    timedSeparationSet (fun _ : X => fixed) q i 1 = ∅ := by
  ext pair
  simp [timedSeparationSet, timedReadout, completeItinerary, observerSeparationSet]

-- Degenerate audit: the zero readout separates no pair at any time.
example (F : Nat → Nat) (n : Nat) :
    timedSeparationSet F (fun _ : Unit => fun _ : Nat => 0) () n = ∅ := by
  ext pair
  simp [timedSeparationSet, timedReadout, completeItinerary, observerSeparationSet]

end D5.S3.Observer.Budget.PrimeTimeCoverEquivalence
