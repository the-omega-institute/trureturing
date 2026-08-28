/- GID: D5/S3/Observer/Budget/MinimumCompleteSetCover
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/MinimumCompleteSetCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite observer completeness is minimum set cover, including degenerate cases. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * Repository searches found the exact canonical dependent-product primitive
     `jointReadout` and reuse it below rather than introducing a second readout.
   * `FiniteExperimentCoverCriterion` covers unordered target-relative pairs with
     baseline evidence, but does not expose the ordered distinct-pair universe,
     observer separation sets, costs, or minimum complete budgets required here.
   * Pinned-Mathlib searches found `Set.mem_iUnion`, `Set.iUnion_of_empty`, and
     `Finset.sum_erase_add`; no exact theorem packages injectivity, separation cover,
     and natural-number minimum cost. The local smart-search script found no exact hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.MinimumCompleteSetCover

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w

/- 卷内该条截断,定义由本模块补齐: the three definitions below reconstruct the
ordered state-pair universe, each observer's separation set, and its supplied cost. -/

/-- The ordered pairs of distinct states that a complete budget must distinguish. -/
def statePairUniverse (X : Type v) : Set (X × X) :=
  {pair | pair.1 ≠ pair.2}

/-- The distinct ordered state pairs separated by observer `i`. -/
def observerSeparationSet {ι : Type u} {X : Type v} {V : ι → Type w}
    (q : ∀ i, X → V i) (i : ι) : Set (X × X) :=
  {pair | pair.1 ≠ pair.2 ∧ q i pair.1 ≠ q i pair.2}

/-- The natural-number cost supplied for observer `i`. -/
def observerCost {ι : Type u} (c : ι → Nat) (i : ι) : Nat :=
  c i

/-- The total cost of a finite observer budget. -/
def budgetCost {ι : Type u} (J : Finset ι) (c : ι → Nat) : Nat :=
  ∑ i ∈ J, observerCost c i

/-- A finite budget is complete and has no greater cost than any complete budget. -/
def IsMinimumCompleteBudget {ι : Type u} {X : Type v} {V : ι → Type w}
    (J : Finset ι) (q : ∀ i, X → V i) (c : ι → Nat) : Prop :=
  Function.Injective
      (jointReadout (fun i : {candidate // candidate ∈ J} => q i.1)) ∧
    ∀ K : Finset ι,
      Function.Injective
          (jointReadout (fun i : {candidate // candidate ∈ K} => q i.1)) →
        budgetCost J c ≤ budgetCost K c

/-- A finite selected family is injective exactly when its separation sets cover
all distinct ordered state pairs. The word "prime" in the source title only
specializes the observer index type and supplies no hypothesis used here. -/
theorem finite_budget_injective_iff_cover
    {ι : Type u} {X : Type v} {V : ι → Type w}
    (J : Finset ι) (q : ∀ i, X → V i) :
    Function.Injective
        (jointReadout (fun i : {candidate // candidate ∈ J} => q i.1)) ↔
      (⋃ i, ⋃ _ : i ∈ J, observerSeparationSet q i) = statePairUniverse X := by
  constructor
  · intro injective
    apply Set.Subset.antisymm
    · intro pair covered
      obtain ⟨i, covered⟩ := Set.mem_iUnion.mp covered
      obtain ⟨hi, separated⟩ := Set.mem_iUnion.mp covered
      change pair.1 ≠ pair.2 ∧ q i pair.1 ≠ q i pair.2 at separated
      exact separated.1
    · intro pair distinct
      change pair.1 ≠ pair.2 at distinct
      by_contra notCovered
      have sameReadout :
          jointReadout (fun i : {candidate // candidate ∈ J} => q i.1) pair.1 =
            jointReadout (fun i : {candidate // candidate ∈ J} => q i.1) pair.2 := by
        funext selected
        by_contra different
        apply notCovered
        apply Set.mem_iUnion.mpr
        refine ⟨selected.1, ?_⟩
        apply Set.mem_iUnion.mpr
        refine ⟨selected.2, ?_⟩
        change pair.1 ≠ pair.2 ∧
          q selected.1 pair.1 ≠ q selected.1 pair.2
        exact ⟨distinct, different⟩
      exact distinct (injective sameReadout)
  · intro covers x y sameReadout
    by_contra distinct
    have inUniverse : (x, y) ∈ statePairUniverse X := distinct
    have covered :
        (x, y) ∈ ⋃ i, ⋃ _ : i ∈ J, observerSeparationSet q i := by
      rw [covers]
      exact inUniverse
    obtain ⟨i, covered⟩ := Set.mem_iUnion.mp covered
    obtain ⟨hi, separated⟩ := Set.mem_iUnion.mp covered
    change x ≠ y ∧ q i x ≠ q i y at separated
    exact separated.2 (congrFun sameReadout ⟨i, hi⟩)
#print axioms finite_budget_injective_iff_cover

/-- Minimum complete budgets are exactly minimum-cost covers of the distinct-pair
universe. No existence claim is made, so neither the observer type nor the state
space needs a finiteness assumption. -/
theorem minimum_complete_budget_iff_minimum_cover
    {ι : Type u} {X : Type v} {V : ι → Type w}
    (J : Finset ι) (q : ∀ i, X → V i) (c : ι → Nat) :
    IsMinimumCompleteBudget J q c ↔
      (⋃ i, ⋃ _ : i ∈ J, observerSeparationSet q i) = statePairUniverse X ∧
        ∀ K : Finset ι,
          (⋃ i, ⋃ _ : i ∈ K, observerSeparationSet q i) = statePairUniverse X →
            budgetCost J c ≤ budgetCost K c := by
  constructor
  · intro minimum
    refine ⟨(finite_budget_injective_iff_cover J q).mp minimum.1, ?_⟩
    intro K covers
    exact minimum.2 K ((finite_budget_injective_iff_cover K q).mpr covers)
  · rintro ⟨covers, minimum⟩
    refine ⟨(finite_budget_injective_iff_cover J q).mpr covers, ?_⟩
    intro K complete
    exact minimum K ((finite_budget_injective_iff_cover K q).mp complete)
#print axioms minimum_complete_budget_iff_minimum_cover

/-- One pair of distinct states with equal selected readouts certifies
incompleteness. -/
theorem counterexample_certifies_incomplete_budget
    {ι : Type u} {X : Type v} {V : ι → Type w}
    (J : Finset ι) (q : ∀ i, X → V i) :
    (∃ x y, x ≠ y ∧
        jointReadout (fun i : {candidate // candidate ∈ J} => q i.1) x =
          jointReadout (fun i : {candidate // candidate ∈ J} => q i.1) y) →
      ¬Function.Injective
        (jointReadout (fun i : {candidate // candidate ∈ J} => q i.1)) := by
  rintro ⟨x, y, distinct, sameReadout⟩ injective
  exact distinct (injective sameReadout)
#print axioms counterexample_certifies_incomplete_budget

/-- An injective selected readout supplies a selected observer separating every
distinct ordered state pair. -/
theorem injective_budget_covers_every_distinct_pair
    {ι : Type u} {X : Type v} {V : ι → Type w}
    (J : Finset ι) (q : ∀ i, X → V i)
    (injective : Function.Injective
      (jointReadout (fun i : {candidate // candidate ∈ J} => q i.1))) :
    ∀ pair ∈ statePairUniverse X,
      ∃ i ∈ J, pair ∈ observerSeparationSet q i := by
  intro pair distinct
  have covered :
      pair ∈ ⋃ i, ⋃ _ : i ∈ J, observerSeparationSet q i := by
    rw [finite_budget_injective_iff_cover J q |>.mp injective]
    exact distinct
  obtain ⟨i, covered⟩ := Set.mem_iUnion.mp covered
  obtain ⟨hi, separated⟩ := Set.mem_iUnion.mp covered
  exact ⟨i, hi, separated⟩
#print axioms injective_budget_covers_every_distinct_pair

/-- The empty budget is complete exactly when there are no distinct state pairs. -/
theorem empty_budget_injective_iff_pair_universe_empty
    {ι : Type u} {X : Type v} {V : ι → Type w}
    (q : ∀ i, X → V i) :
    Function.Injective
        (jointReadout
          (fun i : {candidate // candidate ∈ (∅ : Finset ι)} => q i.1)) ↔
      statePairUniverse X = ∅ := by
  rw [finite_budget_injective_iff_cover (∅ : Finset ι) q]
  simpa using (eq_comm : (∅ : Set (X × X)) = statePairUniverse X ↔ _)
#print axioms empty_budget_injective_iff_pair_universe_empty

/-- For `n = 0`, the state space `Fin n` has empty pair universe and the empty
budget is complete. -/
theorem fin_zero_empty_budget_complete
    {ι : Type u} {V : ι → Type w}
    (q : ∀ i, Fin 0 → V i) :
    statePairUniverse (Fin 0) = ∅ ∧
      Function.Injective
        (jointReadout
          (fun i : {candidate // candidate ∈ (∅ : Finset ι)} => q i.1)) := by
  constructor
  · ext pair
    exact Fin.elim0 pair.1
  · intro x y
    exact Fin.elim0 x
#print axioms fin_zero_empty_budget_complete

/-- A singleton state space also has empty pair universe and a complete empty
budget. -/
theorem singleton_empty_budget_complete
    {ι : Type u} {V : ι → Type w}
    (q : ∀ i, Unit → V i) :
    statePairUniverse Unit = ∅ ∧
      Function.Injective
        (jointReadout
          (fun i : {candidate // candidate ∈ (∅ : Finset ι)} => q i.1)) := by
  constructor
  · ext pair
    simp [statePairUniverse]
  · intro x y _
    exact Subsingleton.elim x y
#print axioms singleton_empty_budget_complete

/-- Every constant observer has empty separation set. -/
theorem constant_observer_separation_set_empty
    {ι : Type u} {X : Type v} {V : ι → Type w}
    (value : ∀ i, V i) (i : ι) :
    observerSeparationSet (fun j (_ : X) => value j) i = ∅ := by
  ext pair
  simp [observerSeparationSet]
#print axioms constant_observer_separation_set_empty

/-- One identity observer is a complete finite budget on every state space. -/
theorem identity_observer_singleton_budget_complete (X : Type v) :
    Function.Injective
        (jointReadout
          (fun _ : {candidate // candidate ∈ ({()} : Finset Unit)} =>
            (id : X → X))) ∧
      (⋃ i, ⋃ _ : i ∈ ({()} : Finset Unit),
          observerSeparationSet (fun _ : Unit => (id : X → X)) i) =
        statePairUniverse X := by
  have injective : Function.Injective
      (jointReadout
        (fun _ : {candidate // candidate ∈ ({()} : Finset Unit)} =>
          (id : X → X))) := by
    intro x y sameReadout
    exact congrFun sameReadout ⟨(), by simp⟩
  exact ⟨injective,
    (finite_budget_injective_iff_cover
      ({()} : Finset Unit) (fun _ : Unit => (id : X → X))).mp injective⟩
#print axioms identity_observer_singleton_budget_complete

/-- The singleton zero observer on `Nat` separates no pair and is incomplete. -/
theorem zero_observer_singleton_budget_incomplete_on_nat :
    observerSeparationSet (fun _ : Unit => fun _ : Nat => 0) () = ∅ ∧
      ¬Function.Injective
        (jointReadout
          (fun _ : {candidate // candidate ∈ ({()} : Finset Unit)} =>
            fun _ : Nat => 0)) := by
  constructor
  · exact constant_observer_separation_set_empty (fun _ : Unit => 0) ()
  · intro injective
    exact Nat.zero_ne_one (injective rfl)
#print axioms zero_observer_singleton_budget_incomplete_on_nat

/-- With zero costs, minimum completeness reduces exactly to completeness. -/
theorem zero_cost_budget_minimum_iff_complete
    {ι : Type u} {X : Type v} {V : ι → Type w}
    (J : Finset ι) (q : ∀ i, X → V i) :
    IsMinimumCompleteBudget J q (fun _ => 0) ↔
      Function.Injective
        (jointReadout (fun i : {candidate // candidate ∈ J} => q i.1)) := by
  constructor
  · exact fun minimum => minimum.1
  · intro complete
    refine ⟨complete, ?_⟩
    intro K _
    simp [budgetCost, observerCost]
#print axioms zero_cost_budget_minimum_iff_complete

/-- An observer with empty separation set can be erased from a minimum budget
without losing minimum completeness. -/
theorem empty_separation_observer_removal_preserves_minimum
    {ι : Type u} {X : Type v} {V : ι → Type w} [DecidableEq ι]
    (J : Finset ι) (q : ∀ i, X → V i) (c : ι → Nat) (i : ι)
    (emptySeparation : observerSeparationSet q i = ∅)
    (minimum : IsMinimumCompleteBudget J q c) :
    IsMinimumCompleteBudget (J.erase i) q c := by
  have coverErase :
      (⋃ j, ⋃ _ : j ∈ J.erase i, observerSeparationSet q j) =
        ⋃ j, ⋃ _ : j ∈ J, observerSeparationSet q j := by
    apply Set.Subset.antisymm
    · intro pair covered
      obtain ⟨j, covered⟩ := Set.mem_iUnion.mp covered
      obtain ⟨hj, separated⟩ := Set.mem_iUnion.mp covered
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      apply Set.mem_iUnion.mpr
      exact ⟨Finset.mem_of_mem_erase hj, separated⟩
    · intro pair covered
      obtain ⟨j, covered⟩ := Set.mem_iUnion.mp covered
      obtain ⟨hj, separated⟩ := Set.mem_iUnion.mp covered
      by_cases same : j = i
      · subst j
        rw [emptySeparation] at separated
        exact separated.elim
      · apply Set.mem_iUnion.mpr
        refine ⟨j, ?_⟩
        apply Set.mem_iUnion.mpr
        exact ⟨Finset.mem_erase.mpr ⟨same, hj⟩, separated⟩
  have erasedCostLe : budgetCost (J.erase i) c ≤ budgetCost J c := by
    by_cases hi : i ∈ J
    · have sumDecomposition :
          budgetCost (J.erase i) c + observerCost c i = budgetCost J c := by
        simpa [budgetCost] using J.sum_erase_add (observerCost c) hi
      omega
    · rw [Finset.erase_eq_self.mpr hi]
  refine ⟨?_, ?_⟩
  · apply (finite_budget_injective_iff_cover (J.erase i) q).mpr
    rw [coverErase]
    exact (finite_budget_injective_iff_cover J q).mp minimum.1
  · intro K complete
    exact erasedCostLe.trans (minimum.2 K complete)
#print axioms empty_separation_observer_removal_preserves_minimum

/-- The empty-separation premise is necessary: deleting the sole useful identity
observer destroys minimum completeness, even when every cost is zero. -/
theorem empty_separation_hypothesis_is_necessary :
    let J : Finset Unit := {()}
    let q : Unit → Bool → Bool := fun _ => id
    let c : Unit → Nat := fun _ => 0
    IsMinimumCompleteBudget J q c ∧
      observerSeparationSet q () ≠ ∅ ∧
        ¬IsMinimumCompleteBudget (J.erase ()) q c := by
  dsimp only
  have injective : Function.Injective
      (jointReadout
        (fun _ : {candidate // candidate ∈ ({()} : Finset Unit)} =>
          (id : Bool → Bool))) := by
    intro x y sameReadout
    exact congrFun sameReadout ⟨(), by simp⟩
  refine ⟨(zero_cost_budget_minimum_iff_complete _ _).mpr injective, ?_, ?_⟩
  · intro emptySeparation
    have separated :
        (false, true) ∈
          observerSeparationSet (fun _ : Unit => (id : Bool → Bool)) () := by
      simp [observerSeparationSet]
    rw [emptySeparation] at separated
    exact separated
  · intro erasedMinimum
    apply Bool.false_ne_true
    apply erasedMinimum.1
    funext selected
    have different : selected.1 ≠ () := (Finset.mem_erase.mp selected.2).1
    exact (different (Subsingleton.elim selected.1 ())).elim
#print axioms empty_separation_hypothesis_is_necessary

/-- The starting-minimum premise is necessary: after erasing a useless observer,
an expensive identity observer can still be dominated by a cheaper identity observer. -/
theorem minimum_budget_hypothesis_is_necessary :
    let q : Fin 3 → Bool → Bool := fun i =>
      if i = 0 then fun _ => false else id
    let c : Fin 3 → Nat := fun i => if i = 1 then 2 else if i = 2 then 1 else 0
    let J : Finset (Fin 3) := {0, 1}
    observerSeparationSet q 0 = ∅ ∧
      ¬IsMinimumCompleteBudget (J.erase 0) q c := by
  dsimp only
  constructor
  · ext pair
    simp [observerSeparationSet]
  · intro minimum
    have cheapComplete : Function.Injective
        (jointReadout
          (fun i : {candidate // candidate ∈ ({2} : Finset (Fin 3))} =>
            (if i.1 = 0 then fun _ : Bool => false else id))) := by
      intro x y sameReadout
      have atTwo := congrFun sameReadout ⟨2, by simp⟩
      simpa [jointReadout] using atTwo
    have costBound := minimum.2 ({2} : Finset (Fin 3)) cheapComplete
    have twoNeOne : (2 : Fin 3) ≠ 1 := by decide
    simp [budgetCost, observerCost, twoNeOne] at costBound
#print axioms minimum_budget_hypothesis_is_necessary

end D5.S3.Observer.Budget.MinimumCompleteSetCover
