/- GID: D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite states admit bounded classifiers; empty and infinite cases are audited. -/

import D5.S3.Observer.Budget.MinimumCompleteSetCover

/- Library-search audit trail (2026-08-25):
   * The exact D5 `jointReadout`, `statePairUniverse`, and
     `finite_budget_injective_iff_cover` declarations are imported and reused.
   * The same budget module supplies the established empty, singleton, and
     constant-observer audits; the wrappers below expose the cases needed here.
   * Pinned Mathlib supplied `Finset.card_image_le` and
     `Infinite.exists_notMem_finset`; no exact finite-selection theorem was found.
   * `FiniteMarginalGlobalReadoutContrast.finite_index_readout_image_full` was
     checked. It concerns full measure of one canonical finite-index image, not
     injectivity of a state-indexed family, so importing that measure module would
     add no reusable proof dependency. This is the finite-state dual contrast to 120.1.
   * No prime parameter occurs, and no primality property is used. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.FinitePairwiseGlobalClassifier

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.Observer.Budget.MinimumCompleteSetCover

universe u v w

/-- A readout family separates points when every distinct pair has some
coordinate on which its readouts differ. The coordinate may depend on the pair. -/
def PairwiseSeparating {I : Type u} {X : Type v} {V : I → Type w}
    (q : ∀ i, X → V i) : Prop :=
  ∀ x y, x ≠ y → ∃ i, q i x ≠ q i y

/-- A finite global classifier is an injective joint readout on some finite
subfamily of coordinates. -/
def HasFiniteGlobalClassifier {I : Type u} {X : Type v} {V : I → Type w}
    (q : ∀ i, X → V i) : Prop :=
  ∃ J : Finset I,
    Function.Injective
      (jointReadout (fun i : {candidate // candidate ∈ J} => q i.1))

/-- The Boolean point readout at `i` recognizes exactly the natural number `i`. -/
def pointReadout (i x : Nat) : Bool :=
  decide (x = i)

/-- On a finite state type, one witness for each ordered distinct pair gives a
finite global classifier. Its size is at most the number of such pairs. Empty
and singleton state types have no distinct pairs, so this construction takes
`J = ∅` there. Neither the index type nor any output type must be finite. -/
theorem finite_pairwise_global_classifier_bounded
    {I : Type u} {X : Type v} {V : I → Type w} [Finite X]
    (q : ∀ i, X → V i) (separates : PairwiseSeparating q) :
    ∃ J : Finset I,
      J.card ≤ Nat.card ↥(statePairUniverse X) ∧
        Function.Injective
          (jointReadout (fun i : {candidate // candidate ∈ J} => q i.1)) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  let witness : ↥(statePairUniverse X) → I := fun pair =>
    Classical.choose (separates pair.1.1 pair.1.2 pair.2)
  let J : Finset I := Finset.univ.image witness
  refine ⟨J, ?_, ?_⟩
  · simpa [J, Nat.card_eq_fintype_card] using
      (Finset.card_image_le (s := (Finset.univ : Finset ↥(statePairUniverse X)))
        (f := witness))
  · apply (finite_budget_injective_iff_cover J q).mpr
    apply Set.Subset.antisymm
    · intro pair covered
      obtain ⟨i, covered⟩ := Set.mem_iUnion.mp covered
      obtain ⟨_, separated⟩ := Set.mem_iUnion.mp covered
      change pair.1 ≠ pair.2 ∧ q i pair.1 ≠ q i pair.2 at separated
      exact separated.1
    · intro pair distinct
      change pair.1 ≠ pair.2 at distinct
      let selected : ↥(statePairUniverse X) := ⟨pair, distinct⟩
      have selectedSeparates :
          q (witness selected) pair.1 ≠ q (witness selected) pair.2 := by
        dsimp only [witness]
        exact Classical.choose_spec (separates pair.1 pair.2 distinct)
      have selectedMem : witness selected ∈ J := by
        apply Finset.mem_image.mpr
        exact ⟨selected, Finset.mem_univ selected, rfl⟩
      apply Set.mem_iUnion.mpr
      refine ⟨witness selected, ?_⟩
      apply Set.mem_iUnion.mpr
      exact ⟨selectedMem, distinct, selectedSeparates⟩

#print axioms finite_pairwise_global_classifier_bounded

/-- Finite pairwise separation closes to one finite global classifier. The
selected coordinates are a finite subset of the original index type, not
necessarily the whole index family. -/
theorem finite_pairwise_global_classifier
    {I : Type u} {X : Type v} {V : I → Type w} [Finite X]
    (q : ∀ i, X → V i) (separates : PairwiseSeparating q) :
    HasFiniteGlobalClassifier q := by
  obtain ⟨J, _, injective⟩ :=
    finite_pairwise_global_classifier_bounded q separates
  exact ⟨J, injective⟩

#print axioms finite_pairwise_global_classifier

/-- With no readout indices, pairwise separation says exactly that no distinct
state pair exists. Thus the pairwise premise is vacuous only on subsingleton
state spaces. -/
theorem empty_index_pairwise_separating_iff_no_distinct_pairs
    {X : Type v} {V : Empty → Type w} (q : ∀ i, X → V i) :
    PairwiseSeparating q ↔ statePairUniverse X = ∅ := by
  constructor
  · intro separates
    ext pair
    constructor
    · intro distinct
      change pair.1 ≠ pair.2 at distinct
      obtain ⟨i, _⟩ := separates pair.1 pair.2 distinct
      exact i.elim
    · intro impossible
      exact impossible.elim
  · intro noPairs x y distinct
    have pairMem : (x, y) ∈ statePairUniverse X := distinct
    rw [noPairs] at pairMem
    exact pairMem.elim

#print axioms empty_index_pairwise_separating_iff_no_distinct_pairs

/-- The empty state type has an injective empty-index joint readout. This is the
`Fin 0` specialization of the existing finite-budget degenerate audit. -/
theorem empty_state_empty_budget_classifier
    {I : Type u} {V : I → Type w} (q : ∀ i, Fin 0 → V i) :
    Function.Injective
      (jointReadout
        (fun i : {candidate // candidate ∈ (∅ : Finset I)} => q i.1)) :=
  (fin_zero_empty_budget_complete q).2

#print axioms empty_state_empty_budget_classifier

/-- A singleton state type also has an injective empty-index joint readout. -/
theorem singleton_state_empty_budget_classifier
    {I : Type u} {V : I → Type w} (q : ∀ i, Unit → V i) :
    Function.Injective
      (jointReadout
        (fun i : {candidate // candidate ∈ (∅ : Finset I)} => q i.1)) :=
  (singleton_empty_budget_complete q).2

#print axioms singleton_state_empty_budget_classifier

/-- A coordinate that is constant on the state type separates no state pair,
so it contributes no pairwise certificate to the classifier construction. -/
theorem constant_readout_separation_set_empty
    {I : Type u} {X : Type v} {V : I → Type w}
    (q : ∀ i, X → V i) (i : I) (value : V i)
    (constant : ∀ x, q i x = value) :
    observerSeparationSet q i = ∅ := by
  ext pair
  constructor
  · intro separated
    change pair.1 ≠ pair.2 ∧ q i pair.1 ≠ q i pair.2 at separated
    exact separated.2 ((constant pair.1).trans (constant pair.2).symm)
  · intro impossible
    exact impossible.elim

#print axioms constant_readout_separation_set_empty

/-- The constant premise in the preceding audit cannot be dropped: the identity
Boolean readout has a nonempty separation set. -/
theorem constant_hypothesis_is_necessary :
    observerSeparationSet (fun _ : Unit => (id : Bool → Bool)) () ≠ ∅ := by
  intro emptySeparation
  have separated :
      (false, true) ∈
        observerSeparationSet (fun _ : Unit => (id : Bool → Bool)) () := by
    simp [observerSeparationSet]
  rw [emptySeparation] at separated
  exact separated

#print axioms constant_hypothesis_is_necessary

/-- The constant-zero readout on natural-number states has empty separation set
and its singleton budget is not injective. This is the explicit zero-map audit. -/
theorem zero_readout_singleton_budget_incomplete :
    observerSeparationSet (fun _ : Unit => fun _ : Nat => 0) () = ∅ ∧
      ¬Function.Injective
        (jointReadout
          (fun _ : {candidate // candidate ∈ ({()} : Finset Unit)} =>
            fun _ : Nat => 0)) :=
  zero_observer_singleton_budget_incomplete_on_nat

#print axioms zero_readout_singleton_budget_incomplete

/-- The natural-number point readouts separate every pair: the coordinate `x`
distinguishes `x` from every different `y`. -/
theorem point_readouts_pairwise_separate :
    PairwiseSeparating pointReadout := by
  intro x y distinct
  refine ⟨x, ?_⟩
  have reverse : y ≠ x := Ne.symm distinct
  simp [pointReadout, reverse]

#print axioms point_readouts_pairwise_separate

/-- Every finite selection of natural-number point readouts has a collision:
choose two states outside the selected index set, where all selected values are
`false`. -/
theorem finite_point_readout_classifier_not_injective (J : Finset Nat) :
    ¬Function.Injective
      (jointReadout
        (fun i : {candidate // candidate ∈ J} => pointReadout i.1)) := by
  obtain ⟨x, xOutside⟩ := Infinite.exists_notMem_finset J
  obtain ⟨y, yOutside⟩ := Infinite.exists_notMem_finset (insert x J)
  have yOutsideJ : y ∉ J := fun hy => yOutside (Finset.mem_insert_of_mem hy)
  have distinct : x ≠ y := by
    intro same
    subst y
    exact yOutside (Finset.mem_insert_self x J)
  intro injective
  apply distinct
  apply injective
  funext selected
  have xDifferent : x ≠ selected.1 := by
    intro same
    apply xOutside
    rw [same]
    exact selected.2
  have yDifferent : y ≠ selected.1 := by
    intro same
    apply yOutsideJ
    rw [same]
    exact selected.2
  simp [jointReadout, pointReadout, xDifferent, yDifferent]

#print axioms finite_point_readout_classifier_not_injective

/-- Finiteness of the state type is necessary. Natural numbers are infinite;
their point readouts separate pairwise, but no finite selected joint readout is
injective. -/
theorem finite_state_is_necessary :
    (¬Finite Nat) ∧
      PairwiseSeparating pointReadout ∧
        ∀ J : Finset Nat,
          ¬Function.Injective
            (jointReadout
              (fun i : {candidate // candidate ∈ J} => pointReadout i.1)) := by
  exact ⟨Infinite.not_finite, point_readouts_pairwise_separate,
    finite_point_readout_classifier_not_injective⟩

#print axioms finite_state_is_necessary

/-- Pairwise separation is also a substantive premise: a constant family on
two Boolean states is neither pairwise separating nor finitely classifying. -/
theorem pairwise_separation_is_necessary :
    let q : Unit → Bool → Unit := fun _ _ => ()
    ¬PairwiseSeparating q ∧ ¬HasFiniteGlobalClassifier q := by
  dsimp only
  constructor
  · intro separates
    obtain ⟨_, different⟩ := separates false true Bool.false_ne_true
    exact different rfl
  · rintro ⟨J, injective⟩
    apply Bool.false_ne_true
    apply injective
    funext selected
    rfl

#print axioms pairwise_separation_is_necessary

/-- FPOD principle 227.1: finite pairwise separation yields one finite global
classifier, while the natural-number point readouts give the sharp infinite
counterexample. No prime or primality hypothesis is involved. -/
theorem fpod_principle_227_1 :
    (∀ {I : Type u} {X : Type v} {V : I → Type w} [Finite X]
        (q : ∀ i, X → V i),
      PairwiseSeparating q → HasFiniteGlobalClassifier q) ∧
      (¬Finite Nat) ∧
        PairwiseSeparating pointReadout ∧
          ∀ J : Finset Nat,
            ¬Function.Injective
              (jointReadout
                (fun i : {candidate // candidate ∈ J} => pointReadout i.1)) := by
  constructor
  · intro I X V _ q separates
    exact finite_pairwise_global_classifier q separates
  · exact finite_state_is_necessary

#print axioms fpod_principle_227_1

end D5.S3.Observer.ProbabilisticClosure.FinitePairwiseGlobalClassifier
