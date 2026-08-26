# Minimum Complete Set Cover

## Abstract

Finite observer completeness is exactly coverage of all distinct ordered state pairs; minimum complete budgets are the corresponding natural-cost set covers.

**Theorem 1.1 (Finite-budget injectivity is separation coverage).**

$$\forall X \in \operatorname{Type}, I \in \operatorname{Type}, V \in I \to \operatorname{Type}, q \in \operatorname{ObserverFamily}\left(I, X, V\right), J \in \operatorname{Finset}\left(I\right),\; \operatorname{Injective}\left(\operatorname{jointReadout}\left(J, q\right)\right) \Leftrightarrow \operatorname{selectedSeparationUnion}\left(J, q\right) = \operatorname{statePairUniverse}\left(X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/MinimumCompleteSetCover.finite_budget_injective_iff_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a Finset J, equality of joint readouts means equality at every selected observer. Thus injectivity is equivalent to the union of the selected separation sets being the universe of distinct ordered state pairs. Neither the state type nor the observer type is assumed finite.

**Theorem 1.2 (Minimum complete budgets are minimum-cost covers).**

$$\forall X \in \operatorname{Type}, I \in \operatorname{Type}, V \in I \to \operatorname{Type}, q \in \operatorname{ObserverFamily}\left(I, X, V\right), J \in \operatorname{Finset}\left(I\right), c \in I \to \mathbb{N},\; \operatorname{IsMinimumCompleteBudget}\left(J, q, c\right) \Leftrightarrow \left(\operatorname{selectedSeparationUnion}\left(J, q\right) = \operatorname{statePairUniverse}\left(X\right) \land \left(\forall K \in \operatorname{Finset}\left(I\right),\; \operatorname{selectedSeparationUnion}\left(K, q\right) = \operatorname{statePairUniverse}\left(X\right) \Rightarrow \operatorname{budgetCost}\left(J, c\right) \leq \operatorname{budgetCost}\left(K, c\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/MinimumCompleteSetCover.minimum_complete_budget_iff_minimum_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The injectivity-cover equivalence rewrites both completeness of J and completeness of every competitor K. The remaining comparison is the natural-number sum of supplied observer costs, so this is precisely a finite-budget set-cover instance without an existence claim.

**Theorem 1.3 (One collision certifies incompleteness).**

$$\forall X \in \operatorname{Type}, I \in \operatorname{Type}, V \in I \to \operatorname{Type}, q \in \operatorname{ObserverFamily}\left(I, X, V\right), J \in \operatorname{Finset}\left(I\right),\; \left(\exists x \in X, y \in X,\; x \ne y \land \operatorname{jointReadoutAt}\left(J, q, x\right) = \operatorname{jointReadoutAt}\left(J, q, y\right)\right) \Rightarrow \left(\neg \operatorname{Injective}\left(\operatorname{jointReadout}\left(J, q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/MinimumCompleteSetCover.counterexample_certifies_incomplete_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two distinct states with equal selected joint readouts contradict injectivity. This is the counterexample half of Principle 12.1.

**Theorem 1.4 (Completeness separates every distinct pair).**

$$\forall X \in \operatorname{Type}, I \in \operatorname{Type}, V \in I \to \operatorname{Type}, q \in \operatorname{ObserverFamily}\left(I, X, V\right), J \in \operatorname{Finset}\left(I\right),\; \operatorname{Injective}\left(\operatorname{jointReadout}\left(J, q\right)\right) \Rightarrow \left(\forall x \in X, y \in X,\; x \ne y \Rightarrow \left(\exists i \in I,\; i \in J \land \operatorname{Separates}\left(q, i, x, y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/MinimumCompleteSetCover.injective_budget_covers_every_distinct_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An injective joint readout covers the distinct-pair universe. Membership in that union exposes a selected observer that separates each given pair, formalizing the complete-coverage half of Principle 12.1.

**Lemma 1.5 (The empty budget is complete exactly for an empty pair universe).**

$$\forall X \in \operatorname{Type}, I \in \operatorname{Type}, V \in I \to \operatorname{Type}, q \in \operatorname{ObserverFamily}\left(I, X, V\right),\; \operatorname{Injective}\left(\operatorname{jointReadout}\left(\emptyset, q\right)\right) \Leftrightarrow \operatorname{statePairUniverse}\left(X\right) = \emptyset$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/MinimumCompleteSetCover.empty_budget_injective_iff_pair_universe_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty union covers exactly when there are no distinct state pairs. This also characterizes when an empty selected product can be injective.

**Lemma 1.6 (The empty budget is complete on Fin zero).**

$$\forall I \in \operatorname{Type}, q \in \operatorname{ObserverFamily}\left(I, \operatorname{Fin}\left(0\right)\right),\; \operatorname{statePairUniverse}\left(\operatorname{Fin}\left(0\right)\right) = \emptyset \land \operatorname{Injective}\left(\operatorname{jointReadout}\left(\emptyset, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/MinimumCompleteSetCover.fin_zero_empty_budget_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin 0 has no states and hence no distinct pairs. Its empty-budget readout is injective vacuously, covering the empty-state degeneracy explicitly.

**Lemma 1.7 (The empty budget is complete on a singleton).**

$$\forall I \in \operatorname{Type}, q \in \operatorname{ObserverFamily}\left(I, Unit\right),\; \operatorname{statePairUniverse}\left(Unit\right) = \emptyset \land \operatorname{Injective}\left(\operatorname{jointReadout}\left(\emptyset, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/MinimumCompleteSetCover.singleton_empty_budget_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unit has no pair of unequal states. Consequently its distinct-pair universe is empty and every empty-budget joint readout is injective.

**Lemma 1.8 (A constant observer separates no pair).**

$$\forall X \in \operatorname{Type}, I \in \operatorname{Type}, value \in \operatorname{ValueFamily}\left(I\right), i \in I,\; \operatorname{observerSeparationSet}\left(\operatorname{constantObserverFamily}\left(value\right), i\right) = \emptyset$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/MinimumCompleteSetCover.constant_observer_separation_set_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant readout agrees on both components of every pair, so its named separation set is empty on every state space.

**Lemma 1.9 (One identity observer is complete).**

$$\forall X \in \operatorname{Type},\; \operatorname{Injective}\left(\operatorname{jointReadout}\left(\{*\}, \operatorname{identityObserverFamily}\left(X\right)\right)\right) \land \operatorname{selectedSeparationUnion}\left(\{*\}, \operatorname{identityObserverFamily}\left(X\right)\right) = \operatorname{statePairUniverse}\left(X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/MinimumCompleteSetCover.identity_observer_singleton_budget_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity coordinate recovers the state from the singleton joint readout. The main equivalence then shows that its separation set covers every distinct ordered pair, including on infinite state spaces.

**Lemma 1.10 (One zero observer is incomplete on Nat).**

$$\operatorname{observerSeparationSet}\left(\operatorname{constantObserverFamily}\left(0\right), *\right) = \emptyset \land \left(\neg \operatorname{Injective}\left(\operatorname{jointReadout}\left(\{*\}, \operatorname{constantObserverFamily}\left(0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/MinimumCompleteSetCover.zero_observer_singleton_budget_incomplete_on_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant-zero observer has empty separation set, while the states zero and one collide. This supplies a concrete trivial-map audit.

**Lemma 1.11 (With zero costs, minimum means complete).**

$$\forall X \in \operatorname{Type}, I \in \operatorname{Type}, V \in I \to \operatorname{Type}, q \in \operatorname{ObserverFamily}\left(I, X, V\right), J \in \operatorname{Finset}\left(I\right),\; \operatorname{IsMinimumCompleteBudget}\left(J, q, \operatorname{const}\left(0\right)\right) \Leftrightarrow \operatorname{Injective}\left(\operatorname{jointReadout}\left(J, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/MinimumCompleteSetCover.zero_cost_budget_minimum_iff_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every observer costs zero, all finite budgets have equal total cost. A budget is therefore minimum complete exactly when it is complete.

**Lemma 1.12 (A useless observer can be removed from a minimum budget).**

$$\forall X \in \operatorname{Type}, I \in \operatorname{Type}, V \in I \to \operatorname{Type}, q \in \operatorname{ObserverFamily}\left(I, X, V\right), J \in \operatorname{Finset}\left(I\right), c \in I \to \mathbb{N},\; \operatorname{DecidableEq}\left(I\right) \Rightarrow \left(\forall i \in I,\; \left(\operatorname{observerSeparationSet}\left(q, i\right) = \emptyset \land \operatorname{IsMinimumCompleteBudget}\left(J, q, c\right)\right) \Rightarrow \operatorname{IsMinimumCompleteBudget}\left(\operatorname{erase}\left(J, i\right), q, c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/MinimumCompleteSetCover.empty_separation_observer_removal_preserves_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Erasing an observer whose separation set is empty leaves the cover unchanged. Natural-number nonnegativity makes the erased budget no more expensive, so minimum completeness is preserved.

**Lemma 1.13 (Empty separation is necessary for the removal theorem).**

$$\operatorname{IsMinimumCompleteBudget}\left(\{*\}, \operatorname{identityObserverFamily}\left(Bool\right), \operatorname{const}\left(0\right)\right) \land \left(\operatorname{observerSeparationSet}\left(\operatorname{identityObserverFamily}\left(Bool\right), *\right) \ne \emptyset \land \left(\neg \operatorname{IsMinimumCompleteBudget}\left(\operatorname{erase}\left(\{*\}, *\right), \operatorname{identityObserverFamily}\left(Bool\right), \operatorname{const}\left(0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/MinimumCompleteSetCover.empty_separation_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Bool, the sole identity observer is a zero-cost minimum complete budget and has nonempty separation set. Erasing it yields the empty incomplete budget, giving a concrete counterexample if the premise is omitted.

**Lemma 1.14 (Starting minimality is necessary for the removal theorem).**

$$\operatorname{observerSeparationSet}\left(\operatorname{observerTriple}\left(\operatorname{const}\left(false\right), id, id\right), 0\right) = \emptyset \land \left(\neg \operatorname{IsMinimumCompleteBudget}\left(\operatorname{erase}\left(\{0, 1\}, 0\right), \operatorname{observerTriple}\left(\operatorname{const}\left(false\right), id, id\right), \operatorname{costTriple}\left(0, 2, 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/MinimumCompleteSetCover.minimum_budget_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For three observers on Bool, observer zero is useless and observer one is an identity of cost two. After erasing zero, that budget remains dominated by the identity observer two of cost one, so it is not minimum.

## References

- Truth anchor: `D5/S3/Observer/Budget/MinimumCompleteSetCover.constant_observer_separation_set_empty`
- Truth anchor: `D5/S3/Observer/Budget/MinimumCompleteSetCover.counterexample_certifies_incomplete_budget`
- Truth anchor: `D5/S3/Observer/Budget/MinimumCompleteSetCover.empty_budget_injective_iff_pair_universe_empty`
- Truth anchor: `D5/S3/Observer/Budget/MinimumCompleteSetCover.empty_separation_hypothesis_is_necessary`
- Truth anchor: `D5/S3/Observer/Budget/MinimumCompleteSetCover.empty_separation_observer_removal_preserves_minimum`
- Truth anchor: `D5/S3/Observer/Budget/MinimumCompleteSetCover.fin_zero_empty_budget_complete`
- Truth anchor: `D5/S3/Observer/Budget/MinimumCompleteSetCover.finite_budget_injective_iff_cover`
- Truth anchor: `D5/S3/Observer/Budget/MinimumCompleteSetCover.identity_observer_singleton_budget_complete`
- Truth anchor: `D5/S3/Observer/Budget/MinimumCompleteSetCover.injective_budget_covers_every_distinct_pair`
- Truth anchor: `D5/S3/Observer/Budget/MinimumCompleteSetCover.minimum_budget_hypothesis_is_necessary`
- Truth anchor: `D5/S3/Observer/Budget/MinimumCompleteSetCover.minimum_complete_budget_iff_minimum_cover`
- Truth anchor: `D5/S3/Observer/Budget/MinimumCompleteSetCover.singleton_empty_budget_complete`
- Truth anchor: `D5/S3/Observer/Budget/MinimumCompleteSetCover.zero_cost_budget_minimum_iff_complete`
- Truth anchor: `D5/S3/Observer/Budget/MinimumCompleteSetCover.zero_observer_singleton_budget_incomplete_on_nat`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../../ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.md)
