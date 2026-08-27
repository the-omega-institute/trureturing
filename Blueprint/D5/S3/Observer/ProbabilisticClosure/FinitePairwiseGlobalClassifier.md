# Finite Pairwise Global Classifier

## Abstract

Finite pairwise state separation closes to one finite joint classifier, and point readouts on the naturals show that finiteness is sharp.

**Definition 1.1 (Pairwise separating readout family).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.PairwiseSeparating`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.PairwiseSeparating` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every pair of distinct states has some readout coordinate on which the two values differ; the coordinate may depend on the pair.

**Definition 1.2 (Existence of a finite global classifier).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.HasFiniteGlobalClassifier`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.HasFiniteGlobalClassifier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Some finite subset of indices has an injective dependent joint readout on the state type.

**Definition 1.3 (Natural-number point readout).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.pointReadout`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.pointReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinate i returns true exactly at the natural-number state i.

**Theorem 1.4 (Finite pairwise separation has a bounded finite classifier).**

$$\operatorname{Finite}\left(X\right) \land \operatorname{PairwiseSeparating}\left(q\right) \Rightarrow \exists J: FinsetI, \operatorname{card}\left(J\right) \leq \operatorname{card}\left(\operatorname{statePairUniverse}\left(X\right)\right) \land \operatorname{Injective}\left(\operatorname{JointReadout}\left(q, J\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.finite_pairwise_global_classifier_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose one separating coordinate for each ordered distinct state pair. The image of this finite witness map is a classifier, with cardinality bounded by the distinct-pair universe.

**Theorem 1.5 (Finite pairwise separation closes globally).**

$$\operatorname{Finite}\left(X\right) \land \operatorname{PairwiseSeparating}\left(q\right) \Rightarrow \operatorname{HasFiniteGlobalClassifier}\left(q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.finite_pairwise_global_classifier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bounded witness set gives a finite selected joint readout that is injective. No finiteness is imposed on indices or outputs.

**Theorem 1.6 (Empty index families separate only subsingleton states).**

$$I = \emptyset: \operatorname{PairwiseSeparating}\left(q\right) \iff \operatorname{statePairUniverse}\left(X\right) = \emptyset.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.empty_index_pairwise_separating_iff_no_distinct_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With no coordinate available, the pairwise premise holds exactly when the distinct-state-pair universe is empty.

**Theorem 1.7 (The empty state type needs no coordinates).**

$$X = FinZero: \operatorname{Injective}\left(\operatorname{JointReadout}\left(q, \emptyset\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.empty_state_empty_budget_classifier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty joint readout on Fin zero is injective vacuously.

**Theorem 1.8 (A singleton state type needs no coordinates).**

$$X = Unit: \operatorname{Injective}\left(\operatorname{JointReadout}\left(q, \emptyset\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.singleton_state_empty_budget_classifier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty joint readout on Unit is injective because all states are equal.

**Theorem 1.9 (A constant coordinate separates no state pair).**

$$\operatorname{Constant}\left(\operatorname{q}\left(i\right)\right) \Rightarrow \operatorname{observerSeparationSet}\left(q, i\right) = \emptyset.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.constant_readout_separation_set_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A coordinate constant across states has empty separation set and cannot occur as a witness in the finite classifier.

**Theorem 1.10 (Constancy is necessary for the empty-separation conclusion).**

$$\operatorname{observerSeparationSet}\left(idBool, unit\right) \neq \emptyset.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.constant_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity Boolean readout separates false from true, so its separation set is nonempty.

**Theorem 1.11 (The zero readout is incomplete on the naturals).**

$$\operatorname{observerSeparationSet}\left(zeroReadout, unit\right) = \emptyset \land \neg\operatorname{Injective}\left(\operatorname{JointReadout}\left(zeroReadout, singleton\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.zero_readout_singleton_budget_incomplete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant-zero coordinate has empty separation set, and the states zero and one collide in its singleton budget.

**Theorem 1.12 (Natural-number point readouts separate pairwise).**

$$\operatorname{PairwiseSeparating}\left(pointReadout\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.point_readouts_pairwise_separate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct x and y, coordinate x is true at x and false at y.

**Theorem 1.13 (No finite point-readout selection classifies the naturals).**

$$\forall J: FinsetNat, \neg\operatorname{Injective}\left(\operatorname{JointReadout}\left(pointReadout, J\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.finite_point_readout_classifier_not_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two states outside a finite selected set have false values at every selected coordinate and hence collide.

**Theorem 1.14 (State finiteness is necessary).**

$$\neg\operatorname{Finite}\left(Nat\right) \land \operatorname{PairwiseSeparating}\left(pointReadout\right) \land \forall J: FinsetNat, \neg\operatorname{Injective}\left(\operatorname{JointReadout}\left(pointReadout, J\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.finite_state_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nat is infinite and its point readouts separate all pairs, yet every finite selected joint readout has a collision.

**Theorem 1.15 (Pairwise separation is necessary).**

$$\neg\operatorname{PairwiseSeparating}\left(constantFamily\right) \land \neg\operatorname{HasFiniteGlobalClassifier}\left(constantFamily\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.pairwise_separation_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant Unit-valued family on Bool is neither pairwise separating nor finitely classifying.

**Theorem 1.16 (Pairwise and global separation close on finite states).**

$$\forall X, q, \operatorname{Finite}\left(X\right) \land \operatorname{PairwiseSeparating}\left(q\right) \Rightarrow \operatorname{HasFiniteGlobalClassifier}\left(q\right) \land \neg\operatorname{Finite}\left(Nat\right) \land \operatorname{PairwiseSeparating}\left(pointReadout\right) \land \forall J: FinsetNat, \neg\operatorname{Injective}\left(\operatorname{JointReadout}\left(pointReadout, J\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.fpod_principle_227_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite state spaces turn pair-dependent readout certificates into one finite classifier. The point-readout family on Nat is the sharp infinite counterexample.

This is dual in scope to Principle 120.1: that theorem concerns infinite-index measure realizability, while this theorem concerns finite-state injective classification.

No prime parameter or primality assumption is used.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.HasFiniteGlobalClassifier`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.PairwiseSeparating`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.constant_hypothesis_is_necessary`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.constant_readout_separation_set_empty`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.empty_index_pairwise_separating_iff_no_distinct_pairs`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.empty_state_empty_budget_classifier`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.finite_pairwise_global_classifier`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.finite_pairwise_global_classifier_bounded`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.finite_point_readout_classifier_not_injective`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.finite_state_is_necessary`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.fpod_principle_227_1`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.pairwise_separation_is_necessary`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.pointReadout`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.point_readouts_pairwise_separate`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.singleton_state_empty_budget_classifier`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/FinitePairwiseGlobalClassifier.zero_readout_singleton_budget_incomplete`
- Dependency: [D5/S3/Observer/Budget/MinimumCompleteSetCover](../Budget/MinimumCompleteSetCover.md)
