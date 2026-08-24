# Finite Identification Capacity Bound

## Abstract

Injective joint readout bounds a finite state space by the capacity of its dependent outcome space, equivalently by its base-two logarithmic cost at positive capacity.

**Theorem 1.1 (Injective joint readout bounds state cardinality).**

$$\begin{aligned}\forall X, J: \operatorname{Type}, O: J \to \operatorname{Type},\\qJ: X \to \prod_{j: J}O_{j},\\\operatorname{Finite}\left(X\right) \land \operatorname{Fintype}\left(J\right) \land (\forall j: J, \operatorname{Fintype}\left(O_{j}\right)) \land \operatorname{Injective}\left(qJ\right) \Rightarrow \operatorname{card}\left(X\right) \leq \operatorname{Cap}\left(O\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/FiniteIdentificationCapacityBound.finite_identification_capacity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite experiment family, capacity is the number of dependent joint outcome tuples, with one outcome chosen from each indexed outcome type.

An injective joint readout assigns different tuples to different states. The finite state space therefore embeds in the joint-outcome space, so its cardinality cannot exceed the experiment capacity.

**Lemma 1.2 (The capacity bound implies the base-two cost bound).**

$$\begin{aligned}\forall X, J: \operatorname{Type}, O: J \to \operatorname{Type},\\qJ: X \to \prod_{j: J}O_{j},\\\operatorname{Finite}\left(X\right) \land \operatorname{Fintype}\left(J\right) \land (\forall j: J, \operatorname{Fintype}\left(O_{j}\right)) \land 0 < \operatorname{Cap}\left(O\right) \land \operatorname{Injective}\left(qJ\right) \Rightarrow \operatorname{logb}\left(2, \operatorname{card}\left(X\right)\right) \leq \operatorname{Cost}\left(O\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/FiniteIdentificationCapacityBound.cost_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When capacity is positive, the injective readout first gives the finite cardinality bound. Taking logarithms to base two preserves that order, and the logarithm of capacity is exactly the defined cost.

If the state cardinality is zero, its base-two logarithm is zero and the positive capacity has nonnegative cost. Otherwise both cardinalities are positive, so ordinary logarithmic monotonicity applies directly.

**Lemma 1.3 (Positive capacity equates cardinal and cost bounds).**

$$\begin{aligned}\forall X, J: \operatorname{Type}, O: J \to \operatorname{Type},\\\operatorname{Finite}\left(X\right) \land \operatorname{Fintype}\left(J\right) \land (\forall j: J, \operatorname{Fintype}\left(O_{j}\right)) \land 0 < \operatorname{Cap}\left(O\right) \Rightarrow \\(\operatorname{card}\left(X\right) \leq \operatorname{Cap}\left(O\right) \iff \operatorname{logb}\left(2, \operatorname{card}\left(X\right)\right) \leq \operatorname{Cost}\left(O\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/FiniteIdentificationCapacityBound.cardinal_bound_iff_cost_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At positive capacity, bounding the number of states by the joint-readout capacity is equivalent to bounding its base-two logarithm by the identification cost.

The forward implication is monotonicity of the base-two logarithm. For a nonempty finite state space, strict increase of that logarithm also reflects the cost inequality back to the cardinal inequality; the zero-cardinality case satisfies the cardinal bound automatically.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/FiniteIdentificationCapacityBound.cardinal_bound_iff_cost_bound`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/FiniteIdentificationCapacityBound.cost_form`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/FiniteIdentificationCapacityBound.finite_identification_capacity_bound`
