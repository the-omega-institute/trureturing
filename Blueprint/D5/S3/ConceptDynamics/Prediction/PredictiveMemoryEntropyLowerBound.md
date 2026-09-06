# Predictive Memory Entropy Lower Bound

## Abstract

Every finite exact predictive memory contains at least the conditional information carried by the minimal predictive quotient.

**Definition 1.1 (Exact predictive memory factors current and updated information).**

$$\forall X, O, M: \operatorname{Type}, q: X \to O, F: X \to X, r: X \to M,\\{}\operatorname{IsExactPredictiveMemory}\left(q, F, r\right) \iff \operatorname{Refines}\left(q, r\right) \land \operatorname{Refines}\left(r \circ F, r\right).$$

*Formalization.* `D5/S3/ConceptDynamics/Prediction/PredictiveMemoryEntropyLowerBound.IsExactPredictiveMemory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A memory readout r is exact for q and F exactly when q factors through r and the updated memory r after F also factors through r. Both factorization clauses use the same present memory interface.

**Theorem 1.2 (Exact predictive memories dominate the minimal quotient).**

$$\begin{gathered}\forall X, O, M: \operatorname{Type},\\{}[\operatorname{Fintype}(X)] [\operatorname{Fintype}(O)] [\operatorname{Fintype}(M)],\\mu: X \to \mathbb{R}, q: X \to O,\\F: X \to X, r: X \to M,\\(\forall x, 0 \leq \operatorname{mu}\left(x\right)) \land \operatorname{IsExactPredictiveMemory}\left(q, F, r\right) \Rightarrow\\\operatorname{conditionalEntropy}\left(\operatorname{predictiveMemoryJointLaw}\left(mu, q, \operatorname{predictiveProjection}\left(F, q\right)\right)\right) \leq \operatorname{conditionalEntropy}\left(\operatorname{predictiveMemoryJointLaw}\left(mu, q, r\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Prediction/PredictiveMemoryEntropyLowerBound.predictive_memory_entropy_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An exact memory factors both the current readout and its updated memory through the memory state. The coarseness clause of the minimal predictive completion theorem therefore makes the canonical predictive projection a deterministic function of the memory.

Conditional-entropy data processing gives the inequality for a normalized law. For arbitrary nonnegative finite mass, zero total mass is immediate; otherwise normalize, apply the library theorem, and rescale both conditional entropies.

No nonemptiness assumptions are needed. The statement includes empty state carriers, singleton carriers, constant maps, identity maps, and identically zero mass.

**Lemma 1.3 (Nonnegative mass is necessary).**

$$\begin{gathered}\operatorname{mu}\left(false\right) = 2, \operatorname{mu}\left(true\right) = -1,\\\forall b: Bool, \operatorname{q}\left(b\right) = star,\\\neg(\forall b, 0 \leq \operatorname{mu}\left(b\right)) \land \operatorname{IsExactPredictiveMemory}\left(q, id, id\right) \land\\\neg(\operatorname{conditionalEntropy}\left(\operatorname{predictiveMemoryJointLaw}\left(mu, q, \operatorname{predictiveProjection}\left(id, q\right)\right)\right) \leq \operatorname{conditionalEntropy}\left(\operatorname{predictiveMemoryJointLaw}\left(mu, q, id\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Prediction/PredictiveMemoryEntropyLowerBound.nonnegative_mass_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take state and memory carrier Bool, constant Unit readout, identity update, identity memory, and signed masses two and minus one. The memory is exact and the predictive quotient is a singleton.

The quotient conditional entropy is zero, whereas the identity-memory conditional entropy is minus two times log two. Since log two is positive, the claimed lower-bound inequality fails without nonnegativity.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Prediction/PredictiveMemoryEntropyLowerBound.IsExactPredictiveMemory`
- Truth anchor: `D5/S3/ConceptDynamics/Prediction/PredictiveMemoryEntropyLowerBound.nonnegative_mass_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Prediction/PredictiveMemoryEntropyLowerBound.predictive_memory_entropy_lower_bound`
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/MinimalPredictiveCompletionQuotient](../Sufficiency/MinimalPredictiveCompletionQuotient.md)
- Dependency: [D5/S3/Entropy/Forgetting/CompletionEntropyMinimality](../../Entropy/Forgetting/CompletionEntropyMinimality.md)
