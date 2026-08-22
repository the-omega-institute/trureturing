# Belief Set Sufficiency

## Abstract

Equal compatible belief sets determine equal future observation trajectories.

**Theorem 1.1 (The compatible belief set is sufficient for future trajectories).**

$$\begin{gathered}\forall X, U, O: \operatorname{Type},\\F: U \to \left(X \to X\right), q: X \to O,\\o_{1}, o_{2}: O, h_{1}, h_{2}: \operatorname{List}(U \times O),\\\operatorname{compatibleBelief}(F, q, o_{1}, h_{1}) = \operatorname{compatibleBelief}(F, q, o_{2}, h_{2}) \Rightarrow\\\forall a: \operatorname{List}(U), \operatorname{possibleObservationTrajectories}(F, q, o_{1}, h_{1}, a) = \operatorname{possibleObservationTrajectories}(F, q, o_{2}, h_{2}, a).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionFactors/BeliefSetSufficiency.belief_set_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be the hidden-state type, U the action type, and O the observation type. The compatible belief set starts with every state having the initial observation, then processes each action-observation pair by applying the indexed update and retaining exactly the states with the reported next observation.

For a future action word, the observation trajectory of a state reads the canonical controlled behavior on every prefix of that word. Possible trajectories are constructed independently from hidden start and final states connected by every observed transition in the concrete history.

If two concrete histories generate the same compatible belief set, their possible trajectory sets are equal for every future action word. The statement retains both histories publicly. The proof first identifies the final states produced by the recursive belief update with those produced by the independent transition-path relation.

The module directly reuses the repository's `controlledBehavior` semantics and pinned Mathlib's exact `List.inits` prefix construction. Searches found no existing theorem combining them with recursively updated belief sets.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/BeliefSetSufficiency.belief_set_sufficiency`
