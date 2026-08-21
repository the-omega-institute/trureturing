# Controlled Distinguishing Depth

## Abstract

Shortest distinguishing input words characterize complete controlled behavior and its stabilization depth.

**Theorem 1.1 (Shortest distinguishing words determine controlled stability).**

$$\begin{gathered}\forall Y, U, O,\\{}\operatorname{FiniteNonempty}(Y), \operatorname{FiniteNonempty}(U), \operatorname{FiniteNonempty}(O),\\{}F: U \to Y \to Y, q: Y \to O, \operatorname{Surjective}(q),\\{}(\forall y, y'\in Y, \operatorname{shortestDistinguishingDepth}(F, q, (y, y')) = \infty \Leftrightarrow (y, y') \in \operatorname{controlledLimitRelation}(F, q)) \land\\{}(\operatorname{finitelyDistinguishablePairs}(F, q) \neq \emptyset \Rightarrow \operatorname{controlledStabilityDepth}(F, q) = \max_{(y, y') \in \operatorname{finitelyDistinguishablePairs}(F, q)} \operatorname{shortestDistinguishingDepth}(F, q, (y, y'))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/ControlledDistinguishingDepth.controlled_shortest_intervention_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the state, input, and realized readout carriers be finite and nonempty. An input word is applied from left to right through the canonical controlled transition semantics. The distance of a state pair is the least word length at which the two resulting readouts differ, and is infinite when no such word exists.

A pair has infinite distance exactly when every finite input word gives equal readouts, which is membership in the canonical complete controlled relation. When at least one pair has finite distance, the source's least stable refinement depth is the maximum of those finite shortest-word distances.

The proof directly applies the frozen controlled finite-stability theorem. Pinned Mathlib's Nat.find selects the least source-level separating word length, while the nonempty finite supremum supplies the latest such length. Repository and pinned-library searches found no theorem already packaging both branching-input clauses.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ControlledDistinguishingDepth.controlled_shortest_intervention_witness`
- Dependency: [D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability](ControlledFiniteStability.md)
