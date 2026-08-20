# Finite Contracting Stability

## Abstract

Finite contracting set updates stabilize with a sharp strict-change bound.

**Theorem 1.1 (Finite contracting updates stabilize).**

$$\forall X: \operatorname{Type}, [\operatorname{Finite}(X)],\ U: \operatorname{Set}(X) \to \operatorname{Set}(X),\ (\forall A: \operatorname{Set}(X), U(A) \subseteq A),\ S: \mathbb{N} \to \operatorname{Set}(X),\ (\forall n: \mathbb{N}, S(n+1) = U(S(n))) \Rightarrow\\(\exists N\in \mathbb{N}, N \leq \operatorname{ncard}(S(0)) \land \forall n\in \mathbb{N}, N \leq n \Rightarrow S(n) = S(N)) \land\\\operatorname{ncard}(\{n\in \mathbb{N} \mid S(n+1) \neq S(n)\}) \leq \operatorname{ncard}(S(0)).$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/FiniteContractingStability.finite_contracting_updates_stabilize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be finite, let U map subsets of X to subsets of X without adding states, and let S satisfy S(n+1) = U(S(n)). There is an index N, no larger than the cardinality of S(0), after which every set in the sequence equals S(N).

The set of all indices at which the update is strict has cardinality at most the cardinality of S(0). Thus the statement records both eventual stability and the source's strict-change bound.

Pinned Mathlib supplies Nat.stabilises_of_antitone for the cardinality sequence. Equal consecutive cardinalities force equal finite sets, and all strict changes occur before the resulting stable index. Repository search found no generic theorem containing both conclusions.

## References

- Truth anchor: `D5/S1/FixedPoints/FiniteContractingStability.finite_contracting_updates_stabilize`
