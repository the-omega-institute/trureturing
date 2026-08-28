# Transitive Invariant Distribution

## Abstract

A transitive action admits exactly the uniform invariant probability mass function.

**Theorem 1.1 (The invariant law is uniquely uniform).**

$$\begin{gathered}\forall G: \operatorname{Type}, A: \operatorname{Type},\\{}\operatorname{Group}(G) \land \operatorname{Fintype}(A) \land \operatorname{Nonempty}(A) \land\\{}\operatorname{MulAction}(G, A) \land \operatorname{IsPretransitive}(G, A) \Rightarrow\\{}{\exists ! mu: \operatorname{PMF}(A), \forall g: G, a: A, mu(g smul a) = mu(a)} \land\\{}{\forall mu: \operatorname{PMF}(A), (\forall g: G, a: A, mu(g smul a) = mu(a)) \Rightarrow \forall a: A, mu(a) = \operatorname{card}(A)^{-1}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TransitiveInvariantDistribution.transitive_invariant_distribution_unique_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transitivity sends any chosen point to any other point. Invariance therefore forces all point masses of a candidate law to agree.

The total mass is one, so cancellation by the nonzero finite carrier cardinality identifies that common value with the uniform mass.

The argument proves both the unique invariant probability mass function and its public pointwise cardinality formula.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TransitiveInvariantDistribution.transitive_invariant_distribution_unique_uniform`
