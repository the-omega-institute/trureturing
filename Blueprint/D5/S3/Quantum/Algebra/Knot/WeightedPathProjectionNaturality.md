# Naturality of Weighted Path Projections

## Abstract

The literal old local projection is preserved by extension of a legal path, and the endpoint trace is cyclic.

**Theorem 1.1 (Old generators in the actual path tower).**

$$\begin{gathered}\operatorname{FiniteDecidable}\left(L\right); \operatorname{ArbitraryRelationAndRealWeights}\left(R, d, delta\right)\\\forall n \in \mathbb{N},\; \forall s \in L,\; \forall i \in \mathbb{N},\; \operatorname{And}\left(\operatorname{Lt}\left(0, i\right), \operatorname{Lt}\left(i, n\right)\right)\Rightarrow \operatorname{iota}\left(n, s, \operatorname{e}\left(n, s, i\right)\right) = \operatorname{e}\left(n+1, s, i\right)\\\forall n \in \mathbb{N},\; \forall s \in L,\; \forall X \in \operatorname{C}\left(n, s\right),\; \forall Y \in \operatorname{C}\left(n, s\right),\; \operatorname{tau}\left(n, s, X \cdot Y\right) = \operatorname{tau}\left(n, s, Y \cdot X\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Knot/WeightedPathProjectionNaturality.weighted_path_projection_naturality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L be any finite decidable vertex type, R any relation on L, d any real vertex weights, and delta any real number. LegalPath, pathProjection, C, iota and tau are the actual declarations of WeightedLegalPathTemperleyLieb and WeightedPathMarkovTrace. The named kernel e(n,s,i) has endpoint block pathProjection R d delta n s t i; idempotence is not asserted for these arbitrary weights. Its index satisfies zero less than i less than n. Neither symmetry, positivity nor a Perron equality is needed for the two identities proved here; division and square root are the total Lean real operations.

Splitting a length n+1 path into its predecessor endpoint and length n prefix identifies each new endpoint fiber with the disjoint union of old fibers. The actual inclusion iota is block diagonal in these coordinates. Within a fixed predecessor block, appending an edge preserves every old coordinate and adds the same last coordinate to both paths, so the literal local kernel is unchanged. Between distinct predecessor blocks, the old local index i is strictly less than n; the kernel preserves coordinate n and consequently vanishes. These two entry calculations prove naturality of the full endpoint-block projection.

The trace tau is the weighted sum of the ordinary matrix traces, divided by delta to the n times d(s). Matrix trace cyclicity applies separately to each endpoint block, and the common weights and denominator preserve it. Empty endpoint fibers and n=0 remain in the trace scope. The generator condition zero less than i less than n is vacuous at n=0 and n=1.

This supplies the compatibility of old literal generators needed to extend path-model representations along the tower. The source theorem includes trace cyclicity by reuse of Matrix.trace_mul_comm. This is classical path-model background: Aharonov, Jones and Landau, A Polynomial Quantum Algorithm for Approximating the Jones Polynomial, arXiv:quant-ph/0511096v2, Definition 3.2 and equation (4) define the local path operator, while Definition 3.3 and Claim 3.6 describe the endpoint-weighted trace and its Markov properties for the line graph. The present statement covers arbitrary finite relation and weights; it is not attributed as their exact theorem.

The theorem does not construct an Artin braid group representation, a geometric closure map, geometric Markov equivalence or a knot invariant. It does not establish positivity or faithfulness of tau, Laurent polynomial integrality, modular specialization or an explicit knot witness.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Knot/WeightedPathProjectionNaturality.weighted_path_projection_naturality`
- Dependency: [D5/S3/Quantum/Algebra/Knot/WeightedPathMarkovTrace](WeightedPathMarkovTrace.md)
