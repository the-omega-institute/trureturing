# Vertex and literal-colour triple reservoirs

## Abstract

Independent tagged Bernoulli coordinates give an actual triple-event count with sparse-mean concentration.

**Theorem 1.1 (Three-coordinate success count).**

Lean statement: `D5/S3/Combinatorics/Probability/TripleReservoir.triple_reservoir_lower_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/TripleReservoir.triple_reservoir_lower_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V, C and A be finite. Each i in A chooses a vertex v_i and two distinct literal colours c_i,d_i. Sample every coordinate of the tagged sum V+C independently with Bernoulli parameter p in [0,1]. A choice succeeds exactly when all three coordinates inl(v_i), inr(c_i), inr(d_i) are selected. Thus its support has exactly three elements, including when V and C have identical underlying types. A supplied deterministic map A to Fin 3 must have pairwise disjoint supports inside each fibre. No probability, independence or MGF certificate is supplied to the theorem.

The proof obtains mutually independent coordinate events from Mathlib's iIndepFun_pi and finite-preimage factorization. Each success event has probability p^3. For every finite set T of choices in a fibre, its joint success intersection is exactly the coordinate intersection over the biUnion of their supports. Coordinate factorization and Finset.prod_biUnion give the product of the individual probabilities. The finite-intersection equivalence and indicator API then prove mutual independence of the success indicators. Binary block independence alone is not used as a substitute.

Let N be the actual sum of these success indicators and mu=p^3 card(A). For every delta>=0, P.real{N<=(1-delta)mu}<=exp(-delta^2 mu/6). This includes empty A and p=0 or p=1. The actual-mean finite-colour theorem supplies the final concentration step only after the exact integrals and mutual independence have been proved.

Later connector integration must independently produce the graph-realized choices, distinct literal colours, and a proper three-colouring whose fibres have disjoint supports. This theorem does not prove a conflict-degree bound or that graph realization. It does not assemble post-revelation forbidden sets or a longer simple path. Full original Lemma 4.3 (B1/B2/B3 with all quantifiers and constants), arbitrary-abelian proper-interval Good, and unrestricted AM remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Probability/TripleReservoir.triple_reservoir_lower_tail`
- Dependency: [D5/S3/Combinatorics/Probability/FiniteColourLowerTail](FiniteColourLowerTail.md)
