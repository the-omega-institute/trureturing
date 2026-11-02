# Graph rank states and cyclic embedding counts

## Abstract

The signed rank-state polynomial has an exact finite coefficient decomposition. Its forest contribution is not generally the negative-binomial coefficient: on the triangle its cubic coefficient is zero, while the comparison coefficient is minus one. Actual graph rank bounds give nonnegative exponents, small support, a fixed-rank cyclic-state count through finite ordered-embedding codes, and rank-dependent term growth. The companion TutteCoefficientAsymptotics module consumes these bounds to control both forest error and cyclic contribution. The weaving geometry and Jones identification remain separate obligations.

**Definition 1.1 (State exponent).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponent`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite polynomial uses the Nat conversion of the integer exponent only after an explicit nonnegativity proof has been supplied.

**Definition 1.2 (Integer rank-state exponent).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponentInteger`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponentInteger` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exponent is first formed in Z as v − 1 + s − 2q, before any conversion to a polynomial Nat exponent.

**Theorem 1.3 (No-truncation exponent bridge).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponent_cast_eq_integer`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponent_cast_eq_integer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the explicit integer nonnegativity hypothesis, the Nat exponent used by the polynomial casts back to the original integer rank-state exponent.

**Definition 1.4 (Signed rank-state term).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateTerm`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each subset state contributes its sign, rank power and (1+z) exponent to the integer polynomial.

**Definition 1.5 (Signed rank-state polynomial).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.statePolynomial`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.statePolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial is the finite sum over all edge-indexed subset states.

**Definition 1.6 (Forest states).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.forestStates`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.forestStates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

States with q(S)=|S| are selected as the forest part of the finite subset sum.

**Definition 1.7 (Cyclic states).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicStates`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicStates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

States with q(S)<|S| are selected as the cyclic part.

**Definition 1.8 (Coefficient of one state).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.termCoefficient`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.termCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient of z^k in one state term is the signed binomial contribution when q(S)≤k and is zero otherwise.

**Definition 1.9 (Ideal forest coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.idealCoefficient`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.idealCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The comparison coefficient is Ring.choose (−b) k over the integers.

**Theorem 1.10 (Negative-binomial coefficient formula).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.idealCoefficient_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.idealCoefficient_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ideal coefficient equals (−1)^k choose(b+k−1,k), including the b=k=0 boundary case.

**Theorem 1.11 (Exact state coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_stateTerm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_stateTerm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Polynomial coefficient extraction agrees with termCoefficient for every finite subset state.

**Theorem 1.12 (Exact finite coefficient sum).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_statePolynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_statePolynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient of the full state polynomial is the finite sum of the state coefficients.

**Definition 1.13 (Forest coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.forestCoefficient`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.forestCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forest contribution is the sum of termCoefficient over forestStates.

**Definition 1.14 (Cyclic coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicCoefficient`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cyclic contribution is the sum of termCoefficient over cyclicStates.

**Theorem 1.15 (Forest/cyclic coefficient split).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_split`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the rank upper bound, every state belongs to exactly one of the forest and cyclic filters, so the full coefficient splits into the two contributions.

**Definition 1.16 (Actual simple-graph edge predicate).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphEdgePredicate`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphEdgePredicate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph wrapper lifts SimpleGraph adjacency to the unordered edge type Sym2(Fin n).

**Definition 1.17 (Actual graph edge type).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphEdge`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph wrapper restricts the finite edge index type to the actual adjacency predicate, so nonedges are not duplicated in the subset state sum.

**Definition 1.18 (Actual graph rank state).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphRank`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph wrapper computes rank from the connected-component count of the image of the actual edge subset, including isolated vertices.

**Definition 1.19 (Actual graph state polynomial).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphStatePolynomial`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphStatePolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any positive vertex count, the polynomial sums over actual graph edge subsets. Exponent nonnegativity is proved from the component rank, rather than supplied as an extra premise.

**Definition 1.20 (Spanning graph of a state).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphOfState`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphOfState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph consists of the selected actual edges and retains every isolated vertex.

**Theorem 1.21 (Support bound from graph rank).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.support_card_le_twice_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.support_card_le_twice_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite graph has at most twice its graph rank in nonisolated vertices. The proof uses a spanning forest with the same reachability relation and the degree-sum formula.

**Theorem 1.22 (Actual rank inequalities).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graph_rank_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graph_rank_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a graph with a positive number of vertices, every state has rank at most its edge count and at most v minus one; the integer state exponent is nonnegative.

**Theorem 1.23 (State support bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graph_state_support_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graph_state_support_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual rank-j state graph has at most 2j nonisolated vertices.

**Definition 1.24 (Sources of an ordered pattern).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.orderedSources`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.orderedSources` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A source has no adjacent vertex earlier in the specified finite vertex order.

**Definition 1.25 (Forward neighbor carrier).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.forwardNeighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.forwardNeighbors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This carrier contains the actual later adjacent vertices of a vertex.

**Definition 1.26 (Bounded forward degree).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.boundedForwardDegree`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.boundedForwardDegree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supplied ordering has at most D later neighbors at every vertex. This is a graph property, not an assumed subset-count estimate.

**Definition 1.27 (Increasing graph embeddings).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.orderedEmbeddings`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.orderedEmbeddings` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Increasing vertex maps preserve all edges of the support pattern.

**Theorem 1.28 (Cyclic ordered embedding bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclic_ordered_embedding_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclic_ordered_embedding_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A cyclic simple pattern without isolated vertices has at most rank minus one source choices. A finite injection records source images and one bounded forward-neighbor slot for each remaining vertex, yielding the stated uniform embedding bound.

**Definition 1.29 (Finite cyclic support patterns).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicPatterns`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicPatterns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite carrier contains all simple patterns of the specified graph rank, with no isolated vertices and with an actual cycle.

**Definition 1.30 (Cyclic states of one rank).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicRankStates`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicRankStates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only subsets with graph rank exactly j and more than j edges belong to this filter.

**Theorem 1.31 (Cyclic graph rank is at least two).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclic_graph_rank_ge_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclic_graph_rank_ge_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual cyclic edge subset of a simple graph has rank at least two; this excludes rank zero and makes the first coefficient exact.

**Definition 1.32 (Uniform pattern constant).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicPatternConstant`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicPatternConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constant depends only on D and j through finite carriers of simple support graphs on at most 2j vertices.

**Theorem 1.33 (Rank-specific subset count).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclic_rank_state_count_vertices`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclic_rank_state_count_vertices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual rank-j cyclic edge subsets inject into finitely many increasing support-pattern embeddings. The exponent of the vertex-count factor is j minus one.

**Theorem 1.34 (Uniform connected-graph cyclic count).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclic_rank_state_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclic_rank_state_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Connectedness replaces the vertex factor by an edge-count factor. The bound is uniform over all carrier sizes and graphs with forward degree at most D.

**Theorem 1.35 (Rank-dependent state term growth).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graph_term_coefficient_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graph_term_coefficient_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rank-j state contributes at most 2 to the k times (e plus one) to the k minus j in absolute value. The exponent and binomial bound are derived from actual graph ranks and edge counts.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.boundedForwardDegree`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_split`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_statePolynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_stateTerm`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicCoefficient`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicPatternConstant`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicPatterns`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicRankStates`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicStates`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclic_graph_rank_ge_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclic_ordered_embedding_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclic_rank_state_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclic_rank_state_count_vertices`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.forestCoefficient`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.forestStates`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.forwardNeighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphEdge`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphEdgePredicate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphOfState`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphRank`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphStatePolynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graph_rank_bounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graph_state_support_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graph_term_coefficient_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.idealCoefficient`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.idealCoefficient_formula`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.orderedEmbeddings`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.orderedSources`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponent`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponentInteger`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponent_cast_eq_integer`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.statePolynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateTerm`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.support_card_le_twice_rank`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.termCoefficient`
- Dependency: [D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks](../Jacobi/LeafPruningRanks.md)
- Dependency: [D5/S3/Fourier/CharacterSelection/SimpleGraphCycleSpace](../../../Fourier/CharacterSelection/SimpleGraphCycleSpace.md)
