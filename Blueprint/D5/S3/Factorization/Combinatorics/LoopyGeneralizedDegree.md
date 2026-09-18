# Ordinary Loopy equality leaves the generalized degree polynomial free

## Abstract

Two eight-vertex trees, each carrying a single loop, have one common ordinary Loopy polynomial and two different generalized degree polynomials.

The generalized degree polynomial of Crew records, for every subset S of the vertex set, the size of S, the number of edges with both endpoints in S, and the number of edges with exactly one endpoint in S. A loop lies inside S exactly when its vertex does, and never crosses. Two graphs carry the same generalized degree polynomial exactly when these exponent triples agree with multiplicity, so the multiset of triples is a faithful record of it.

The two graphs below are trees on the vertices 0 through 7 with one loop each. Both have degree multiset 1, 1, 1, 1, 2, 2, 3, 5. Running the deletion-contraction recursion of the ordinary Loopy polynomial to its 128 leaves gives one and the same polynomial of 25 monomials. The exponent triples separate them: among the subsets of size two that span two inside edges and two crossing edges there is exactly one for the first graph and exactly two for the second.

**Definition 1.1 (Edges inside a subset).**

Lean statement: `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.inside`

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.inside` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

inside E ell S counts the edge occurrences with both endpoints in S and adds the accumulated loops carried by the members of S.

**Definition 1.2 (Edges leaving a subset).**

Lean statement: `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.crossing`

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.crossing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

crossing E S counts the edge occurrences with exactly one endpoint in S. A loop never contributes.

**Definition 1.3 (The exponent triples of the generalized degree polynomial).**

Lean statement: `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.gdTriples`

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.gdTriples` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

gdTriples maps every subset of the vertex set to the triple of its size, its inside count and its crossing count, retaining multiplicity.

**Definition 1.4 (The common vertex set).**

Lean statement: `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.V`

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.V` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

V is the eight vertices 0 through 7.

**Definition 1.5 (The first graph).**

Lean statement: `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.EG`

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.EG` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

EG is a tree on V with one loop at vertex 1; the loop is stored as the pending edge occurrence from 1 to 1, and the remaining seven occurrences are 0-1, 0-5, 1-2, 1-4, 2-3, 5-6 and 5-7.

**Definition 1.6 (The second graph).**

Lean statement: `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.EH`

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.EH` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

EH is a tree on V with one loop at vertex 4; the remaining seven occurrences are 0-1, 0-4, 0-7, 1-2, 2-3, 4-5 and 4-6.

**Definition 1.7 (The determination claim).**

Lean statement: `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.claim`

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

claim asserts that for independent vertex sets, edge lists and loop accumulators, two valid encodings with equal ordinary Loopy polynomials have equal exponent-triple multisets. There is no looplessness, connectedness, simplicity or equal-order premise.

**Theorem 1.8 (The determination claim is false).**

Lean statement: `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.result`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.result` (`✓ std3`). ∎

*Resolves.* `Problems/loopy-generalized-degree-polynomial` (refuted) by `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"loopy-generalized-degree-polynomial","declaration_gid":"D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Both encodings retain every endpoint and store no loops away from the vertex set. The deletion-contraction recursion, run to its leaves on each graph, yields the same polynomial, so the hypothesis of the claim is met. The exponent-triple multisets differ, which contradicts its conclusion. Eight vertices is the smallest order at which this happens among trees carrying a single loop: at orders three through seven every pair with a common ordinary Loopy polynomial also has a common exponent-triple multiset.

## References

- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.EG`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.EH`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.V`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.claim`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.crossing`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.gdTriples`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.inside`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.result`
- Dependency: [D5/S3/Factorization/Combinatorics/LoopyEvaluator](LoopyEvaluator.md)
