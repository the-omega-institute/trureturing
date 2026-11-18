# Matching counts relative to a maximum matching

## Abstract

Exact matching-count fibers and complementary coefficient domination for finite unweighted simple graphs, with no bound on the vertex order.

Problem 4.7 of Ball–Galvin–Hyry–Weingartner, arXiv:1901.06579v2, PDF page 17, asks for all weak sorting permutations of m(1),…,m(n) for graphs of matching number n, and their growth. The results here are necessary structural prerequisites. They supply neither a graph realizing each admitted order nor an enumeration of the actual realizable class. Ties remain in scope, and m(0) is excluded from the source permutations.

**Definition 1.1 (Outside matchings).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.outsideMatchings`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.outsideMatchings` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite edge sets E and Q on a finite vertex carrier, enumerate all pairwise vertex-disjoint subsets F of E minus Q, including the empty set.

**Definition 1.2 (Untouched matching edges).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.untouched`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.untouched` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite edge sets Q and F, retain precisely the q in Q sharing no vertex with any edge of F.

**Theorem 1.3 (Exact fiber cardinality).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.matching_fiber_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.matching_fiber_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q be a matching contained in E, let F be an outside matching, and let k be any natural number. Matchings M contained in E with cardinality k and M minus Q equal to F are counted by choose(card(untouched Q F),k−card F) if card F is at most k, and by zero otherwise. The bijection sends a subset A of untouched Q-edges to F union A; its inverse is M intersection Q. No maximality assumption is used.

**Theorem 1.4 (Partition of every coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.count_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.count_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite edge set E, every matching Q contained in E, and every k, cnt(E,k) is the sum of the guarded fiber cardinalities over all outside matchings F. Partitioning by M minus Q is exhaustive and unique.

**Theorem 1.5 (Original graph-count identity).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.matchingCount_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.matchingCount_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural vertex order N, simple graph G on Fin N, edge-decision instance, matching Q in G and natural k, the original matchingCount G k equals the same sum with E equal to G.edgeFinset. This consumes the original owner's matchingCount_eq_cnt bridge; vertex order N and matching size are separate parameters.

**Theorem 1.6 (Maximum-matching touch bounds).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.maximum_outside_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.maximum_outside_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every such G and matching Q with matchingNumber G equal to card Q, and every outside matching F, put t=card F and s=card Q−card(untouched Q F). Then t is at most s, and s is at most min(2t,card Q). The lower bound adjoins every untouched Q-edge to F. The upper bound injects touched Q-edges into the at most 2t vertices of F. All relations refer to this same graph and matching.

**Theorem 1.7 (Complementary matching-count comparison).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.matchingCount_complement_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.matchingCount_complement_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N, unweighted simple graph G on Fin N with decidable adjacency, and natural k with 2k at most matchingNumber G, matchingCount G k is at most matchingCount G (matchingNumber G−k). A maximum matching exists by the native count definition. Each exact fiber contributes a nonnegative complementary difference, by binomial symmetry and monotonicity. The theorem includes zero and the middle coefficient.

The exact source Problem 4.7 was reread in the fixed-version text. Repository and pinned Mathlib searches found the native count bridge and binomial suppliers, but no matching partition or sharp rigidity theorem in the searched scope. Crossref metadata identifies Farrell's 1992 paper On the theory of matching equivalent graphs and rook equivalent chessboards, DOI 10.1016/0016-0032(92)90095-X. Its primary text and the Kennedy primary text have not been verified here. No novelty or priority claim is made.

The four-slot escape audit remains unfinished under issue #31461. The dependent-family enrollment requires complete reconstruction of the varying graph, matching and count telescope, an exact readout bridge, whole-family variation and sensitivity, and actual observational dependence. Those audit data are not supplied by the combinatorial proof. No declared_validated registration is claimed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.count_partition`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.matchingCount_complement_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.matchingCount_partition`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.matching_fiber_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.maximum_outside_bounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.outsideMatchings`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/MatchingPartition.untouched`
- Dependency: [D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching](../ComponentPacking/FactorCriticalMatching.md)
