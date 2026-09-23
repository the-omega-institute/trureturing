# Sahbi's hypercube sub-quorum conjecture

## Abstract

For every Boolean cube of dimension at least two, the largest number of colors in a sub-quorum coloring is exactly one parity class, namely two to the power n-1.

**Definition 1.1 (Source-faithful partial colorings).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeSubQuorum.IsSubQuorumColoring`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeSubQuorum.IsSubQuorumColoring` (`✓ std3`).

*Citation.* Rafik Sahbi (2026). *Sub-quorum colorings of graphs*. DOI: [10.48550/arXiv.2609.25128](https://doi.org/10.48550/arXiv.2609.25128). URL: <https://arxiv.org/html/2609.25128v1>.

*Commentary.*

A coloring consists of a finite colored support S in the Boolean cube and an onto map from S to the positive color type Fin k. At every colored vertex, the center together with its same-color colored neighbors is at least half of the center together with all colored neighbors. The center occurs once on each side, while uncolored neighbors do not enter either count. This is exactly Definition 2.2 of the source.

**Definition 1.2 (Attainable color counts).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeSubQuorum.SubQuorumAttainable`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeSubQuorum.SubQuorumAttainable` (`✓ std3`).

*Citation.* Rafik Sahbi (2026). *Sub-quorum colorings of graphs*. DOI: [10.48550/arXiv.2609.25128](https://doi.org/10.48550/arXiv.2609.25128). URL: <https://arxiv.org/html/2609.25128v1>.

*Commentary.*

A natural number k is attainable in dimension n when some finite support and onto admissible partial coloring use exactly k colors. Positivity is part of admissibility, rather than an external convention.

**Definition 1.3 (The attained bounded maximum).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeSubQuorum.subQuorumChromaticNumber`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeSubQuorum.subQuorumChromaticNumber` (`✓ std3`).

*Citation.* Rafik Sahbi (2026). *Sub-quorum colorings of graphs*. DOI: [10.48550/arXiv.2609.25128](https://doi.org/10.48550/arXiv.2609.25128). URL: <https://arxiv.org/html/2609.25128v1>.

*Commentary.*

The invariant is Nat.findGreatest over attainable k bounded by the number of cube vertices. Surjectivity bounds every attainable k by 2^n. A one-vertex, one-color support proves positive attainment in every dimension, so the default zero behavior of findGreatest on an empty predicate is never used; the selected maximum is itself attainable.

**Theorem 1.4 (The exact value in every dimension at least two).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeSubQuorum.subQuorumChromaticNumber_hypercube`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeSubQuorum.subQuorumChromaticNumber_hypercube` (`✓ std3`). ∎

*Resolves.* `Problems/sahbi-hypercube-subquorum` (proved) by `D5/S3/Combinatorics/Graph/HypercubeSubQuorum.subQuorumChromaticNumber_hypercube`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sahbi-hypercube-subquorum","declaration_gid":"D5/S3/Combinatorics/Graph/HypercubeSubQuorum.subQuorumChromaticNumber_hypercube","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Rafik Sahbi (2026). *Sub-quorum colorings of graphs*. DOI: [10.48550/arXiv.2609.25128](https://doi.org/10.48550/arXiv.2609.25128). URL: <https://arxiv.org/html/2609.25128v1>.

*Commentary.*

Fix an arbitrary admissible k-coloring. Split its colors into E, those with a colored internal edge, and N, those with none. Choose both ends of one edge for each color in E and one representative for each color in N. Distinct colors separate the choices, and the two ends of an edge differ, so the selected map is injective. If A is the set of all selected vertices and T the representatives of N, then |A|=|N|+2|E|, |T|=|N|, and |A|+|T|=2k.

For t in T there is no same-color neighbor. The sub-quorum inequality therefore gives colored degree at most one, hence t has at most one neighbor in A. Conversely each a in A has at most n-1 neighbors in T. This follows from the preceding bound when a lies in T, using n>=2. When a is selected from an edged class, its selected partner is a cube neighbor outside T, while every cube vertex has degree n.

The proof privately bridges the repository hypercube to Huang's symmetric signed adjacency operator from pinned Archive.Sensitivity. Its entries have absolute value one exactly on cube edges and its square is n times the identity. These matrix facts are Huang's Lemma 2.2, not a new result of this module. For a real vector supported on T, rowwise finite Cauchy-Schwarz and reverse summation give energy at most (n-1)||x||^2 on A. The full signed-cube identity gives total energy n||x||^2, leaving at least ||x||^2 on B, the complement of A.

Thus restriction of the signed operator defines an injective linear map from real functions on T to real functions on B. Finite-dimensional rank comparison yields |T|<=|B|. Combining |A|+|B|=2^n with |A|+|T|=2k gives k<=2^(n-1). For the reverse inequality, the even-parity vertices form an edgeless support and receive distinct colors; this is onto and admissible and has 2^(n-1) colors. Since the bounded maximum is attained, the two inequalities give equality.

Sahbi supplies Definition 2.2, the selection idea of Lemma 5.4, the cases through dimension six, and Conjecture 6.4. The repository-derived content is the restricted signed-matrix norm and dimension argument for arbitrary partial colorings. Prior-resolution searches are bounded and do not establish a worldwide novelty or priority claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeSubQuorum.IsSubQuorumColoring`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeSubQuorum.SubQuorumAttainable`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeSubQuorum.subQuorumChromaticNumber`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeSubQuorum.subQuorumChromaticNumber_hypercube`
- Dependency: [D5/S3/Combinatorics/Graph/Hypercube](Hypercube.md)
