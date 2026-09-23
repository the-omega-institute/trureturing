# Refutation of the panchromatic pairing conjecture

## Abstract

A six-vertex hypergraph refutes the proposed equality between panchromatic and bipanchromatic extrema.

**Definition 1.1 (Lalou--Mbarek--Skender--Togni Conjecture 1).**

$$(claim) \Leftrightarrow (\forall V \in FiniteType, H \in Hypergraph\left(V\right), p \in \mathbb{N}, b \in \mathbb{N}, a \in \mathbb{N},\; ((IsPanchromaticMaximum\left(H, p\right)) \land \left((IsBipanchromaticMaximum\left(H, b\right)) \land (IsSingletonMinimum\left(H, p, a\right))\right)) \Rightarrow (b = p - ceilDiv\left(a, 2\right)))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/PanchromaticPairingConjectureRefutation.claim` (`✓ std3`).

*Citation.* Mohammed Lalou; Nader Mbarek; Abdallah Skender; Olivier Togni (2026). *Completely Independent Spanning Trees in Split Graphs: Structural Properties and Complexity*. DOI: [10.48550/arXiv.2512.15486](https://doi.org/10.48550/arXiv.2512.15486). URL: <https://arxiv.org/abs/2512.15486v2>.

*Commentary.*

For a finite set-valued hypergraph, p and b are attained maxima over all panchromatic and bipanchromatic color counts. The value a is an attained minimum of the number of globally singleton color fibers over all maximizing p-colorings. The claim states b = p - ceil(a/2).

**Theorem 1.2 (Conjecture 1 is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/PanchromaticPairingConjectureRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lalou-mbarek-skender-togni-conjecture-one-refutation` (refuted) by `D5/S3/ConceptDynamics/GraphColoring/PanchromaticPairingConjectureRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lalou-mbarek-skender-togni-conjecture-one-refutation","declaration_gid":"D5/S3/ConceptDynamics/GraphColoring/PanchromaticPairingConjectureRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Lalou; Nader Mbarek; Abdallah Skender; Olivier Togni (2026). *Completely Independent Spanning Trees in Split Graphs: Structural Properties and Complexity*. DOI: [10.48550/arXiv.2512.15486](https://doi.org/10.48550/arXiv.2512.15486). URL: <https://arxiv.org/abs/2512.15486v2>.

*Commentary.*

On vertices 0 through 5, take the three edges {0,1,2,3}, {0,1,2,4}, and {0,1,2,5}. Their panchromatic maximum is four. Every maximizing coloring has the three core colors globally singleton and a common petal color, so the minimum singleton count is three. The bipanchromatic maximum is three. Thus the left side is 3 while the proposed right side is 4 - ceil(3/2) = 2.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/PanchromaticPairingConjectureRefutation.claim`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/PanchromaticPairingConjectureRefutation.result`
