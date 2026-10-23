# Regular graph adjacency energy excludes 2k√2

## Abstract

The adjacency energy of a regular graph cannot equal 2k√2 for a positive integer k.

**Definition 1.1 (Ramane–Kitturmath Conjecture 3.11).**

$$claim \Leftrightarrow (\forall (V : Type), [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall (r : \mathbb{N}), \operatorname{SimpleGraph.IsRegularOfDegree}\left(G, r\right) \Rightarrow \forall (k : \mathbb{N}), 0 < k \Rightarrow \operatorname{graphEnergy}\left(G, adjacency\right) \ne 2 \cdot (k : \mathbb{R}) \cdot \operatorname{Real.sqrt}\left(2\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/RegularGraphEnergyQuadraticExclusion.claim` (`✓ std3`).

*Citation.* H. S. Ramane; D. V. Kitturmath (2023). *On the conjecture of Sombor energy of a graph*. DOI: [10.1016/j.exco.2023.100115](https://doi.org/10.1016/j.exco.2023.100115). URL: <https://doi.org/10.1016/j.exco.2023.100115>.

*Commentary.*

Conjecture 3.11, page 8: "There is no regular graph with adjacency energy 2k√2, where k∈Z⁺." The source's adjacency energy is the sum of absolute values of the real adjacency eigenvalues, with multiplicities. The Lean encoding quantifies over every finite vertex type, its finite simple graph, a regular degree r, and every positive integer k; the graphEnergy and graphSpectrum definitions are the imported source definitions.

**Theorem 1.2 (The conjecture is proved).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall (r : \mathbb{N}), \operatorname{SimpleGraph.IsRegularOfDegree}\left(G, r\right) \Rightarrow \forall (k : \mathbb{N}), 0 < k \Rightarrow \operatorname{graphEnergy}\left(G, adjacency\right) \ne 2 \cdot (k : \mathbb{R}) \cdot \operatorname{Real.sqrt}\left(2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/RegularGraphEnergyQuadraticExclusion.result` (`✓ std3`). ∎

*Resolves.* `Problems/ramane-kitturmath-2023-regular-graph-energy-conjecture-3-11` (proved) by `D5/S3/Combinatorics/SpectralGraph/RegularGraphEnergyQuadraticExclusion.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ramane-kitturmath-2023-regular-graph-energy-conjecture-3-11","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/RegularGraphEnergyQuadraticExclusion.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* H. S. Ramane; D. V. Kitturmath (2023). *On the conjecture of Sombor energy of a graph*. DOI: [10.1016/j.exco.2023.100115](https://doi.org/10.1016/j.exco.2023.100115). URL: <https://doi.org/10.1016/j.exco.2023.100115>.

*Commentary.*

The characteristic polynomial has rational coefficients. Its real splitting field is normal, and an algebra automorphism sends a square root of 2 to its negative. The root multiset is invariant under this automorphism. A positive regular degree is a root, while the zero-sum root multiset and the positive-part estimate force the assumed energy identity to imply r ≤ 0. This contradicts the positive degree. The formula displays the complete proposition proved by result.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/RegularGraphEnergyQuadraticExclusion.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/RegularGraphEnergyQuadraticExclusion.result`
- Dependency: [D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation](../Graph/SubgroupGenerating/CyclicExtensionRefutation.md)
