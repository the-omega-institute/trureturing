# Exact binary Hamming dimension of permutation prefixes

## Abstract

For every ground-set size at least three, the least dimension of a unit binary Hamming cube realizing twice Rossi's atom metric is twelve at size four and two to the ground-set size minus two otherwise.

**Definition 1.1 (Unordered prefixes).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathrm{Perm}\left(\mathrm{Fin}\left(n\right)\right),\; \forall k \in \mathbb{N},\; \mathrm{prefixSet}\left(p, k\right) = \{p\left(i\right) \mid i \in \mathrm{Fin}\left(n\right), i < k\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.prefixSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The prefix set collects the values at zero-based positions below k. The rank argument is any natural number.

**Definition 1.2 (Proper ranks).**

$$\forall n \in \mathbb{N},\; \mathrm{Rank}\left(n\right) = \{k \mid k \in \mathrm{Fin}\left(n\right), 0 < k\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.Rank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proper ranks are the positive positions strictly below the ground-set size.

**Definition 1.3 (Scaled prefix distance).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathrm{Perm}\left(\mathrm{Fin}\left(n\right)\right),\; \forall q \in \mathrm{Perm}\left(\mathrm{Fin}\left(n\right)\right),\; \mathrm{prefixDistance}\left(p, q\right) = 2 \cdot \mathrm{card}\left(\{k \mid k \in \mathrm{Rank}\left(n\right), \mathrm{prefixSet}\left(p, k\right) \ne \mathrm{prefixSet}\left(q, k\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.prefixDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each proper rank at which the unordered prefixes differ contributes two.

**Definition 1.4 (The dimension threshold).**

$$\forall n \in \mathbb{N},\; \mathrm{minimumDimension}\left(n\right) = \begin{cases}12&n = 4\\2^{n} - 2&\text{otherwise}\end{cases}$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.minimumDimension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The threshold gives the least feasible dimension for ground-set sizes at least three.

**Theorem 1.5 (Exact dimension and all feasible paddings).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; 3 \le n \Rightarrow ((\exists f \in \mathrm{Perm}\left(\mathrm{Fin}\left(n\right)\right) \to \mathrm{Fin}\left(d\right) \to \mathrm{Bool},\; \forall p \in \mathrm{Perm}\left(\mathrm{Fin}\left(n\right)\right),\; \forall q \in \mathrm{Perm}\left(\mathrm{Fin}\left(n\right)\right),\; \mathrm{hammingDist}\left(f\left(p\right), f\left(q\right)\right) = 2 \cdot \mathrm{card}\left(\{k \mid k \in \mathrm{Rank}\left(n\right), \mathrm{prefixSet}\left(p, k\right) \ne \mathrm{prefixSet}\left(q, k\right)\}\right)) \Leftrightarrow \begin{cases}12&n = 4\\2^{n} - 2&\text{otherwise}\end{cases} \le d)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.minimum_hamming_dimension` (`✓ std3`). ∎

*Resolves.* `Problems/rossi-2026-prefix-hamming-dimension` (proved) by `D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.minimum_hamming_dimension`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rossi-2026-prefix-hamming-dimension","declaration_gid":"D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.minimum_hamming_dimension","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

For each natural n at least three and each natural d, the formula asks for one map on all permutations into d Boolean coordinates. The ordinary Hamming distance of its two values must exactly equal twice the number of unequal proper prefixes for every pair. The cut families recover the permutations, so preservation at this scale implies injectivity.

For the lower bound, an adjacent exchange at a rank gives the difference of two prefix-incidence basis vectors. Paths of exchanges realize every difference at that rank. Polarization transfers the pairings of these integer sums to any distance-preserving binary map. At a fixed rank, subtract one reference basis vector. The resulting nonzero vectors have two signed coordinates each and pairwise inner product one. Their supports are distinct intersecting pairs, hence form a star or a triangle. Orthogonality across ranks forces disjoint coordinate supports. Adding the resulting rank bounds gives the stated threshold.

For attainment, concatenate one-hot words for the possible prefixes at each rank. A rank with four prefixes uses instead the three-bit words 000, 011, 101, and 110, which have distance two for distinct words. For n at least three this saving occurs only at the two outer ranks for n equal to four. Extra zero coordinates preserve every distance, giving the map for all dimensions above the threshold.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.Rank`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.minimumDimension`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.minimum_hamming_dimension`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.prefixDistance`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.prefixSet`
- Dependency: [D5/S3/Combinatorics/Graph/DUFStructure](../DUFStructure.md)
