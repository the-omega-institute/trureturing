# Original C3 pair events on one circle inventory

## Abstract

Original C3 pair events on one circle inventory

**Theorem 1.1 (Original C3 pair events on one circle inventory).**

$$\forall r \in \mathrm{Nat},\; \forall T \in \mathrm{Finset}\left(\mathrm{Fin}\left(r\right)\right),\; ((12 \le r) \land (\mathrm{card}\left(T\right) \le 3)) \Rightarrow (\mathrm{card}\left(\mathrm{AdjacencyIntersection}\left(r, T\right)\right) = 2^{\mathrm{card}\left(T\right)} \cdot \mathrm{factorial}\left(2 \cdot r - \mathrm{card}\left(T\right) - 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/PairedCircleEvents.adjacency_intersection_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

AdjacencyIntersection(r,T) is the subset of circles(alphabet(r)) realizing adjacency i for every i in T. This count uses one common oriented circle space.

The original alphabet in Fin r to ZMod 3 consists of the distinct signed coordinate vectors. A coordinate subset I gives its actual union of opposite pairs, of cardinality 2 times card(I). Complementation of coordinate subsets corresponds exactly to complementation in the original alphabet.

For any prescribed coordinate subset T of size at most three and r at least twelve, the common-circle contraction yields exactly 2^card(T) times (2r-card(T)-1)! simultaneous adjacency circles. Enumerating the coordinate subsets gives the binomial moments consumed by the third Bonferroni estimate.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/PairedCircleEvents.adjacency_intersection_card`
- Dependency: [D5/S3/Combinatorics/CircularWords/SimultaneousPairContraction](../CircularWords/SimultaneousPairContraction.md)
- Dependency: [D5/S3/Combinatorics/Sequenceability/PairedZeroSubsetSpectrum](PairedZeroSubsetSpectrum.md)
