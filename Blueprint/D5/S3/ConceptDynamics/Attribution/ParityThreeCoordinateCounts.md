# Three-dimensional fixed-seed counts at every budget

## Abstract

The full integer fixed-count spectrum of three uniformly coloured parity coordinates.

**Theorem 1.1 (The box, total bound, and odd-budget cuts characterize attainable vectors).**

$$\forall k \in Nat,\; \forall z \in \operatorname{CountVectors}\left(3\right),\; \operatorname{Realizable}\left(1, k, z\right) \Leftrightarrow \left(\exists u \in \operatorname{CountVectors}\left(3\right),\; \left(\forall i \in \operatorname{Fin}\left(3\right),\; z_{i} = 4 \cdot u_{i}\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(3\right),\; u_{i} \le 2 \cdot k\right) \land \left(\operatorname{Total}\left(u\right) \le 4 \cdot k \land \left(\operatorname{Odd}\left(k\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(3\right),\; 2 \cdot u_{i} \le \operatorname{Total}\left(u\right) + 2 \cdot (k - 1)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParityThreeCoordinateCounts.exact_three_coordinate_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CountVectors(3) is the type of natural-valued functions on Fin(3). Total(u) sums the three entries. Odd(k) means k has remainder one modulo two, and k minus one is truncated subtraction. Realizable(1,k,z) requires an equivariant seed action with 16k seeds, uniform coloured even and odd marginals, and actual coordinate fixed counts z.

The orbit fibre criterion supplies one multiplicity and one fixed count at each coordinate fixing the output points of the orbit. The ordinary cells are four-point orbits. Each cell in the all-ones odd column contains one two-point orbit per right colour. When k is odd, an entry u(i) of 2k forces the other entries to sum to at least two. An entry of 2k minus one forces them to sum to at least one.

The minimum-budget criterion supplies the multiplier-one block. Four pairs of matchings give products of coordinate ranges. Sorting and the total bound select a pair for each multiplier-two vector. Decompositions add these blocks within the stated bounds and preserve both marginals.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParityThreeCoordinateCounts.exact_three_coordinate_counts`
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParityMinimumSeedSpectrum](ParityMinimumSeedSpectrum.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedBudget](ParitySeedBudget.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedCountSpectrum](ParitySeedCountSpectrum.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParityThreeOrbitTable](ParityThreeOrbitTable.md)
