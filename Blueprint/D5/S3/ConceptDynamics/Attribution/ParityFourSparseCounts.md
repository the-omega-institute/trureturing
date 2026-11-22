# Fixed seeds at a single coordinate in dimension four

## Abstract

The budget threshold for exactly four fixed seeds concentrated at one coordinate.

**Theorem 1.1 (The least multiplier is two).**

$$\forall k \in Nat,\; \forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{Realizable}\left(2, k, \operatorname{FourAt}\left(i\right)\right) \Leftrightarrow 2 \le k$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParityFourSparseCounts.exact_four_sparse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

FourAt(i) has value four at i and zero at each other coordinate. Realizable(2,k,z) requires an equivariant seed action with 32k seeds, uniform coloured even and odd parity marginals, and fixed counts z.

At multiplier one the all-ones even word gives a cut that excludes the prescribed vector. At multiplier zero the seed set is empty. For two and three, two explicit integer tables specify the preimage multiplicities at each output point. They satisfy both coloured marginals and their odd entries supply exactly the required fixed seeds through the orbit fibre criterion.

At larger multipliers, adjoining an even block with zero fixed counts preserves the same vector. A permutation of the four coordinates moves the construction to any prescribed coordinate.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParityFourSparseCounts.exact_four_sparse`
- Dependency: [D5/S3/ConceptDynamics/Attribution/CoordinateFibreCounts](CoordinateFibreCounts.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParityMinimumSeedSpectrum](ParityMinimumSeedSpectrum.md)
