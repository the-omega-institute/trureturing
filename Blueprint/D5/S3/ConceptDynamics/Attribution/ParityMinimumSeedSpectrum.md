# Fixed counts at the least coloured parity budget

## Abstract

The smallest uniform seed budget has an exact coordinate fixed-count spectrum.

**Theorem 1.1 (The even-word cuts at the least positive seed budget).**

$$\forall n \in Nat,\; \forall z \in \operatorname{CountVectors}\left(n\right),\; \operatorname{RealizedAtMinimum}\left(n, z\right) \Leftrightarrow \operatorname{EvenCutCounts}\left(n, z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParityMinimumSeedSpectrum.exact_minimal_budget_fixed_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CountVectors(n) consists of the natural-valued functions on Fin(n+2). RealizedAtMinimum(n,z) means an equally weighted seed set of size 2^(n+3) with equivariant readouts to the two uniformly distributed coloured parity classes has exactly z(i) seeds fixed by the subgroup acting at coordinate i.

Let M = 2^n. EvenCutCounts(n,z) means there is an integer vector a with 0 <= a(i) <= M and z(i) = 4(M-a(i)) at every coordinate. For every even binary word e, the sum of a(i) at its zero coordinates and M-a(i) at its one coordinates is at least M.

Each coloured marginal fibre contains two seeds. If two seeds share both outputs, they fill both fibres. Equivariance then forces both outputs to have the same stabilizer. A coordinate at which the two parity profiles differ has a generator that fixes just one output.

The joint readout is injective, so equivariance identifies fixed seeds with seeds over fixed output pairs. The normalized mismatch vector gives the cuts and the common-one counts. Conversely, a coupling furnished by the cuts lifts to an equivariant seed action by taking the four colour combinations.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParityMinimumSeedSpectrum.exact_minimal_budget_fixed_counts`
- Dependency: [D5/S3/Combinatorics/Graph/Hypercube/ParityMismatchCounts](../../Combinatorics/Graph/Hypercube/ParityMismatchCounts.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedCountSpectrum](ParitySeedCountSpectrum.md)
