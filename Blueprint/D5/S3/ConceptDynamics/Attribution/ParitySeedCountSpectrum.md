# Attainable fixed counts for coloured parity seeds

## Abstract

The actual fixed-seed counts of coloured parity couplings obey orbit divisibility.

**Theorem 1.1 (Fourfold divisibility of each coordinate fixed count).**

$$\forall n \in Nat,\; \forall A \in \operatorname{UniformRealizations}\left(n\right),\; \forall i \in \operatorname{Coordinates}\left(n\right),\; \exists q \in Nat,\; \operatorname{FixedCount}\left(A, i\right) = 4 \cdot q$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParitySeedCountSpectrum.coordinate_fixed_count_four_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinates(n) is Fin(n+2). UniformRealizations(n) consists of finite seed sets with the coordinate colour action and an equivariant map into the even and odd coloured profile sets. Each possible output in either readout has the same seed count. FixedCount(A,i) counts seeds fixed by the subgroup acting in coordinate i.

The seeds whose output pair is fixed by that subgroup have total count divisible by four. Separate out those moved by the generator. A two-point seed orbit mapping to a moving output orbit maps bijectively, so on this subset every orbit has size divisible by four. The difference is the actual fixed count.

**Theorem 1.2 (When every coordinate has zero fixed count).**

$$\forall n \in Nat,\; \forall k \in Nat,\; \operatorname{Realizable}\left(n, k, \operatorname{ZeroVector}\left(n\right)\right) \Leftrightarrow (\operatorname{Odd}\left(n + 2\right) \lor \operatorname{Even}\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParitySeedCountSpectrum.zero_coordinate_counts_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Realizable(n,k,z) means that one uniform coloured parity realization with 2 to the power n+3 times k seeds gives count vector z. ZeroVector(n) is zero in every coordinate.

Complement pairing works in odd dimension. In even dimension a fibre above one colour of the all-ones output has size 2k. If every fixed count vanishes, each orbit in this fibre has size divisible by four. Conversely, an even budget multiplier permits a binary label flipped by every coordinate generator.

**Theorem 1.3 (Exact fixed-count vectors in dimension two).**

$$\forall k \in Nat,\; \forall z \in \operatorname{CountVectors}\left(0\right),\; \operatorname{Realizable}\left(0, k, z\right) \Leftrightarrow (\exists s \in Nat,\; \exists t \in Nat,\; z = \operatorname{PairVector}\left(4 \cdot s, 4 \cdot t\right) \land (s + t \le k \land (\operatorname{Even}\left(k\right) \lor 0 < s + t)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParitySeedCountSpectrum.exact_two_coordinate_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CountVectors(n) consists of natural-valued functions on Coordinates(n). PairVector(a,b) gives the counts a and b in the first and second coordinates.

Every vector is bounded by an attained boundary vector and each entry is divisible by four. A disjoint union adds both counts and budget multipliers. An implementation with sixteen seeds and counts (4,0), and its coordinate swap, provide the extra unit of multiplier when the unused multiplier is odd.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParitySeedCountSpectrum.coordinate_fixed_count_four_dvd`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParitySeedCountSpectrum.exact_two_coordinate_counts`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParitySeedCountSpectrum.zero_coordinate_counts_iff`
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedOptimization](ParitySeedOptimization.md)
