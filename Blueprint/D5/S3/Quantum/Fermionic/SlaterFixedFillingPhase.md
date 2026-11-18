# Slater shuffle signs at fixed filling

## Abstract

Slater shuffle signs at fixed filling

**Theorem 1.1 (Particle and hole inversion counts).**

Lean statement: `D5/S3/Quantum/Fermionic/SlaterFixedFillingPhase.crossCount_particle_hole`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/SlaterFixedFillingPhase.crossCount_particle_hole` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For retained occupations a contained in I and discarded occupations b contained in J, count the pairs j < i in each of the four products of occupied and empty subsets. The occupied inversion count plus the count for all sites equals the sum of the two one-sided occupied counts and the hole inversion count.

**Definition 1.2 (Separate phases on the supported occupations).**

Lean statement: `D5/S3/Quantum/Fermionic/SlaterFixedFillingPhase.Factors`

*Formalization.* `D5/S3/Quantum/Fermionic/SlaterFixedFillingPhase.Factors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There are two integer-valued factors, one depending on the occupation of each side, whose product is the occupied shuffle sign for every pair of subsets with total size k.

**Theorem 1.3 (Phase factorization at extreme fillings).**

Lean statement: `D5/S3/Quantum/Fermionic/SlaterFixedFillingPhase.factors_of_extreme_filling`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/SlaterFixedFillingPhase.factors_of_extreme_filling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any retained and discarded site sets, the degree-k phase factors whenever k is at most one or the number of sites is at most k plus one. A supported pair then has at most one occupied site or at most one hole. In the latter case the hole inversion count vanishes and the particle and hole identity gives the factors.

**Theorem 1.4 (Alternating cuts at intermediate filling).**

Lean statement: `D5/S3/Quantum/Fermionic/SlaterFixedFillingPhase.not_factors_of_alternating`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/SlaterFixedFillingPhase.not_factors_of_alternating` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For disjoint retained and discarded site sets, take two sites from each side in either strictly increasing alternating order. If k is at least two and k plus two is at most the combined size, choose k minus two spectators outside the alternating sites and hold their occupations fixed. The two diagonal inversion counts of the resulting occupation rectangle differ by exactly one in total from the off-diagonal counts. Any row and column factorization would give the same product of signs along both pairs of opposite corners.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterFixedFillingPhase.Factors`
- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterFixedFillingPhase.crossCount_particle_hole`
- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterFixedFillingPhase.factors_of_extreme_filling`
- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterFixedFillingPhase.not_factors_of_alternating`
- Dependency: [D5/S3/Quantum/Fermionic/SlaterCutPhase](SlaterCutPhase.md)
