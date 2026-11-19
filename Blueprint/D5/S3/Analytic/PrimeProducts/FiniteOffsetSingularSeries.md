# Finite Offset Singular Series

## Abstract

Complete blocking is a finite prime check; the singular series is a convergent product of the local correlation factors over every prime.

**Definition 1.1 (offset local factor).**

Lean statement: `D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries.offsetLocalFactor`

*Formalization.* `D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries.offsetLocalFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite set H of integer offsets and a prime p, the local factor is (1-localResidueCount(H,p)/p) divided by (1-1/p) raised to the cardinality of H.

**Definition 1.2 (offset singular series).**

Lean statement: `D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries.offsetSingularSeries`

*Formalization.* `D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries.offsetSingularSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The singular series of a finite set of integer offsets is the infinite product of offsetLocalFactor over all primes.

**Theorem 1.3 (local residue count eq card of diameter lt).**

Lean statement: `D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries.local_residue_count_eq_card_of_diameter_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries.local_residue_count_eq_card_of_diameter_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every absolute difference between two integer offsets in H is at most a natural diameter, then for every natural modulus p larger than that diameter the forbidden-residue count modulo p equals the cardinality of H.

**Theorem 1.4 (binomial remainder le).**

Lean statement: `D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries.binomial_remainder_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries.binomial_remainder_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x in [0,1] and every natural n, the difference between (1-x)^n and 1-nx is at most n squared times x squared.

**Theorem 1.5 (Finite blocking and the full numerical product).**

$$\forall H \in \operatorname{Finset}\left(\mathbb{Z}\right), k \in \mathbb{N},\; \operatorname{card}\left(H\right) = k \Rightarrow \left(\left(\forall p \in NatPrimes,\; k < p \Rightarrow \left(\operatorname{localResidueCount}\left(H, p\right) \le k \land \operatorname{localResidueCount}\left(H, p\right) < p\right)\right) \land \left(\left(\left(\forall p \in NatPrimes,\; \operatorname{localResidueCount}\left(H, p\right) < p\right) \Leftrightarrow \left(\forall p \in NatPrimes,\; p \le k \Rightarrow \operatorname{localResidueCount}\left(H, p\right) < p\right)\right) \land \operatorname{HasProd}\left((p: NatPrimes \mapsto \frac{1 - \frac{\operatorname{localResidueCount}\left(H, p\right)}{p}}{\left(1 - \frac{1}{p}\right)^{\operatorname{card}\left(H\right)}}), \operatorname{tprod}\left((p: NatPrimes \mapsto \frac{1 - \frac{\operatorname{localResidueCount}\left(H, p\right)}{p}}{\left(1 - \frac{1}{p}\right)^{\operatorname{card}\left(H\right)}})\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries.finite_offset_blocking_and_singular_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite set H contains integer offsets. localResidueCount(H,p) counts the image of h mapped to minus h in ZMod p. The displayed lambda is offsetLocalFactor(H), and its tprod is offsetSingularSeries(H); both use the full prime index.

The frozen residue criterion supplies the two blocking clauses. Beyond the maximum distance between offsets, the residue map is injective. An inductive quadratic binomial remainder bound then bounds the absolute local-factor deviation by C divided by p squared, where C depends only on H.

Summability of these deviations gives HasProd at the displayed all-prime product. Neither admissibility nor nonemptiness is assumed: a blocked configuration may have a zero local factor.

## References

- Truth anchor: `D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries.binomial_remainder_le`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries.finite_offset_blocking_and_singular_series`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries.local_residue_count_eq_card_of_diameter_lt`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries.offsetLocalFactor`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries.offsetSingularSeries`
- Dependency: [D5/S3/Analytic/PrimeProducts/FiniteLocalResidueBlockingCriterion](FiniteLocalResidueBlockingCriterion.md)
- Dependency: [D5/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples](FormalFactorTableCounterexamples.md)
