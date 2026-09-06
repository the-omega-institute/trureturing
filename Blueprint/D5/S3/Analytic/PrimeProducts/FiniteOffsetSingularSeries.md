# Finite Offset Singular Series

## Abstract

Complete blocking is a finite prime check; the singular series is a convergent product of the local correlation factors over every prime.

**Theorem 1.1 (Finite blocking and the full numerical product).**

$$\forall H \in \operatorname{Finset}\left(\mathbb{Z}\right), k \in \mathbb{N},\; \operatorname{card}\left(H\right) = k \Rightarrow \left(\left(\forall p \in NatPrimes,\; k < p \Rightarrow \left(\operatorname{localResidueCount}\left(H, p\right) \le k \land \operatorname{localResidueCount}\left(H, p\right) < p\right)\right) \land \left(\left(\left(\forall p \in NatPrimes,\; \operatorname{localResidueCount}\left(H, p\right) < p\right) \Leftrightarrow \left(\forall p \in NatPrimes,\; p \le k \Rightarrow \operatorname{localResidueCount}\left(H, p\right) < p\right)\right) \land \operatorname{HasProd}\left((p: NatPrimes \mapsto \frac{1 - \frac{\operatorname{localResidueCount}\left(H, p\right)}{p}}{\left(1 - \frac{1}{p}\right)^{\operatorname{card}\left(H\right)}}), \operatorname{tprod}\left((p: NatPrimes \mapsto \frac{1 - \frac{\operatorname{localResidueCount}\left(H, p\right)}{p}}{\left(1 - \frac{1}{p}\right)^{\operatorname{card}\left(H\right)}})\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries.finite_offset_blocking_and_singular_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite set H contains integer offsets. localResidueCount(H,p) counts the image of h mapped to minus h in ZMod p. The displayed lambda is offsetLocalFactor(H), and its tprod is offsetSingularSeries(H); both use the full prime index.

The frozen residue criterion supplies the two blocking clauses. Beyond the maximum distance between offsets, the residue map is injective. An inductive quadratic binomial remainder bound then bounds the absolute local-factor deviation by C divided by p squared, where C depends only on H.

Summability of these deviations gives HasProd at the displayed all-prime product. Neither admissibility nor nonemptiness is assumed: a blocked configuration may have a zero local factor.

## References

- Truth anchor: `D5/S3/Analytic/PrimeProducts/FiniteOffsetSingularSeries.finite_offset_blocking_and_singular_series`
- Dependency: [D5/S3/Analytic/PrimeProducts/FiniteLocalResidueBlockingCriterion](FiniteLocalResidueBlockingCriterion.md)
- Dependency: [D5/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples](FormalFactorTableCounterexamples.md)
