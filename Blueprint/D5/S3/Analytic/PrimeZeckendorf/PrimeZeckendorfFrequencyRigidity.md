# Prime-Zeckendorf Frequency Rigidity

## Abstract

The calibrated first golden frequency removes abstract prime-relabeling freedom, and finite rational prime superpositions retain unique coefficients.

**Theorem 1.1 (First excited frequency separates prime relabelings).**

$$\operatorname{SeparatesPrimeRelabelings}(\operatorname{firstExcitedFrequencyReadout}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeZeckendorf/PrimeZeckendorfFrequencyRigidity.first_excited_frequency_separates_prime_relabelings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first excited frequency is phi squared times log p. Equality of this calibrated value forces equality of the prime channel, so an invariant prime relabeling fixes every prime.

The same module proves that pairing this frequency with the canonical Zeckendorf layer address is faithful and that the complete first-frequency family is rationally linearly independent. These are arithmetic rigidity statements; they do not derive log p from a cut-and-project carrier.

## References

- Truth anchor: `D5/S3/Analytic/PrimeZeckendorf/PrimeZeckendorfFrequencyRigidity.first_excited_frequency_separates_prime_relabelings`
- Dependency: [D5/S3/Analytic/PrimeZeckendorf/PrimeRelabelingUnderdetermination](PrimeRelabelingUnderdetermination.md)
- Dependency: [D5/S3/Analytic/PrimeZeckendorf/PrimeZeckendorfFrequencyBridge](PrimeZeckendorfFrequencyBridge.md)
- Dependency: [D5/S3/Weil/PrimeAddress/PrimeLogIndependence](../../Weil/PrimeAddress/PrimeLogIndependence.md)
