# Prime-Relabeling Underdetermination

## Abstract

Golden depth and Zeckendorf structure are invariant under arbitrary prime relabeling, so canonical prime localization requires additional arithmetic rigidity.

**Theorem 1.1 (Layer observation cannot distinguish prime relabeling).**

$$\forall r, \operatorname{layerReadout} \circ \operatorname{primeRelabeling}(r) = \operatorname{layerReadout}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeZeckendorf/PrimeRelabelingUnderdetermination.layer_readout_prime_relabeling_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every equivalence of the prime type can relabel the local coordinate while leaving the entire golden layer coordinate unchanged.

The same relabeling also preserves the Zeckendorf component. Thus layer geometry alone cannot canonically identify which local label is the arithmetic prime two, three, five, and so on.

**Theorem 1.2 (The explicit prime readout has relabeling rigidity).**

$$\operatorname{SeparatesPrimeRelabelings}(\operatorname{primeReadout}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeZeckendorf/PrimeRelabelingUnderdetermination.prime_readout_separates_prime_relabelings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An observable satisfies the new rigidity criterion when invariance under a prime relabeling forces every prime to be fixed.

The explicit prime projection satisfies this condition. A future geometric-to-prime map must establish comparable rigidity from valuation, norm, divisibility, adelic, or spectral structure rather than by attaching anonymous labels.

## References

- Truth anchor: `D5/S3/Analytic/PrimeZeckendorf/PrimeRelabelingUnderdetermination.layer_readout_prime_relabeling_invariant`
- Truth anchor: `D5/S3/Analytic/PrimeZeckendorf/PrimeRelabelingUnderdetermination.prime_readout_separates_prime_relabelings`
- Dependency: [D5/S3/Analytic/PrimeZeckendorf/PrimeZeckendorfCoordinates](PrimeZeckendorfCoordinates.md)
