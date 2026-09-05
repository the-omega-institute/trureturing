# Prime-Zeckendorf Coordinates

## Abstract

A prime-local coordinate paired with a canonical Zeckendorf address is a faithful address for one golden Euler layer.

**Theorem 1.1 (Prime plus Zeckendorf depth is faithful).**

$$\operatorname{Injective}(\operatorname{primeZeckendorfReadout}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeZeckendorf/PrimeZeckendorfCoordinates.prime_zeckendorf_readout_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prime coordinate is retained and the layer coordinate is replaced by the canonical Zeckendorf equivalence, so the joint address loses no information.

This theorem establishes faithfulness of an already supplied arithmetic product coordinate. It does not derive prime labels from geometric projection data.

**Theorem 1.2 (A fixed prime-local factor sums Zeckendorf-addressed layers).**

$$\operatorname{germLocalFactor}(s, p) = \operatorname{tsum}(v, \operatorname{primeZeckendorfWeight}(s, (p, \operatorname{wEncoding}(v)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeZeckendorf/PrimeZeckendorfCoordinates.germLocalFactor_eq_prime_zeckendorf_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one fixed prime channel, the frozen golden local factor is exactly the sum over all natural layers after replacing each layer by its canonical Zeckendorf address.

The first excited layer retains the common phi-squared exponent used by the existing golden-germ zeta factorization.

## References

- Truth anchor: `D5/S3/Analytic/PrimeZeckendorf/PrimeZeckendorfCoordinates.germLocalFactor_eq_prime_zeckendorf_sum`
- Truth anchor: `D5/S3/Analytic/PrimeZeckendorf/PrimeZeckendorfCoordinates.prime_zeckendorf_readout_injective`
- Dependency: [D5/S0/Conventions/WDigits](../../../S0/Conventions/WDigits.md)
- Dependency: [D5/S3/ObserverMemory/Refinement/ProductCoordinateTransversality](../../ObserverMemory/Refinement/ProductCoordinateTransversality.md)
