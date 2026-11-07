# Native scoped implementation

## Abstract

Real-endpoint four-term prime-counting expansion.

Native compiled scope only. The consumed theta remainder transfer and private finite FTC ratio helper support the original quantitative statements. This delivery does not claim final16, RH, or exact-infimum admission.

**Theorem 1.1 (Theta remainder at every fixed log power).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.theta_error_log_power`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.theta_error_log_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N, theta(x)-x is little-o of x/log(x)^N at real atTop, using the actual MediumPNT exponent 1/10 and the frozen psi-minus-theta transfer.

**Definition 1.2 (Four-term counting polynomial).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.countingPolynomial`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.countingPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

countingPolynomial x is x*(1/log x + 1/log(x)^2 + 2/log(x)^3 + 6/log(x)^4).

**Theorem 1.3 (Four terms with residual coefficient 24).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.prime_counting_four_terms`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.prime_counting_four_terms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real-endpoint residual (primeCount x-countingPolynomial x)/(x/log(x)^5) tends to 24 atTop. The primeCount definition includes the floor endpoint and no separate pi hypothesis is introduced.

**Theorem 1.4 (Uniform coefficient-25 consequence).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.prime_counting_four_terms_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.prime_counting_four_terms_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One threshold X>1 gives the uniform absolute error bound 25*x/log(x)^5 for every real x>=X. The finite-tail consumer uses this moving-endpoint envelope.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.countingPolynomial`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.prime_counting_four_terms`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.prime_counting_four_terms_uniform`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.theta_error_log_power`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/PrimeBoundaryAbel](PrimeBoundaryAbel.md)
- Dependency: [D5/S3/Weil/PrimeNumberTheorem/MediumPNT](../../../Weil/PrimeNumberTheorem/MediumPNT.md)
