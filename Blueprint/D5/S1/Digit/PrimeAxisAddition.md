# Prime-Axis Normalized Addition

## Abstract

Rowwise W normalization of prime-axis table sums decodes as multiplication.

**Theorem 1.1 (Rowwise normalized addition and decoder multiplication).**

$$\forall z,w \in \operatorname{PrimeAxisTable},\ \operatorname{Bijective}(\operatorname{primeAxisEncoding}) \land \operatorname{decodePrimeAxisTable}(\operatorname{normalizedPrimeAxisAdd}(z,w)) = \operatorname{decodePrimeAxisTable}(z)\operatorname{decodePrimeAxisTable}(w)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxisAddition.prime_axis_addition_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prime-indexed canonical W rows are equivalent to positive naturals. Adding raw rows and applying the existing local W normalizer preserves exponent sums, so the finite prime-power decoder turns the normalized table sum into multiplication.

## References

- Truth anchor: `D5/S1/Digit/PrimeAxisAddition.prime_axis_addition_spec`
- Dependency: [D5/S1/Digit/PrimeAxisEncoding](PrimeAxisEncoding.md)
