# Unique Prime-Axis Normalization

## Abstract

Every rowwise prime-axis sum has one canonical normalization, whose decoder is multiplication.

**Theorem 1.1 (Rowwise prime-axis normalization is unique).**

$$\forall z,w \in \operatorname{PrimeAxisTable},\ \exists! result \in \operatorname{PrimeAxisTable},\ (\forall p \in \operatorname{PrimeAxis},\ \operatorname{CanonicalRaw}(result.\operatorname{digits}(p)) \land \operatorname{rawValue}(result.\operatorname{digits}(p)) = \operatorname{rawValue}(z.\operatorname{digits}(p)) + \operatorname{rawValue}(w.\operatorname{digits}(p))) \land \operatorname{decodePrimeAxisTable}(result) = \operatorname{decodePrimeAxisTable}(z) \cdot \operatorname{decodePrimeAxisTable}(w)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxis/PrimeAxisNormalizationUnique.normalized_prime_axis_add_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The result type enforces finite support, while the predicate states legality and exact axiswise preservation explicitly: every output row is canonical and represents the sum of the two input-row exponents. Existence is the established rowwise normalizer. Uniqueness follows independently on each prime axis from uniqueness of canonical W digits at a fixed raw value; extensionality then identifies the whole table.

The same unique result satisfies the decoder equation already proved for rowwise normalization, so PZG table addition followed by normalization is ordinary multiplication after decoding.

## References

- Truth anchor: `D5/S1/Digit/PrimeAxis/PrimeAxisNormalizationUnique.normalized_prime_axis_add_unique`
- Dependency: [D5/S1/Digit/PrimeAxisAddition](../PrimeAxisAddition.md)
