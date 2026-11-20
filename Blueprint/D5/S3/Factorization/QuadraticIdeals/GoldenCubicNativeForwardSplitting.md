# Forward splitting through the native cubic tower

## Abstract

An earlier block prime splits in every later cyclic field.

**Theorem 1.1 (Earlier divisibility forces a fixed later polynomial reduction).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeForwardSplitting.later_cubic_map_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeForwardSplitting.later_cubic_map_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The next Lucas coordinate vanishes modulo the earlier prime and stays zero. The canonical polynomial reduces to X times X minus three times X plus three. The three roots are distinct at primes greater than three.

**Theorem 1.2 (The full later residue algebra is the product of three prime fields).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeForwardSplitting.earlier_prime_residue_product`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeForwardSplitting.earlier_prime_residue_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit integral trace lattice supplies a conductor multiplier coprime to the earlier prime. The Kummer-Dedekind quotient and the Chinese Remainder Theorem then identify the actual ring of integers modulo that prime with three copies of its prime field.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeForwardSplitting.earlier_prime_residue_product`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeForwardSplitting.later_cubic_map_eq`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCyclicOrder](GoldenCubicNativeCyclicOrder.md)
