# The native prime-67 splitting readout

## Abstract

Prime 67 is a certified native clock with least splitting-readout period sixteen.

**Theorem 1.1 (The native polynomial splitting readout has exact least period sixteen).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicPrime67Clock.native_67_least_period`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicPrime67Clock.native_67_least_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed Lucas residues form a checked sixteen-state cycle. The finite-field root tests give a sixteen-letter word, and each shorter positive shift fails at an explicitly checked position. The two-state word is read from the polynomial, not presumed from the input period.

**Theorem 1.2 (An isolated initial positive read forces a large least period).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicPrime67Clock.unbounded_of_split_inert_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicPrime67Clock.unbounded_of_split_inert_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive read followed by a long run of negative reads excludes each shorter period. The unbounded version requires that such prefixes are realizable at every length and that each probe is purely periodic; no prime-density theorem is asserted.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicPrime67Clock.native_67_least_period`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicPrime67Clock.unbounded_of_split_inert_prefix`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCyclic](GoldenCubicNativeCyclic.md)
