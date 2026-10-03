# Golden Cubic Compatibility Compositum

## Abstract

The actual golden cubic radical and cyclotomic fields carry a character-defined compatibility automorphism.

**Theorem 1.1 (Actual radical and cyclotomic compatibility data).**

Lean statement: `D5/S3/Factorization/Galois/GoldenCubicCompatibilityCompositum.actual_compositum_data`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/GoldenCubicCompatibilityCompositum.actual_compositum_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every j and unit residue a modulo 80 times 3 to the power j plus 2 whose image modulo three is one, the actual earlier block support and its oriented Eisenstein factors determine a complete cubic radical field M. The same selected roots and a primitive cyclotomic root define C and the compositum F. The radical and cyclotomic fields meet only in E.

The local cubic characters determine an automorphism of M on every selected root. The unit residue determines an automorphism of C; their product lifts to F. The lift acts by the specified character coordinates and cyclotomic residue, while rational Frobenius in its conjugacy class forces residue a. The statement concerns unrestricted rational primes and does not assert a prime divisor of the current finite block.

## References

- Truth anchor: `D5/S3/Factorization/Galois/GoldenCubicCompatibilityCompositum.actual_compositum_data`
- Dependency: [D5/S3/Factorization/Galois/Chebotarev/Main](Chebotarev/Main.md)
- Dependency: [D5/S3/Factorization/Galois/GoldenCubicCompleteCyclotomicDisjointness](GoldenCubicCompleteCyclotomicDisjointness.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/CubicIdealCharacter](../QuadraticIdeals/CubicIdealCharacter.md)
