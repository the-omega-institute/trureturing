# Convergence and the exact quadratic height law

## Abstract

Convergence and the exact quadratic height law.

**Theorem 1.1 (Convergence and the exact quadratic height law).**

Lean statement: `D5/S3/Factorization/Mordell/CanonicalPointHeight.canonicalHeight_properties`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/CanonicalPointHeight.canonicalHeight_properties` (`✓ std3`). ∎

*Citation.* Michael Stoll; David Kurniadi Angdinata; The Tau Ceti contributors; Kevin Buzzard (2026). *Canonical heights, parallelogram constructions and arithmetic point transport*. URL: <https://github.com/TauCetiProject/TauCeti/tree/934db6ae0034643ffe7b5180242f9ec4c00a56ae>.

*Commentary.*

For a field with admissible absolute values and an elliptic Weierstrass curve, the sequence h(2^n P)/(2 times 4^n) converges to canonicalHeight(P) for every point P. One real constant D bounds the absolute difference between canonicalHeight(P) and h(P)/2 for every P. For all P and Q, the heights of P + Q and P - Q sum to twice the sum of their heights. These conclusions require no Northcott assumption.

The symmetric-square identity and projective height estimates give a uniform two-point defect. Its specialization to doubling gives summable successive differences, convergence and the bounded comparison. Dividing the full defect by 2 times 4^n and passing to the limit gives the exact parallelogram law. The normalization is half the projective x-coordinate height; positive height from infinite order additionally uses Northcott.

## References

- Truth anchor: `D5/S3/Factorization/Mordell/CanonicalPointHeight.canonicalHeight_properties`
- Dependency: [D5/S3/Factorization/Mordell/SymmetricSquareAddition](SymmetricSquareAddition.md)
- Dependency: [D5/S3/QuadraticForms/ParallelogramConstruction](../../QuadraticForms/ParallelogramConstruction.md)
