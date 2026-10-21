# Derivations on Fraction Fields

## Abstract

An integer-linear derivation on an integral domain extends to every realization of its fraction field.

Generality G: the integral domain and its fraction field are arbitrary. Extension and compatibility are classical differential algebra.

**Remark 1.1 (The extended derivation).**

Lean statement: `D5/S1/DifferentialAlgebra/FractionFieldDerivation.extend`

*Formalization.* `D5/S1/DifferentialAlgebra/FractionFieldDerivation.extend` (`✓ std3`).

*Citation.* James Ax (1971). *On Schanuel's conjectures*. DOI: [10.2307/1970774](https://doi.org/10.2307/1970774). URL: <https://annals.math.princeton.edu/1971/93-2/p03>.

*Commentary.*

Let R be an integral domain, F a fraction field of R, and D an integer-linear derivation from R to R. Map r to the dual number whose two coordinates are the images of r and D(r) in F. Every nonzero denominator maps to a unit because its first coordinate is nonzero. The universal property of localization extends this ring homomorphism to F. Its first coordinate is the identity on F, so its second coordinate is an integer-linear derivation. This formalization of the classical extension construction uses Mathlib's localization and trivial square-zero extension APIs.

**Theorem 1.2 (Agreement on the original domain).**

Lean statement: `D5/S1/DifferentialAlgebra/FractionFieldDerivation.extend_algebraMap`

*Proof.* Machine-checked in Lean as `D5/S1/DifferentialAlgebra/FractionFieldDerivation.extend_algebraMap` (`✓ std3`). ∎

*Citation.* James Ax (1971). *On Schanuel's conjectures*. DOI: [10.2307/1970774](https://doi.org/10.2307/1970774). URL: <https://annals.math.princeton.edu/1971/93-2/p03>.

*Commentary.*

For every r in R, the value of the extended derivation at the image of r in F equals the image of D(r). Consequently, a differential equation proved in the original domain remains valid after embedding into its fraction field.

**Theorem 1.3 (Compatibility with further field extensions).**

Lean statement: `D5/S1/DifferentialAlgebra/FractionFieldDerivation.extend_commutes`

*Proof.* Machine-checked in Lean as `D5/S1/DifferentialAlgebra/FractionFieldDerivation.extend_commutes` (`✓ std3`). ∎

*Citation.* James Ax (1971). *On Schanuel's conjectures*. DOI: [10.2307/1970774](https://doi.org/10.2307/1970774). URL: <https://annals.math.princeton.edu/1971/93-2/p03>.

*Commentary.*

Let L be a field over F, with compatible embeddings of R, and let d be an integer-linear derivation on L. If d agrees with D on the embedded original domain R, then d commutes with the extended derivation on every element of F. This is a bind-only compatibility helper, consumed by the kAmbientDifferential and hAmbientDifferential instances in ExponentialDifferentialField. The differentiated identity xb=a proves it after embedding into L and cancelling the image of the nonzero denominator b.

## References

- Truth anchor: `D5/S1/DifferentialAlgebra/FractionFieldDerivation.extend`
- Truth anchor: `D5/S1/DifferentialAlgebra/FractionFieldDerivation.extend_algebraMap`
- Truth anchor: `D5/S1/DifferentialAlgebra/FractionFieldDerivation.extend_commutes`
