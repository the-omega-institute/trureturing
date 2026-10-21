# Derivations on Fraction Fields

## Abstract

An integer-linear derivation on an integral domain extends to every realization of its fraction field.

**Remark 1.1 (The extended derivation).**

Lean statement: `D5/S1/Recurrence/Algebraic/FractionFieldDerivation.extend`

*Formalization.* `D5/S1/Recurrence/Algebraic/FractionFieldDerivation.extend` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let R be an integral domain, F a fraction field of R, and D an integer-linear derivation from R to R. Map r to the dual number whose two coordinates are the images of r and D(r) in F. Every nonzero denominator maps to a unit because its first coordinate is nonzero. The universal property of localization extends this ring homomorphism to F. Its first coordinate is the identity on F, so its second coordinate is an integer-linear derivation. This construction is repository-derived from Mathlib's localization and trivial square-zero extension APIs.

**Theorem 1.2 (Agreement on the original domain).**

Lean statement: `D5/S1/Recurrence/Algebraic/FractionFieldDerivation.extend_algebraMap`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/FractionFieldDerivation.extend_algebraMap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r in R, the value of the extended derivation at the image of r in F equals the image of D(r). Consequently, a differential equation proved in the original domain remains valid after embedding into its fraction field.

**Theorem 1.3 (Uniqueness of the extension).**

Lean statement: `D5/S1/Recurrence/Algebraic/FractionFieldDerivation.extend_unique`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/FractionFieldDerivation.extend_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any integer-linear derivation on F that agrees with D on the image of R equals the constructed extension. Indeed, every x in F satisfies xb=a for images of some a,b in R with b nonzero. Differentiating this identity determines b times the derivative of x, and cancellation of b determines that derivative uniquely.

**Theorem 1.4 (Compatibility with further field extensions).**

Lean statement: `D5/S1/Recurrence/Algebraic/FractionFieldDerivation.extend_commutes`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/FractionFieldDerivation.extend_commutes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L be a field over F, with compatible embeddings of R, and let d be an integer-linear derivation on L. If d agrees with D on the embedded original domain R, then d commutes with the extended derivation on every element of F. The same differentiated identity xb=a proves the assertion after embedding into L and cancelling the image of the nonzero denominator b.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/FractionFieldDerivation.extend`
- Truth anchor: `D5/S1/Recurrence/Algebraic/FractionFieldDerivation.extend_algebraMap`
- Truth anchor: `D5/S1/Recurrence/Algebraic/FractionFieldDerivation.extend_commutes`
- Truth anchor: `D5/S1/Recurrence/Algebraic/FractionFieldDerivation.extend_unique`
