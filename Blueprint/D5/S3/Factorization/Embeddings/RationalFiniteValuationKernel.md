# Rational Finite-Valuation Kernel

## Abstract

Finite rational prime coordinates leave exactly a sign ambiguity.

**Theorem 1.1 (Finite valuations have kernel plus or minus one).**

$$\begin{gathered}\forall x, y\in RatUnits,\\{}let nu: RatUnits \to SignedPrimeLedger, \forall q, nu(q) = primeExponentEquivPositiveRational.symm(Additive.ofMul(Units.mk0(Rat.nnabs(q), \operatorname{nonzero}(q)))),\\{}(nu(x) = nu(y) \Rightarrow (x = y \lor x = -y))\\{}\land\\{}(\forall z\in RatUnits, nu(z) = 0 \iff (z = 1 \lor z = -1))\\{}\land\\{}(nu(x) = nu(y) \land \operatorname{sign}(x) = \operatorname{sign}(y) \Rightarrow x = y).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/RationalFiniteValuationKernel.rational_finite_valuation_kernel_and_sign_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the unit group of the rationals, so zero is excluded exactly as required by the finite prime-valuation profile. The displayed profile takes rational absolute value, packages it as a positive rational unit, and applies the canonical inverse signed-prime equivalence.

Equality of profiles therefore identifies absolute values and leaves only the two sign choices. The second public clause identifies the full kernel as one and minus one, rather than merely proving containment.

The final public clause adds equality of the archimedean sign. Opposite rational values then have opposite nonzero signs, so the remaining ambiguity is eliminated and the rationals are equal.

## References

- Truth anchor: `D5/S3/Factorization/Embeddings/RationalFiniteValuationKernel.rational_finite_valuation_kernel_and_sign_recovery`
- Dependency: [D5/S3/Factorization/PositiveRationalGroup](../PositiveRationalGroup.md)
