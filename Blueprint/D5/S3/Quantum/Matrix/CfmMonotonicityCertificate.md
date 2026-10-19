# The rational functional-calculus expression

## Abstract

A scalar rational function agrees with its matrix expression under functional calculus.

**Definition 1.1 (The scalar rational counterexample).**

$$scalarFunction\left(t\right) = \frac{t + 1}{t + 3} + \frac{t + 1}{2 \cdot t + 4} - \frac{1}{20000} \cdot \frac{t + 1}{3 \cdot t + 5}$$

*Formalization.* `D5/S3/Quantum/Matrix/CfmMonotonicityCertificate.scalarFunction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

scalarFunction t = (t+1)/(t+3) + (t+1)/(2t+4) - (1/20000)(t+1)/(3t+5). Its total real extension is used by continuous functional calculus; all matrix inputs have strictly positive spectrum.

**Definition 1.2 (Rational matrix expression).**

$$rationalFunction\left(A\right) = \left(A + 1\right) \cdot \left(A + 3\right)^{-1} + \left(A + 1\right) \cdot \left(smul\left(2, A\right) + 4\right)^{-1} - smul\left(\frac{1}{20000}, \left(A + 1\right) \cdot \left(smul\left(3, A\right) + 5\right)^{-1}\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/CfmMonotonicityCertificate.rationalFunction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a complex square matrix of any finite size, rationalFunction A is (A+I)(A+3I) inverse plus (A+I)(2A+4I) inverse minus (1/20000) times (A+I)(3A+5I) inverse. Every scalar multiplication in the Lean definition uses the real scalar action. The inverse is Mathlib's nonsingular matrix inverse.

**Definition 1.3 (The diagonal lower endpoint).**

$$lowerMatrix = diagonal\left((\frac{1}{3}, 1, 3)\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/CfmMonotonicityCertificate.lowerMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

lowerMatrix is the complex Hermitian 3 by 3 diagonal matrix with diagonal 1/3, 1, 3.

**Definition 1.4 (The upper endpoint).**

$$smul\left(25, upperMatrix\right) = rows\left((11, 4, 8), (4, 31, 12), (8, 12, 99)\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/CfmMonotonicityCertificate.upperMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

upperMatrix is 1/25 times the symmetric matrix whose rows are (11,4,8), (4,31,12), (8,12,99), regarded as a complex Hermitian matrix.

**Definition 1.5 (The separating vector).**

$$testVector = (-35, 48, -15)$$

*Formalization.* `D5/S3/Quantum/Matrix/CfmMonotonicityCertificate.testVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

testVector is the complex column vector (-35,48,-15).

**Definition 1.6 (Real quadratic form).**

$$quadraticReadout\left(X\right) = Re\left(adjoint\left(testVector\right) \cdot X \cdot testVector\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/CfmMonotonicityCertificate.quadraticReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

quadraticReadout X is the real part of the conjugate-transpose quadratic form testVector adjoint times X times testVector. It is defined on every complex 3 by 3 matrix.

**Theorem 1.7 (Functional calculus of the rational function).**

$$\forall (n: Nat), \forall (A: ComplexSquareMatrix\left(n\right)), PosDef\left(A\right) \Rightarrow cfc\left(scalarFunction, A\right) = rationalFunction\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CfmMonotonicityCertificate.cfc_rationalFunction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural number n and every positive definite complex n by n matrix A, cfc scalarFunction A equals rationalFunction A. The spectrum is finite, so all scalar functions are continuous there. Its nonnegative spectrum makes all three affine denominators strictly positive. cfc_map_div, cfc_add_const and cfc_const_mul_id identify each rational term with its matrix counterpart; Matrix.nonsing_inv_eq_ringInverse identifies the two inverse conventions.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CfmMonotonicityCertificate.cfc_rationalFunction`
- Truth anchor: `D5/S3/Quantum/Matrix/CfmMonotonicityCertificate.lowerMatrix`
- Truth anchor: `D5/S3/Quantum/Matrix/CfmMonotonicityCertificate.quadraticReadout`
- Truth anchor: `D5/S3/Quantum/Matrix/CfmMonotonicityCertificate.rationalFunction`
- Truth anchor: `D5/S3/Quantum/Matrix/CfmMonotonicityCertificate.scalarFunction`
- Truth anchor: `D5/S3/Quantum/Matrix/CfmMonotonicityCertificate.testVector`
- Truth anchor: `D5/S3/Quantum/Matrix/CfmMonotonicityCertificate.upperMatrix`
- Dependency: [D5/S3/Quantum/Matrix/RadialConvexity](RadialConvexity.md)
