# Taylor correction of compression operators

## Abstract

A convergent inverse-square-root Taylor series corrects an almost involution in an associative Banach algebra.

Let A be a complete real normed associative algebra with norm-one identity. For an operator T with norm of T squared minus identity strictly less than one, define S by the Taylor series of (1+z) to the power minus one half, evaluated at T squared minus identity. The corrected compression is one half of the sum of identity and TS. This is the construction in Kitaev, Almost-idempotent quantum channels and approximate C*-algebras, arXiv:2405.02434v2, equations (3.4)-(3.6) and (7.1).

**Theorem 1.1 (The Taylor compression is idempotent).**

$$\forall T\in A, \Vert T^{2}-1\Vert <1 \implies \operatorname{correction}\left(T\right)^{2}=\operatorname{correction}\left(T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Approximate/Compression.correction_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Absolute convergence follows by comparison with the scalar binomial series. Its Cauchy product is evaluated by the Chu-Vandermonde identity, giving S squared equal to the geometric series in identity minus T squared. The geometric-series identity gives T squared times S squared equal to identity. Commutation then proves exact idempotence.

The intended algebra A is the associative algebra of continuous linear endomorphisms. No multiplication instance is imposed on the nonassociative target space. This result supplies the analytic correction after the operator smallness estimate has been proved; it does not supply mixed-corner saturation, the corrected matrix action, or a matrix-block extension.

**Theorem 1.2 (The Taylor correction is close to the midpoint).**

$$\forall T\in A, \operatorname{norm}\left(\operatorname{correction}\left(T\right)-\frac{1}{2} \cdot (1+T)\right) \le \frac{1}{2} \cdot \operatorname{norm}\left(T\right) \cdot \operatorname{norm}\left(\operatorname{inverseSqrt}\left(T^{2}-1\right)-1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Approximate/Compression.correction_closeness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The correction differs from the uncorrected midpoint by one half of T times the inverse-square-root Taylor tail. Submultiplicativity gives the displayed bound without adding any structure to the target space.

**Theorem 1.3 (A linear bound for the Taylor tail).**

$$\operatorname{norm}\left(\operatorname{inverseSqrt}\left(d\right)-1\right)\le\operatorname{norm}\left(d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Approximate/Compression.inverseSqrt_tail_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In every complete real normed associative algebra with norm-one identity, if the norm of d is at most one half, then the norm of the inverse-square-root Taylor tail is at most the norm of d. The coefficients are identified with the already established central-binomial coefficients in OriginalHalfBinomialIntegral.b_multichoose. Its binomial_hasSum gives the scalar majorant 1/sqrt(1-norm(d))-1. This is at most norm(d) on the stated interval.

**Theorem 1.4 (Taylor correction preserves real intertwiners).**

$$\operatorname{s}\left(\operatorname{correction}\left(T, x\right)\right)=\operatorname{correction}\left(U, \operatorname{s}\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Approximate/Compression.correction_intertwines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E and F be complete nontrivial complex normed spaces, s a continuous real-linear map from E to F, and T and U continuous complex-linear endomorphisms. If s(Tx)=U(sx) for every x, and both square defects have norm strictly less than one, then the same intertwining identity holds for their Taylor corrections. The proof transports the convergent series term by term; it applies to the actual conjugate-linear star symmetry without imposing an associative algebra structure on H.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Approximate/Compression.correction_closeness`
- Truth anchor: `D5/S3/Quantum/Algebra/Approximate/Compression.correction_idempotent`
- Truth anchor: `D5/S3/Quantum/Algebra/Approximate/Compression.correction_intertwines`
- Truth anchor: `D5/S3/Quantum/Algebra/Approximate/Compression.inverseSqrt_tail_linear`
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialIntegral](../../../Analytic/OriginalHalfBinomialIntegral.md)
