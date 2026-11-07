# Complete spectral head isolation

## Abstract

Complete spectral head isolation

**Theorem 1.1 (Complete countable-spectrum real negative witness).**

Lean statement: `D5/S3/Constants/Moments/CountableHankelNegativeWitness.exists_real_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CountableHankelNegativeWitness.exists_real_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every index type iota, maps z and w from iota to the complex numbers, and permutation c of iota, assume: every node has norm at most one; z is injective; z(c(i)) is the complex conjugate of z(i); w(c(i)) is the conjugate of w(i); the sum over all i of norm(w(i)) is summable; and for every positive real r the set of indices with norm(z(i)) at least r is finite. For every index i0 whose node is nonreal and whose weight is nonzero, there exists a real-coefficient polynomial p such that the real part of the complete sum of w(i) times p(z(i)) squared is strictly negative.

The finite head consists of every node of norm at least norm(z(i0))/4, including all larger nodes. The existing finite conjugate interpolation proof supplies a real polynomial P taking i and minus i at the target pair and zero at every other head node. A complex square root chooses b with w(i0) b squared equal to minus one. The real polynomial q(m) is X to power m times [minus Re(b/z(i0) to power m) times P squared, plus Im(b/z(i0) to power m) times P]. The entire head sum is minus two.

If C is the coefficient absolute sum of P and B is norm(b) times (C squared plus C), every complementary value has norm at most B times (1/4) to power m. If W is the complete complementary absolute weight mass, the norm of its weighted ordinary-square sum is at most W B squared times (1/16) to power m. Absolute summability is proved before splitting the full sum into head and complement. A finite m makes this bound less than one. No node is discarded, and the square is the complex square, not a squared modulus.

**Theorem 1.2 (Integerization of strict finite quadratic negativity).**

Lean statement: `D5/S3/Constants/Moments/CountableHankelNegativeWitness.exists_integer_negative_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CountableHankelNegativeWitness.exists_integer_negative_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d, real matrix M indexed by Fin d in both coordinates, and real vector u on Fin d with sum over a and b of u(a) u(b) M(a,b) strictly negative, there exists an integer vector v on Fin d for which the same quadratic expression, after the integer-to-real casts, is strictly negative. Neither symmetry nor positive definiteness of M is assumed.

The finite quadratic form is continuous. Componentwise rational casts have dense range, so its negative open set contains a rational vector r. Encode r as a rational matrix with one Unit column. Matrix.den and Matrix.num give a common nonzero natural denominator D and integer vector v, with v(a)=D r(a) after casting to the reals. The form at v is exactly D squared times the form at r; D squared is strictly positive.

**Theorem 1.3 (Absolute convergence for every real polynomial).**

Lean statement: `D5/S3/Constants/Moments/CountableHankelNegativeWitness.square_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CountableHankelNegativeWitness.square_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every index type iota, complex maps z,w, node norm bound norm(z(i)) at most one for all i, summability of norm(w(i)) over all i, and real polynomial p, the complex series w(i) times the ordinary square of p evaluated at z(i) is summable. A finite coefficient absolute sum bounds every evaluation; summability follows by domination. It does not require node injectivity or any conjugation assumption.

**Theorem 1.4 (Existing real interpolation on one finite conjugate head).**

Lean statement: `D5/S3/Constants/Moments/CountableHankelNegativeWitness.pair_polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CountableHankelNegativeWitness.pair_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex node map z on any index type, permutation c with z(c(i))=conjugate(z(i)), finite set E invariant under c, index i0 in E, and nonreal z(i0), there exists a real polynomial p whose value at each z(i), i in E, is I when z(i)=z(i0), minus I when z(i)=conjugate(z(i0)), and zero otherwise. No injectivity of z is assumed in this helper. The proof applies NewtonHankelRealRootCriterion.exists_real_pair_interpolant to the finite node image.

**Definition 1.5 (Real peak polynomial with a chosen exponent).**

Lean statement: `D5/S3/Constants/Moments/CountableHankelNegativeWitness.peak`

*Formalization.* `D5/S3/Constants/Moments/CountableHankelNegativeWitness.peak` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real polynomial p, complex z0,b and natural m, peak p z0 b m is the real polynomial X to power m multiplied by [C of minus Re(b/z0 to power m) times p squared, plus C of Im(b/z0 to power m) times p]. The definition imposes no nonzero premise. Its value and localization properties use the separate peak_at and peak_bound hypotheses.

**Theorem 1.6 (Exact chosen value at the nonzero target).**

Lean statement: `D5/S3/Constants/Moments/CountableHankelNegativeWitness.peak_at`

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CountableHankelNegativeWitness.peak_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real polynomial p, complex z0,b, nonzero z0, p evaluated at z0 equal to I, and natural m, the evaluation of peak p z0 b m at z0 equals b. Evaluation uses I squared equal to minus one and cancellation of the nonzero target power.

**Theorem 1.7 (Quantitative localization of the original peak).**

Lean statement: `D5/S3/Constants/Moments/CountableHankelNegativeWitness.peak_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CountableHankelNegativeWitness.peak_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real polynomial p, complex z0,b,z, nonzero z0, norm(z) at most one, and natural m, the norm of peak p z0 b m evaluated at z is at most norm(b) times (C squared plus C) times (norm(z)/norm(z0)) to power m, where C is the sum over the support of p of the absolute value of its coefficients. This bound makes no interpolation assumption on p. The coefficient absolute-sum bound and the bounds on the real and imaginary parts of b/z0 to power m control this ordinary polynomial evaluation.

## References

- Truth anchor: `D5/S3/Constants/Moments/CountableHankelNegativeWitness.exists_integer_negative_quadratic`
- Truth anchor: `D5/S3/Constants/Moments/CountableHankelNegativeWitness.exists_real_negative`
- Truth anchor: `D5/S3/Constants/Moments/CountableHankelNegativeWitness.pair_polynomial`
- Truth anchor: `D5/S3/Constants/Moments/CountableHankelNegativeWitness.peak`
- Truth anchor: `D5/S3/Constants/Moments/CountableHankelNegativeWitness.peak_at`
- Truth anchor: `D5/S3/Constants/Moments/CountableHankelNegativeWitness.peak_bound`
- Truth anchor: `D5/S3/Constants/Moments/CountableHankelNegativeWitness.square_summable`
- Dependency: [D5/S3/Constants/NewtonHankelRealRootCriterion](../NewtonHankelRealRootCriterion.md)
