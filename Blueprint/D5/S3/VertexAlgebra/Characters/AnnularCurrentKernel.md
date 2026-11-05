# Annular Current Kernel

## Abstract

The annular Lambert kernel, its absolute convergence, and its identification with the existing regularized Weierstrass function.

**Definition 1.1 (Exponential coordinate).**

Lean statement: `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.expCoord`

*Formalization.* `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.expCoord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The multiplicative coordinate is exp(2 pi i w). For a modulus tau in the upper half-plane and 0 < Im w < Im tau, the coordinates satisfy 0 < norm q < norm z < 1, where q = exp(2 pi i tau) and z = exp(2 pi i w).

**Definition 1.2 (The torus period pair).**

Lean statement: `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.periodPair`

*Formalization.* `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.periodPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The periods are exactly 1 and tau. Their real linear independence follows by taking imaginary parts and using Im tau > 0. The associated lattice and Weierstrass function are the original Mathlib PeriodPair constructions.

**Definition 1.3 (Independent split radii).**

Lean statement: `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.splitKernel`

*Formalization.* `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.splitKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The split kernel is the sum over positive integers n of n times (q1^n + q2^n)/(1 - (q1 q2)^n). Its two radial parameters are independent. For norm q1 < 1, setting q2 = 0 leaves the geometric first moment q1/(1-q1)^2; symmetrically the other zero face is q2/(1-q2)^2, and setting both split radii to zero gives zero. These are split-kernel faces, with no annular value assigned at z = 0.

**Definition 1.4 (The ordinary annular kernel).**

Lean statement: `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.annularKernel`

*Formalization.* `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.annularKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For nonzero z, substitute q1 = q/z and q2 = z into the split kernel. The denominator is then 1 - q^n. This substitution is singular at z = 0; it supplies no annular boundary value there and no joint zero limit.

**Theorem 1.5 (Absolute convergence in the strict annulus).**

Lean statement: `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.annular_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.annular_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every strict strip point, both n z^n and n (q/z)^n are summable geometric first moments. Multiplication by the bounded inverse denominator preserves absolute summability in the complex finite-dimensional normed space. No desired convergence is assumed.

**Theorem 1.6 (The exact elliptic kernel identity).**

Lean statement: `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.annular_kernel_eq_periodPair_weierstrassP_sub_E2`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.annular_kernel_eq_periodPair_weierstrassP_sub_E2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every upper-half-plane tau and 0 < Im w < Im tau, the ordinary annular kernel equals PeriodPair.weierstrassP w divided by (2 pi i)^2, minus the normalized EisensteinSeries.E2 tau divided by 12. The lattice sum retains its regularizing subtraction during reindexing by the existing latticeEquivProd. Only after absolute summability gives Fubini are the horizontal row sums separated. EisensteinSeries.qExpansion_identity_pnat at k = 1 is applied directly to upper-half-plane arguments and to the reflected lower rows. Absolute double geometric sums give the annular Lambert series; the zero row contributes pi^2/3 by Basel, and the remaining constant rows use summable_prod_mul_pow and tsum_prod_pow_eq_tsum_sigma at k = 1, followed by EisensteinSeries.E2_eq_tsum_cexp. The zero-row value is taken from e2Summand_zero_eq_two_riemannZeta_two and riemannZeta_two; the conditional symmetric-Icc definition of G2 is never treated as an absolute two-dimensional sum.

The factor (2 pi i)^2 is the square of the additive-to-multiplicative coordinate Jacobian. For an ordinary multiplicative current J, the additive field is (2 pi i) z J(z); an actual field trace requires its own operator calculation and both coordinate factors. The scalar identity here does not evaluate that original-field trace. The function of w on the right-hand side is globally meromorphic and has periods 1 and tau by the existing Weierstrass API. Its restriction to the strict strip agrees with the kernel; periodicity beyond that strip is a property of this continuation. Full charged traces, VOA sewing, anomalies, fusion, string theory and AdS/CFT require separate results.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.annularKernel`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.annular_kernel_eq_periodPair_weierstrassP_sub_E2`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.annular_summable`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.expCoord`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.periodPair`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/AnnularCurrentKernel.splitKernel`
