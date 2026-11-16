# Affine alpha-z Renyi monotonicity with singular supported inputs

## Abstract

Affine alpha-z Renyi monotonicity with singular supported inputs

**Definition 1.1 (Affine scale).**

Lean statement: `D5/S3/Quantum/Divergence/AlphaZAffine/Result.affineZ`

*Formalization.* `D5/S3/Quantum/Divergence/AlphaZAffine/Result.affineZ` (`✓ std3`).

*Citation.* Fumio Hiai (2024). *Log-majorization and matrix norm inequalities with application to quantum information*. DOI: [10.1007/s44146-024-00142-w](https://doi.org/10.1007/s44146-024-00142-w). URL: <https://arxiv.org/abs/2402.16067>.

*Commentary.*

The scale is kappa times alpha plus a nonnegative offset.

**Definition 1.2 (The supported power product).**

Lean statement: `D5/S3/Quantum/Divergence/AlphaZAffine/Result.renyiProduct`

*Formalization.* `D5/S3/Quantum/Divergence/AlphaZAffine/Result.renyiProduct` (`✓ std3`).

*Citation.* Fumio Hiai (2024). *Log-majorization and matrix norm inequalities with application to quantum information*. DOI: [10.1007/s44146-024-00142-w](https://doi.org/10.1007/s44146-024-00142-w). URL: <https://arxiv.org/abs/2402.16067>.

*Commentary.*

The product is rho to alpha over twice z times sigma to one minus alpha over twice z. For nonzero exponents, CFC real powers vanish on the kernel; negative powers therefore invert on the support. At alpha one the sigma exponent is zero and CFC returns the identity; under support inclusion its extra kernel component is killed by the positive rho power. This cancellation concerns the sigma factor at alpha one only.

**Definition 1.3 (The singular-value trace moment).**

Lean statement: `D5/S3/Quantum/Divergence/AlphaZAffine/Result.traceMoment`

*Formalization.* `D5/S3/Quantum/Divergence/AlphaZAffine/Result.traceMoment` (`✓ std3`).

*Citation.* Fumio Hiai (2024). *Log-majorization and matrix norm inequalities with application to quantum information*. DOI: [10.1007/s44146-024-00142-w](https://doi.org/10.1007/s44146-024-00142-w). URL: <https://arxiv.org/abs/2402.16067>.

*Commentary.*

The real trace of the z power of X adjoint times X equals the sum of the singular values to power twice z.

**Definition 1.4 (The alpha-z trace).**

Lean statement: `D5/S3/Quantum/Divergence/AlphaZAffine/Result.renyiQ`

*Formalization.* `D5/S3/Quantum/Divergence/AlphaZAffine/Result.renyiQ` (`✓ std3`).

*Citation.* Fumio Hiai (2024). *Log-majorization and matrix norm inequalities with application to quantum information*. DOI: [10.1007/s44146-024-00142-w](https://doi.org/10.1007/s44146-024-00142-w). URL: <https://arxiv.org/abs/2402.16067>.

*Commentary.*

For positive alpha and positive z this agrees with the Hiai Section 3 trace functional. The real-valued formula is used on supported semidefinite pairs.

**Definition 1.5 (The divergence away from one).**

Lean statement: `D5/S3/Quantum/Divergence/AlphaZAffine/Result.renyiD`

*Formalization.* `D5/S3/Quantum/Divergence/AlphaZAffine/Result.renyiD` (`✓ std3`).

*Citation.* Fumio Hiai (2024). *Log-majorization and matrix norm inequalities with application to quantum information*. DOI: [10.1007/s44146-024-00142-w](https://doi.org/10.1007/s44146-024-00142-w). URL: <https://arxiv.org/abs/2402.16067>.

*Commentary.*

The logarithm of Q divided by the trace of rho, divided by alpha minus one. Its totalized value at one is unused; hiaiD supplies the Umegaki value there.

**Definition 1.6 (Normalized Umegaki entropy).**

Lean statement: `D5/S3/Quantum/Divergence/AlphaZAffine/Result.umegaki`

*Formalization.* `D5/S3/Quantum/Divergence/AlphaZAffine/Result.umegaki` (`✓ std3`).

*Citation.* Fumio Hiai (2024). *Log-majorization and matrix norm inequalities with application to quantum information*. DOI: [10.1007/s44146-024-00142-w](https://doi.org/10.1007/s44146-024-00142-w). URL: <https://arxiv.org/abs/2402.16067>.

*Commentary.*

The real trace of rho times the difference of log rho and log sigma divided by the real trace of rho. Finite spectral logarithms have value zero at zero, which implements the supported convention after multiplication by rho.

**Definition 1.7 (Hiai divergence including alpha one).**

Lean statement: `D5/S3/Quantum/Divergence/AlphaZAffine/Result.hiaiD`

*Formalization.* `D5/S3/Quantum/Divergence/AlphaZAffine/Result.hiaiD` (`✓ std3`).

*Citation.* Fumio Hiai (2024). *Log-majorization and matrix norm inequalities with application to quantum information*. DOI: [10.1007/s44146-024-00142-w](https://doi.org/10.1007/s44146-024-00142-w). URL: <https://arxiv.org/abs/2402.16067>.

*Commentary.*

For alpha equal to one this is normalized Umegaki entropy. At every other alpha it is the normalized logarithmic trace quotient. Support inclusion is a hypothesis of the theorem.

**Theorem 1.8 (Affine monotonicity on the full positive axis).**

Lean statement: `D5/S3/Quantum/Divergence/AlphaZAffine/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/AlphaZAffine/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/hiai-2024-affine-alpha-z-renyi-monotonicity` (proved) by `D5/S3/Quantum/Divergence/AlphaZAffine/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hiai-2024-affine-alpha-z-renyi-monotonicity","declaration_gid":"D5/S3/Quantum/Divergence/AlphaZAffine/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2024). *Log-majorization and matrix norm inequalities with application to quantum information*. DOI: [10.1007/s44146-024-00142-w](https://doi.org/10.1007/s44146-024-00142-w). URL: <https://arxiv.org/abs/2402.16067>.

*Commentary.*

In every finite complex matrix dimension, for nonzero positive semidefinite rho and positive semidefinite sigma with kernel sigma contained in kernel rho, positive kappa and nonnegative offset, the divergence along z equals kappa times alpha plus offset is nondecreasing for all positive alpha. The value at one is the prescribed Umegaki entropy. Joint convexity and the constant vertical normalization transfer the Petz tangent to every affine line. Simultaneous positive identity regularization converges in the supported power product: its kernel factor has the positive net exponent one over twice z. The entropy limit uses continuity of x log x and the same kernel cancellation. Passing inequalities through these limits proves the singular case. The Lean conclusion quantifies alpha greater than zero. If the offset is zero, alpha zero gives z zero and lies outside the source domain. If the offset is positive, the source alpha-zero endpoint is defined but is not quantified by result. The positive-alpha rho powers tend to the support projection as alpha decreases to zero. Theorem 3.1 and continuity give the source endpoint comparison: source literature proved or paper derived, not formalized. The totalized CFC rho power at alpha zero is the identity, so the formula there is not asserted to equal the source support-power value. The fixed-z case kappa equals zero is identified as Hiai Theorem 3.1(ii); extended infinite values outside support inclusion are discussed in the source note and are outside this real-valued theorem.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/AlphaZAffine/Result.affineZ`
- Truth anchor: `D5/S3/Quantum/Divergence/AlphaZAffine/Result.hiaiD`
- Truth anchor: `D5/S3/Quantum/Divergence/AlphaZAffine/Result.renyiD`
- Truth anchor: `D5/S3/Quantum/Divergence/AlphaZAffine/Result.renyiProduct`
- Truth anchor: `D5/S3/Quantum/Divergence/AlphaZAffine/Result.renyiQ`
- Truth anchor: `D5/S3/Quantum/Divergence/AlphaZAffine/Result.result`
- Truth anchor: `D5/S3/Quantum/Divergence/AlphaZAffine/Result.traceMoment`
- Truth anchor: `D5/S3/Quantum/Divergence/AlphaZAffine/Result.umegaki`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior](../../Entanglement/Witness/CorrelationMinorNormExterior.md)
- Dependency: [D5/S3/Quantum/Hiai/SupportPowerLimits](../../Hiai/SupportPowerLimits.md)
- Dependency: [D5/S3/Quantum/Schatten/Holder](../../Schatten/Holder.md)
- Dependency: [D5/S3/Quantum/Schatten/PowerMajorization](../../Schatten/PowerMajorization.md)
