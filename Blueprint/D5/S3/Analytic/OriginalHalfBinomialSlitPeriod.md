# The Original Period on the Slit Plane

## Abstract

Principal Euler continuation of the literal half-binomial-square period.

**Definition 1.1 (The period domain).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitDomain`

*Formalization.* `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A parameter r belongs to the slit domain when 1 − r belongs to the principal complex slit plane.

**Definition 1.2 (The complementary period domain).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.doubleSlit`

*Formalization.* `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.doubleSlit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both r and 1 − r belong to the principal complex slit plane.

**Definition 1.3 (Euler's principal integral).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod`

*Formalization.* `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Integrate the principal complex power (1 − r sin² θ)^(−1/2) on [0, π/2] and multiply by 2/π.

**Theorem 1.4 (Differentiation under the integral).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_differentiableAt`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_differentiableAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the slit domain the kernel stays off the branch cut. Its parameter derivative is bounded on a smaller closed parameter disk times the integration interval. Dominated differentiation proves complex differentiability.

**Theorem 1.5 (Holomorphy on the slit domain).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_analyticOnNhd`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_analyticOnNhd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Euler period is holomorphic on a neighborhood of every point of the open slit domain.

**Theorem 1.6 (Equality with the original series).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_eq_period`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_eq_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the full open unit disk the Euler period equals OriginalHalfBinomialPeriod.period. The dominated sine-moment calculation identifies the real values, and holomorphic uniqueness extends the equality to complex parameters.

**Theorem 1.7 (Positive real part).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_re_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_re_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The principal square root has positive real part off its cut. Its reciprocal has the same strict sign, which persists under the normalized integral.

**Theorem 1.8 (Nonvanishing of the period).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive real part excludes zeros everywhere on the slit domain.

**Definition 1.9 (The complementary ratio).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.tau`

*Formalization.* `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.tau` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the Euler period at 1 − r by i and divide by the Euler period at r.

**Theorem 1.10 (Positive imaginary part of the complementary ratio).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.tau_im_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.tau_im_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pair the conjugate kernel at r with the kernel at 1 − r. Their product has positive real part from the imaginary parts of the square roots and of their squared product. Integrating twice and dividing by the squared norm of the period gives the strict sign.

**Theorem 1.11 (Pfaff preserves the slit domain).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.pfaff_mem_slitDomain`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.pfaff_mem_slitDomain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complement of r/(r − 1) is the reciprocal of 1 − r and stays off the cut.

**Theorem 1.12 (The Pfaff transformation).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.pfaff`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.pfaff` (`✓ std3`). ∎

*Citation.* NIST Digital Library of Mathematical Functions (2026). *Hypergeometric function, Pfaff transformation*. URL: <https://dlmf.nist.gov/15.8.E1>.

*Commentary.*

On the full slit domain the period at r/(r − 1) equals the principal square root of 1 − r times the period at r. This is DLMF 15.8.1 at a = b = 1/2 and c = 1, with the period normalization from DLMF 19.5.1. The Lean proof reflects the real integration variable about π/4 for real r < 1 and extends the identity to the slit domain by analytic uniqueness.

**Theorem 1.13 (The exact complementary Wronskian).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slit_wronskian`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slit_wronskian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the double slit, r(1 − r) times the sum of P′(r)P(1 − r) and P(r)P′(1 − r) equals 1/π. The disk identities also identify the local derivatives, so the existing lens Wronskian extends by uniqueness.

**Theorem 1.14 (The quotient derivative).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.tau_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.tau_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complex derivative of the complementary ratio is −i/(π r (1 − r) P(r)²) on the double slit.

**Theorem 1.15 (Uniform positivity on compact subsets).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.exists_pos_le_tau_im`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.exists_pos_le_tau_im` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imaginary part of the complementary ratio has a strictly positive lower bound on each compact subset of the double slit.

**Theorem 1.16 (Uniform positivity in the three crossing charts).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.exists_pos_le_tau_im_charts`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.exists_pos_le_tau_im_charts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The continuous images of a compact set of nonreal cross-ratios under 1 − 1/z, z and 1/z have a common strictly positive lower bound for the imaginary part of the corresponding ratio.

## References

- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.doubleSlit`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.exists_pos_le_tau_im`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.exists_pos_le_tau_im_charts`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.pfaff`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.pfaff_mem_slitDomain`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitDomain`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_analyticOnNhd`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_differentiableAt`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_eq_period`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_ne_zero`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_re_pos`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slit_wronskian`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.tau`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.tau_hasDerivAt`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.tau_im_pos`
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialWronskian](OriginalHalfBinomialWronskian.md)
