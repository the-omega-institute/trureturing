# Regularity after subtracting paired poles

## Abstract

Removing finitely many paired spectral poles gives a holomorphic regular part with polynomial boundary control.

**Theorem 1.1 (Paired pole comparison).**

Lean statement: `D5/S3/Analytic/Laplace/PairedPoleRegularity.pole_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/PairedPoleRegularity.pole_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the complex argument has norm at most three quarters of the ordinate, pairing the two opposite poles bounds its term by 32 times the norm times multiplicity divided by ordinate squared.

**Theorem 1.2 (Differentiability away from the two poles).**

Lean statement: `D5/S3/Analytic/Laplace/PairedPoleRegularity.poleTerm_differentiableAt`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/PairedPoleRegularity.poleTerm_differentiableAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A paired pole term is complex differentiable at any point where both denominators are nonzero.

**Theorem 1.3 (Splitting the paired series).**

Lean statement: `D5/S3/Analytic/Laplace/PairedPoleRegularity.pole_sum_split`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/PairedPoleRegularity.pole_sum_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The summable paired series equals its finite cutoff sum plus the complementary tail, with totalized reciprocals at poles.

**Definition 1.4 (Reindexing the complementary spectral tail).**

Lean statement: `D5/S3/Analytic/Laplace/PairedPoleRegularity.cutoff_complement`

*Formalization.* `D5/S3/Analytic/Laplace/PairedPoleRegularity.cutoff_complement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The indices outside the finite spectral cutoff at T are in bijection with the indices whose ordinates are strictly greater than T.

**Theorem 1.5 (Absolute summability of paired poles).**

Lean statement: `D5/S3/Analytic/Laplace/PairedPoleRegularity.poles_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/PairedPoleRegularity.poles_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive spectrum with logarithmic counting asymptotics, away from the poles the paired series is summable. At a pole the Lean expression uses the convention 1/0 = 0.

**Theorem 1.6 (Holomorphic regular part).**

Lean statement: `D5/S3/Analytic/Laplace/PairedPoleRegularity.regularPart_differentiableOn`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/PairedPoleRegularity.regularPart_differentiableOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a locally finite positive spectrum, with positive integral multiplicities, have counting function asymptotic to T log(T)/(2 pi). Suppose a Laplace transform has the prescribed paired pole expansion with holomorphic remainder J on the strip from -eta to 1, where 0<eta<1/5. For M>=1, subtract all poles whose positive ordinate is at most 2M. The resulting regular part is holomorphic on abs(Re(s))<eta and abs(Im(s))<M+1. Pairing opposite poles supplies an inverse-square summable majorant for large cutoffs. For cutoffs between one and four, a finite pole correction to cutoff four remains holomorphic on this rectangle.

**Theorem 1.7 (Exact finite pole decomposition).**

Lean statement: `D5/S3/Analytic/Laplace/PairedPoleRegularity.laplace_eq_finite_poles_add_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/PairedPoleRegularity.laplace_eq_finite_poles_add_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same counting and paired Laplace assumptions, for every M>=1 and every s with 1/2<Re(s)<1, the Laplace transform equals minus one half of the finite sum of paired pole terms with ordinate at most 2M, plus the regular part. Absolute summability of the paired series justifies splitting the full series into the finite cutoff and its complementary tail.

**Theorem 1.8 (Polynomial control of boundary values and derivatives).**

Lean statement: `D5/S3/Analytic/Laplace/PairedPoleRegularity.regularized_boundary_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/PairedPoleRegularity.regularized_boundary_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume additionally that J has polynomial growth of degree k on abs(Re(s))<=eta/2. There is a positive constant A, independent of M and t, such that for M>=1 and abs(t)<=M the sum of the norms of the regular part and its complex derivative at i*t is at most A*M^(max(k,1)). The inverse-square tail estimate bounds the paired tail by a constant times M in a fixed neighborhood of the segment. Cauchy's estimate on circles of radius eta/4 then controls the derivative with the same degree. For cutoffs below four, the finite correction is bounded using the spectral mass at eight.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/PairedPoleRegularity.cutoff_complement`
- Truth anchor: `D5/S3/Analytic/Laplace/PairedPoleRegularity.laplace_eq_finite_poles_add_regular`
- Truth anchor: `D5/S3/Analytic/Laplace/PairedPoleRegularity.poleTerm_differentiableAt`
- Truth anchor: `D5/S3/Analytic/Laplace/PairedPoleRegularity.pole_bound`
- Truth anchor: `D5/S3/Analytic/Laplace/PairedPoleRegularity.pole_sum_split`
- Truth anchor: `D5/S3/Analytic/Laplace/PairedPoleRegularity.poles_summable`
- Truth anchor: `D5/S3/Analytic/Laplace/PairedPoleRegularity.regularPart_differentiableOn`
- Truth anchor: `D5/S3/Analytic/Laplace/PairedPoleRegularity.regularized_boundary_bound`
- Dependency: [D5/S3/Analytic/Oscillation/OrdinateCounting](../Oscillation/OrdinateCounting.md)
