# Series and signed derivatives

## Abstract

Exponential moments and their quotient coefficients.

**Definition 1.1 (Weighted exponential series).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.weightedSeries`

*Formalization.* `D5/S3/Analytic/ExpRatioCM/Series.weightedSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weighted series at order k is the sum of b(n)*n^k*exp(-n*t) over all natural n.

**Theorem 1.2 (Absolute convergence of weighted exponential series).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.summable_weighted`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.summable_weighted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If B>0 and abs(b(n))<=B^n for every natural n, then for every natural k and real t>log(B) the norms of b(n)*n^k*exp(-n*t) form a summable series.

**Theorem 1.3 (The derivative of a weighted exponential series).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.hasDerivAt_weighted`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.hasDerivAt_weighted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same exponential coefficient bound, the order-k weighted series has derivative minus the order-(k+1) weighted series at every t>log(B). A summable uniform bound on a smaller half-line justifies differentiating the full series.

**Theorem 1.4 (The reciprocal identity).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.reciprocal_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.reciprocal_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive t, 1/(1-exp(-t)) is 1+1/(exp(t)-1). Both the positive-order equality and the zeroth-order constant shift use this identity.

**Theorem 1.5 (Summability of exponential moments).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.summable_expMoment`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.summable_expMoment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural i and positive t, the sequence (n+1)^i exp(-(n+1)t) is summable. The shifted Mathlib exponential-moment theorem supplies this result.

**Theorem 1.6 (Signed derivative composition).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.iteratedDeriv_F`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.iteratedDeriv_F` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural i and k and every real t, the k-th derivative of F(i) is (-1)^k F(i+k). The differentiation operation is iterated on globally defined functions.

**Theorem 1.7 (Equality at positive orders).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.G_eq_F`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.G_eq_F` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For i at least one and t positive, G(i,t)=F(i,t). The reciprocal identity holds on a neighborhood of t, so its derivatives agree there.

**Theorem 1.8 (The exponential moment expansion).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.F_eq_tsum`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.F_eq_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive t, F(i,t) is the sum over natural n of (n+1)^i exp(-(n+1)t). Polynomially weighted geometric convergence supplies locally uniform derivative bounds.

**Theorem 1.9 (Strictly positive moments).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.F_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.F_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every F(i,t) is strictly positive when t is positive. Each term in its convergent exponential expansion is positive.

**Theorem 1.10 (Equality of positive-index ratios).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.ratioG_eq_ratioF`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.ratioG_eq_ratioF` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For i at least one and t positive, the ratios of the two derivative families agree.

**Definition 1.11 (The quotient coefficient recurrence).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.quotCoeff`

*Formalization.* `D5/S3/Analytic/ExpRatioCM/Series.quotCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zeroth coefficient is one. At positive n the coefficient is (n+1)^(i+1) minus the sum over j from zero to n-1 of (j+2)^i times the coefficient at n-1-j.

**Theorem 1.12 (The second quotient coefficient).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.quotCoeff_two`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.quotCoeff_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural i, the coefficient at index two equals 2 times 3^i minus 4^i.

**Theorem 1.13 (A geometric coefficient bound).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.abs_quotCoeff_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.abs_quotCoeff_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For B=2^(i+2), the absolute value of the n-th quotient coefficient is at most B^n. A weighted geometric convolution bounds the recursive contribution by B^n/3 and the numerator contribution by B^n/2.

**Theorem 1.14 (The quotient expansion).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.ratioF_eq_tsum`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.ratioF_eq_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t greater than log(2^(i+2)), the first ratio equals the sum of b(n) exp(-nt). The absolutely convergent Cauchy product reduces this identity to the coefficient recurrence, and the denominator is positive.

**Theorem 1.15 (Signed derivatives of the quotient expansion).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.iteratedDeriv_ratioF`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.iteratedDeriv_ratioF` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive k and t greater than log(2^(i+2)), the signed k-th derivative of the first ratio equals the sum of b(n) n^k exp(-nt). Exponential coefficient bounds provide a summable local majorant at every derivative order.

## References

- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.F_eq_tsum`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.F_pos`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.G_eq_F`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.abs_quotCoeff_le`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.hasDerivAt_weighted`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.iteratedDeriv_F`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.iteratedDeriv_ratioF`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.quotCoeff`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.quotCoeff_two`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.ratioF_eq_tsum`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.ratioG_eq_ratioF`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.reciprocal_eq`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.summable_expMoment`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.summable_weighted`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.weightedSeries`
- Dependency: [D5/S3/Analytic/ExpRatioCM/Defs](Defs.md)
- Dependency: [D5/S3/Analytic/Fourier/SinhLogIntegral](../Fourier/SinhLogIntegral.md)
