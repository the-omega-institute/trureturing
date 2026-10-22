# Series and signed derivatives

## Abstract

Exponential moments and their quotient coefficients.

**Theorem 1.1 (Signed derivative composition).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.iteratedDeriv_F`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.iteratedDeriv_F` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural i and k and every real t, the k-th derivative of F(i) is (-1)^k F(i+k). The differentiation operation is iterated on globally defined functions.

**Theorem 1.2 (Equality at positive orders).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.G_eq_F`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.G_eq_F` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For i at least one and t positive, G(i,t)=F(i,t). The reciprocal identity holds on a neighborhood of t, so its derivatives agree there.

**Theorem 1.3 (The exponential moment expansion).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.F_eq_tsum`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.F_eq_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive t, F(i,t) is the sum over natural n of (n+1)^i exp(-(n+1)t). Polynomially weighted geometric convergence supplies locally uniform derivative bounds.

**Theorem 1.4 (Strictly positive moments).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.F_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.F_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every F(i,t) is strictly positive when t is positive. Each term in its convergent exponential expansion is positive.

**Theorem 1.5 (Equality of positive-index ratios).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.ratioG_eq_ratioF`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.ratioG_eq_ratioF` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For i at least one and t positive, the ratios of the two derivative families agree.

**Definition 1.6 (The quotient coefficient recurrence).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.quotCoeff`

*Formalization.* `D5/S3/Analytic/ExpRatioCM/Series.quotCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zeroth coefficient is one. At positive n the coefficient is (n+1)^(i+1) minus the sum over j from zero to n-1 of (j+2)^i times the coefficient at n-1-j.

**Theorem 1.7 (The second quotient coefficient).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.quotCoeff_two`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.quotCoeff_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural i, the coefficient at index two equals 2 times 3^i minus 4^i.

**Theorem 1.8 (A geometric coefficient bound).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.abs_quotCoeff_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.abs_quotCoeff_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For B=2^(i+2), the absolute value of the n-th quotient coefficient is at most B^n. A weighted geometric convolution bounds the recursive contribution by B^n/3 and the numerator contribution by B^n/2.

**Theorem 1.9 (The quotient expansion).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Series.ratioF_eq_tsum`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Series.ratioF_eq_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t greater than log(2^(i+2)), the first ratio equals the sum of b(n) exp(-nt). The absolutely convergent Cauchy product reduces this identity to the coefficient recurrence, and the denominator is positive.

**Theorem 1.10 (Signed derivatives of the quotient expansion).**

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
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.iteratedDeriv_F`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.iteratedDeriv_ratioF`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.quotCoeff`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.quotCoeff_two`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.ratioF_eq_tsum`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Series.ratioG_eq_ratioF`
- Dependency: [D5/S3/Analytic/ExpRatioCM/Defs](Defs.md)
