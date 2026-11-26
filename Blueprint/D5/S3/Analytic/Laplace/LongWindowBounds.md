# Numerical bounds behind long-window pole exclusion

## Abstract

Numerical Landau comparison for arbitrarily late windows

**Remark 1.1 (The source numerical growth comparison).**

Lean statement: `D5/S3/Analytic/Laplace/LongWindowBounds.landau_growth_contra`

*Formalization.* `D5/S3/Analytic/Laplace/LongWindowBounds.landau_growth_contra` (`✓ std3`).

*Citation.* Levent Alpöge (2026). *Riemann hypothesis formalization in Lean*. URL: <https://github.com/the-omega-institute/riemann-hypothesis>.

*Commentary.*

Alpöge's Deduction.landau_growth_contra proves the existence of eta and U0 by the numerical argument used here. Its proof chooses eta=log(e/d)/2 and U0=2|C|/(c log(e/d)). This original argument is literature-attested.

**Remark 1.2 (The source numerical window contradiction).**

Lean statement: `D5/S3/Analytic/Laplace/LongWindowBounds.landau_window_contra`

*Formalization.* `D5/S3/Analytic/Laplace/LongWindowBounds.landau_window_contra` (`✓ std3`).

*Citation.* Levent Alpöge (2026). *Riemann hypothesis formalization in Lean*. URL: <https://github.com/the-omega-institute/riemann-hypothesis>.

*Commentary.*

Alpöge's Deduction.landau_window_contra gives the numerical contradiction for zero less than d less than e at most E. That original statement and argument are literature-attested. The local extension below removes the ordering between e and E.

The abstract power-window condition consists only of a positive width delta and arbitrarily late positive starting points Y whose entire interval [Y,Y^(1+delta)] obeys the stated upper bound. Restrictions on the exponent are supplied separately by a theorem that needs them.

**Theorem 1.3 (Uniform comparison of the two geometric rates).**

Lean statement: `D5/S3/Analytic/Laplace/LongWindowBounds.landau_growth_contra`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/LongWindowBounds.landau_growth_contra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Levent Alpöge (2026). *Riemann hypothesis formalization in Lean*. URL: <https://github.com/the-omega-institute/riemann-hypothesis>.

*Commentary.*

Let c,d,e be real numbers with c positive and zero less than d less than e, and let C be any real number. Set eta=log(e/d)/2 and U0=2|C|/(c log(e/d)). Eta is positive and U0 is nonnegative. For every U at least U0 and every natural k at least U, C exp(eta U)/e^k is strictly less than c/d^k. The explicit constants and nonnegative cutoff are the repo-derived strengthening of the cited source statement.

**Theorem 1.4 (The coefficient comparison cannot recur arbitrarily late).**

Lean statement: `D5/S3/Analytic/Laplace/LongWindowBounds.landau_window_contra`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/LongWindowBounds.landau_window_contra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Levent Alpöge (2026). *Riemann hypothesis formalization in Lean*. URL: <https://github.com/the-omega-institute/riemann-hypothesis>.

*Commentary.*

Let c,d,e,E be real numbers with c positive and zero less than d less than e, and d less than E, and let B,K be any real numbers. It is impossible that for every eta positive and every cutoff U0 there exist U at least U0 and a natural k at least U such that c/d^k is at most B/e^k plus K exp(eta U)/E^k. No ordering between e and E is required. This repo-derived extension uses their minimum. Both upper contributions are controlled by the uniform geometric comparison, with their absolute coefficients.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/LongWindowBounds.landau_growth_contra`
- Truth anchor: `D5/S3/Analytic/Laplace/LongWindowBounds.landau_growth_contra`
- Truth anchor: `D5/S3/Analytic/Laplace/LongWindowBounds.landau_window_contra`
- Truth anchor: `D5/S3/Analytic/Laplace/LongWindowBounds.landau_window_contra`
