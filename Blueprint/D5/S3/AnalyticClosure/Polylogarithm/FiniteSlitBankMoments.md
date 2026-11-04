# FiniteSlitBankMoments

## Abstract

A strictly signed continuous bank on a finite interval dominates a faster geometric error.

**Theorem 1.1 (A fixed positive bank mass dominates the outer scale).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitBankMoments.bank_dominance`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitBankMoments.bank_dominance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

Let R>1 and let h be continuous and nonnegative on [1,R], with h(x)>0 for 1<x<R. For every real B, eventually in n, B/R^n is strictly less than (1/pi) times the integral from 1 to R of h(x)/x^(n+1). The threshold may depend on h, R and B; B need not be positive.

Choose a=(2+R)/3 and b=(1+2R)/3. The compact interval [a,b] lies inside (1,R), so h has a strictly positive minimum there. Integral monotonicity gives a constant c>0 with c/b^n below the full bank moment for every n. Since b<R, B*(b/R)^n tends to zero and eventually lies below c/pi. This fixed interior mass supplies the strict comparison even when h vanishes at the endpoint one.

This is the real integral estimate used after a finite slit contour has been deformed. The estimate itself neither assumes nor proves the Cauchy contour identity, its orientation, its connector limits, or an outer-circle bound. It therefore asserts no Taylor coefficient sign. No coefficient asymptotic equivalent or effective threshold is asserted.

## References

- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitBankMoments.bank_dominance`
- Dependency: [D5/S3/AnalyticClosure/Polylogarithm/CompositionZeroFreeCollar](CompositionZeroFreeCollar.md)
