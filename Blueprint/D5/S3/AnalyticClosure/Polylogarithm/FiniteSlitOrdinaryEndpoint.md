# FiniteSlitOrdinaryEndpoint

## Abstract

The ordinary inverse coefficients are absolutely summable, with the actual branch endpoint as their total.

**Theorem 1.1 (Absolute summability with the signed finite prefix).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinaryEndpoint.result`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinaryEndpoint.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

For every positive head, every positive-entry tail and positive ell, the original ordinary inverse coefficients are absolutely summable and have HasSum equal to endpoint. This endpoint is zeta(head,tail) to power minus ell for admissible head>1, and zero for head=1. The actual CompositionBanks endpoint theorem supplies both cases on the same source branch; the removable origin is preserved by FiniteSlitCompositionMoments.reciprocal.

Choose N beyond the negative coefficient threshold. The shifted coefficients q(n)=-a(n+N) are nonnegative. For every finite window, their radially weighted partial sum is bounded by the full polynomial prefix minus the actual reciprocal. Passing to the radial endpoint gives a single finite bound for every unweighted partial sum. This proves summability of the shifted tail; adjoining the signed finite prefix gives absolute summability of the original sequence. Abel's theorem then identifies its total with the actual endpoint.

Every sufficiently late partial sum through n strictly exceeds endpoint, because its omitted summable tail contains strictly negative coefficients. The proof retains all early coefficients. This supplies the exact first-partial-sum consequence; the remaining formal smoothing interfaces, positive radial lower bound for second sums, all fixed j and the strict admissible binomial excess are not claimed here. The full original Xu--Zhao problem remains open.

## References

- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinaryEndpoint.result`
- Dependency: [D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinaryCoefficients](FiniteSlitOrdinaryCoefficients.md)
- Dependency: [D5/S3/AnalyticClosure/PositiveSeriesTail](../PositiveSeriesTail.md)
