# FiniteSlitOrdinarySmoothing

## Abstract

Signed prefixes and exact binomial smoothing

**Theorem 1.1 (Signed prefixes and exact binomial smoothing).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinarySmoothing.result`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinarySmoothing.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

The kernel is the unit invOneSubPow, whose inverse is exactly (1-X)^j. For an arbitrary real ordinary series p and endpoint L, smooth(p-C(L),1,n) is the first excess. A strictly positive radial lower bound for its convergent power series, together with eventual positivity of this excess, implies the strict binomial baseline for every fixed positive smoothing order.

If the first excess is summable, Abel's theorem identifies its radial limit with its finite total; the positive margin makes that total positive. Otherwise shift beyond its signed prefix and use divergence of a nonnegative nonsummable tail. Restore the full finite prefix in both cases. The second partial sums then have a positive constant lower bound. Further summations dominate a positive linear function after retaining each signed prefix.

The coefficient identity follows in the ordinary power series ring by multiplication with the geometric series. Subtracting the constant series L subtracts exactly L times choose(n+j-1,n). The theorem requires the quantitative radial margin and the power series realization of the first excess as inputs. These inputs are not inferred from an endpoint limit alone, and this theorem alone does not settle the original full Xu--Zhao event.

## References

- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinarySmoothing.result`
- Dependency: [D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinaryEndpoint](FiniteSlitOrdinaryEndpoint.md)
