# Cumulative and short-window zeta zero counts

## Abstract

The dyadic logarithmic error controls cumulative counts and shorter ordinate windows.

Let N(x,y) be the count of nontrivial zeta zeros in the half-open ordinate interval (x,y], with analytic multiplicity. Put c=1/(2 pi) and M(y)=c y (log(y/(2 pi))-1).

**Theorem 1.1 (Logarithmic-square cumulative counting residual).**

$$|\operatorname{N}\left(0, Y\right)-\operatorname{M}\left(Y\right)| \le D \cdot \operatorname{log}\left(Y\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/CumulativeRvmError.cumulative_rvm_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist U>1 and D>=0 such that the displayed inequality holds for every Y>=U. The existing unconditional dyadic Riemann-von Mangoldt estimate has main term exactly M(2x)-M(x). Thus E(x)=N(0,x)-M(x) has increment |E(2x)-E(x)|<=B log(x) for x sufficiently large. The base band [U,2U] has bounded residual by count monotonicity and elementary logarithm bounds. Enlarge D to dominate that base band and to satisfy 2D log(2)>=B. Since D(log(2x)^2-log(x)^2)>=B log(x), induction along dyadic multiples of the base band gives the result for arbitrary real Y>=U.

**Theorem 1.2 (Lower counts in windows of logarithmic width).**

$$\frac{{y-x} \cdot \operatorname{log}\left(x\right)}{8 \cdot \pi} \le \operatorname{N}\left(x, y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/CumulativeRvmError.short_window_count_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist L>1 and K>0 such that for all real x,y with L<=x, x+K log(x)<=y and y<=2x, the displayed bound holds. For large enough x, monotonicity of the logarithm gives M(y)-M(x)>=c (y-x) log(x)/2. Since y<=2x, the two cumulative errors cost at most 5D log(x)^2. Choosing K>=20D/c makes that cost at most c (y-x) log(x)/4. Count additivity yields the result.

The classical cumulative Riemann-von Mangoldt formula has a stronger O(log Y) residual. Here the O(log Y)^2 bound follows directly from the existing exact dyadic supplier, without assuming the stronger cumulative estimate or RH. The short-window result gives a lower mass input for phase deficit estimates on moving ordinate bands. Uniform high-order Fourier moments require additional phase estimates.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/CumulativeRvmError.cumulative_rvm_error`
- Truth anchor: `D5/S3/Weil/ZeroData/CumulativeRvmError.short_window_count_lower`
- Dependency: [D5/S3/Weil/ZeroData/CumulativeRiemannVonMangoldt](CumulativeRiemannVonMangoldt.md)
