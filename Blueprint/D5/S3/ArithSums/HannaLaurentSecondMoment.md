# A391810: the signed Laurent second moment

## Abstract

The full signed second moment of Hanna's bilateral Laurent rows.

For every natural n>=2, formula (4) concerns T(n,k), the coefficient at zero of x^k times the full bilateral Laurent sum over all integers j of x^j*(1-x^j)^(n+j), expanded at zero. Equivalently T(n,k) is the coefficient at -k of that sum. Integer exponents use Laurent-field inverses. The inherited series is the formally summable Hahn sum, with every outer integer index retained. No value of the bilateral series at one is used.

Put y=x^(-1). The exact coefficient identity HannaLaurentRowSums.series_coefficient identifies T(n,k) with the integer coefficient of P_n(y)=-1+sum_{q=1..n} y^q*(1-y^q)^(n-q). The constant -1 comes from outer index -(n+1); the remaining nonpositive coefficients come from indices -1 through -n. The inherited row_degree bound is natDegree(P_n)<=floor((n+1)/2)^2. Thus the published inclusive endpoint contains the full coefficient support.

For the Euler operator E=y*d/dy, the coefficient of y^k in E^2(P) is k^2 times the coefficient of y^k in P. E^2 does not increase degree. Evaluating this finite polynomial at y=1 therefore gives the full weighted coefficient sum, including k=0 and the upper endpoint.

For the term y^q*(1-y^q)^m, E^2 evaluated at one is q^2 when m=0, -3*q^2 when m=1, 2*q^2 when m=2, and zero when m>=3. For n>=3 only q=n,n-1,n-2 remain. Their sum is n^2-3*(n-1)^2+2*(n-2)^2=-(2*n-5). For n=2 the two available terms give 4-3=1, the same signed expression. The constant -1 is annihilated by E^2. Integer subtraction precedes negation and the cast to rationals.

**Theorem 1.1 (The complete formula (4)).**

$$\forall n \in \mathbb{N},\; 2 \le n \Rightarrow \sum_{k = 0}^{\left\lfloor\frac{n + 1}{2}\right\rfloor^{2}} k^{2} \cdot \operatorname{coeff}\left(\operatorname{series}\left(n\right), -(k)\right) = -(2 \cdot \operatorname{toInt}\left(n\right) - 5)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/HannaLaurentSecondMoment.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a391810-second-moment` (proved) by `D5/S3/ArithSums/HannaLaurentSecondMoment.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a391810-second-moment","declaration_gid":"D5/S3/ArithSums/HannaLaurentSecondMoment.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A391810, nonpositive Laurent coefficients and zero row sums*. URL: <https://oeis.org/A391810/internal>.

*Commentary.*

The theorem holds for every natural n>=2. The coefficient is rational, with the signed integer right side cast to the rationals. Natural division by two is performed before squaring the inclusive bound. The coefficient bridge transports the finite polynomial identity to the original series. This settles the second moment in the stated expansion convention; it asserts no other moment formula or analytic convergence at one.

## References

- Truth anchor: `D5/S3/ArithSums/HannaLaurentSecondMoment.result`
- Dependency: [D5/S3/ArithSums/HannaLaurentRowSums](HannaLaurentRowSums.md)
