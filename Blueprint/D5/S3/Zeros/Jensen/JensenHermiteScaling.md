# Hermite local scaling

## Abstract

Entire weighted coefficient series control every complex segment at an exact finite order.

Write D(k,F,z)=iteratedDeriv k F z, and b(j)=loweredCoefficients(a,j). The derivative, transformed-series, Taylor and scaling results assume HasSum(j -> a(j)*z^j,F(z)) for every complex z and summability of norm(a(j))*j^L*R^j for every natural L and every real R>=0. The transformed-weight result needs only the latter summability assumption. The Hermite coefficient identity and geometric threshold need neither assumption.

**Theorem 1.1 (Actual derivative bound).**

$$\lvert \operatorname{D}\left(b, F, z\right)\rvert \le \operatorname{weightedNorm}\left(a, b, R\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/JensenHermiteScaling.entire_derivative_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume HasSum(j -> a(j) z^j, F(z)) at every complex z, and summability of norm(a(j))*j^L*R^j for every natural L and nonnegative real R. For R>=1 and norm(z)<=R, the actual b-th derivative has norm at most weightedNorm(a,b,R). Complex differentiation of uniformly summable monomial series establishes the derivative identity.

**Theorem 1.2 (The transformed entire series).**

$$\operatorname{HasSum}\left(j\mapsto \operatorname{b}\left(j\right)z^{j}, -4z\operatorname{D}\left(2, F, z\right)-2\operatorname{D}\left(1, F, z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/JensenHermiteScaling.lowered_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For b(j)=-(2j+2)(2j+1)a(j+1), the transformed function is -4z F''(z)-2F'(z). Both derivative series are shifted by one index after treating the vanished coefficient. The identity includes z=0 without division by z.

**Theorem 1.3 (All transformed weighted sums).**

$$\operatorname{Summable}\left(j\mapsto \lvert \operatorname{b}\left(j\right)\rvert j^{L}R^{j}\right)\land \operatorname{weightedNorm}\left(b, L, R\right)\le 4\operatorname{weightedNorm}\left(a, L+2, \operatorname{max}\left(1, R\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/JensenHermiteScaling.lowered_weighted_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural L and nonnegative R, the majorant is 4*norm(a(j+1))*(j+1)^(L+2)*max(1,R)^(j+1). The omitted zero-index term of the original weighted sum is zero. This proves both summability and the displayed norm bound, including R=0 and L=0.

**Theorem 1.4 (The probabilists' normalization).**

$$\operatorname{He}\left(v, u\right)=\sum_{0\le r\le \frac{v}{2}}\frac{(-1)^{r}v!}{2^{r}r!(v-2r)!}u^{v-2r}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/JensenHermiteScaling.hermite_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2026). *DLMF Section 18.2, General Orthogonal Polynomials*. URL: <https://dlmf.nist.gov/18.2>.

*Commentary.*

The integer Hermite coefficient formula, the binomial factorial identity and the even double-factorial identity give this coefficient normalization. The equivalent expression uses correctionCoeff(r,2r)=1/(2^r*r!). Both parities and v=0 are included.

**Theorem 1.5 (An explicit geometric threshold).**

$$\begin{aligned}T=\operatorname{max}\left(1, \operatorname{max}\left(2q, \frac{tzeroq}{sigma}\right)\right)\\N=\operatorname{max}\left(1, \operatorname{NatCeil}\left(T^{2}\right)\right)\\\forall n\ge N, 1\le n\land 1\le \operatorname{sqrt}\left(n\right)\land \frac{q}{\operatorname{sqrt}\left(n\right)}\le \frac{1}{2}\land \frac{tzeroq}{\operatorname{sqrt}\left(n\right)}\le sigma\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/JensenHermiteScaling.hermite_scaling_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real t0>0, sigma>0 and q>=2, NatCeil is the natural ceiling. This threshold simultaneously gives n>=1, sqrt(n)>=1, q/sqrt(n)<=1/2 and t0*q/sqrt(n)<=sigma for every later natural n. It requires no coefficient, analyticity or zero-order hypothesis.

**Theorem 1.6 (Every complex segment).**

$$\lvert \operatorname{D}\left(k, F, c+y\right)-\frac{\operatorname{D}\left(v, F, c\right)y^{v-k}}{(v-k)!}\rvert \le \frac{B\lvert y\rvert ^{v-k+1}}{(v-k)!}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/JensenHermiteScaling.exact_order_taylor_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here c>0, sigma>0, k<=v, norm(y)<=sigma, F has exact order v at c, and B=weightedNorm(a,v+1,max(1,c+sigma)). The real parameter t traverses c+t*y for 0<=t<=1. Its m-th derivative is y^m D^(k+m)F(c+t*y), by complex differentiation and restriction to real scalars. The vector-valued Taylor bound leaves only the degree v-k term. The denominator (v-k)! is sufficient, including k=v and v=0. No cancellation by y occurs.

**Theorem 1.7 (Every order on the full complex disk).**

$$\operatorname{IsExactRealOrder}\left(F, tzero, v\right)\implies \operatorname{ScaledFunctionEstimate}\left(F, a, tzero, sigma, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/JensenHermiteScaling.hermite_scaled_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the actual entire HasSum and all weighted summability hypotheses above, with t0>0 and sigma>0. For each real q>=2, set T=max(1,max(2q,t0*q/sigma)) and N=max(1,ceil(T^2)). An explicit positive finite C bounds the original normalized error by C/sqrt(n) for every natural n>=N and every complex u with norm(u)<=q. The normalization is t0^v*D^vF(t0)/v!, divided by sqrt(n)^v, and is nonzero by exact order.

Set K=v/2. For each finite correction pair r<=K,k<=2r, the normalized leading term has denominator sqrt(n)^(2r-k); only k=2r contributes to the Hermite polynomial. The Taylor error has denominator sqrt(n)^(2r-k+1). The coefficient remainder has denominator sqrt(n)^(2K+2-v), whose exponent is one or two. Positive coefficient norms bound the finite sum, and a positive unit is added to its constant.

The complex disk includes its boundary, u=0 and moving zeros. The transformed branch uses its own coefficient sequence and its own nonzero exact-order derivative. The function estimate supplies no root enumeration, original boundary zero exclusion, compact-window exhaustion or RH conclusion.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/JensenHermiteScaling.entire_derivative_bound`
- Truth anchor: `D5/S3/Zeros/Jensen/JensenHermiteScaling.exact_order_taylor_bound`
- Truth anchor: `D5/S3/Zeros/Jensen/JensenHermiteScaling.hermite_normalization`
- Truth anchor: `D5/S3/Zeros/Jensen/JensenHermiteScaling.hermite_scaled_estimate`
- Truth anchor: `D5/S3/Zeros/Jensen/JensenHermiteScaling.hermite_scaling_threshold`
- Truth anchor: `D5/S3/Zeros/Jensen/JensenHermiteScaling.lowered_series`
- Truth anchor: `D5/S3/Zeros/Jensen/JensenHermiteScaling.lowered_weighted_data`
- Dependency: [D5/S3/Zeros/Jensen/JensenAnalyticCoefficientRemainder](JensenAnalyticCoefficientRemainder.md)
