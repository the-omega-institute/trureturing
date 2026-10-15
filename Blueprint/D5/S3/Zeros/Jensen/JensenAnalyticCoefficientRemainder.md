# Analytic coefficient remainder

## Abstract

An entire complex coefficient series determines the derivatives of its finite Jensen correction remainder.

**Definition 1.1 (Finite correction operator).**

$$\forall r\in \mathbb{N}, \forall F:\mathbb{C}\to \mathbb{C}, \forall z\in \mathbb{C}, \operatorname{correctionOperator}\left(r, F, z\right)=\sum_{0\le k\le 2r} \operatorname{c}\left(r, k\right)z^{k}\operatorname{D}\left(k, F, z\right)$$

*Formalization.* `D5/S3/Zeros/Jensen/JensenAnalyticCoefficientRemainder.correctionOperator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

c(r,k) is correctionCoeff and D(k,F,z) is iteratedDeriv k F z. The sum includes both endpoints 0 and 2r. The finite identity e(r,j)=sum(k<=2r)c(r,k)*descFactorial(j,k) identifies its entire series as sum_j e(r,j)*a(j)*z^j.

**Definition 1.2 (Weighted coefficient norm).**

$$\forall a:\mathbb{N}\to \mathbb{C}, \forall L\in \mathbb{N}, \forall R\in \mathbb{R}, \operatorname{weightedNorm}\left(a, L, R\right)=\sum_{j\in \mathbb{N}} \lvert \operatorname{a}\left(j\right)\rvert j^{L}R^{j}$$

*Formalization.* `D5/S3/Zeros/Jensen/JensenAnalyticCoefficientRemainder.weightedNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All coefficients are retained. The analytic theorem requires summability for every natural order and every nonnegative radius. The infinite sum is weightedNorm, with no tail cutoff.

**Definition 1.3 (Natural falling-factorial polynomial).**

$$\forall a:\mathbb{N}\to \mathbb{C}, \forall n\in \mathbb{N}, \operatorname{coefficientPolynomial}\left(a, n\right)=\sum_{0\le j\le n} \operatorname{C}\left(\frac{\operatorname{descFactorial}\left(n, j\right)}{n^{j}}\operatorname{a}\left(j\right)\right)X^{j}$$

*Formalization.* `D5/S3/Zeros/Jensen/JensenAnalyticCoefficientRemainder.coefficientPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C embeds a complex coefficient in the polynomial ring and X is its indeterminate. p(a,n,z) denotes evaluation of this polynomial at z. The natural falling factorial vanishes for j>n, so the finite polynomial also has the full infinite coefficient-series representation.

**Theorem 1.4 (Every derivative order of the actual remainder).**

$$\begin{aligned}\forall a:\mathbb{N}\to \mathbb{C}, \forall F:\mathbb{C}\to \mathbb{C},\\(\forall z\in \mathbb{C}, \operatorname{HasSum}\left(j\mapsto \operatorname{a}\left(j\right)z^{j}, \operatorname{F}\left(z\right)\right)) \land\\(\forall L\in \mathbb{N}, \forall R\in \mathbb{R}, 0\le R\implies \operatorname{Summable}\left(j\mapsto \lvert \operatorname{a}\left(j\right)\rvert j^{L}R^{j}\right))\implies\\\forall n,K,b\in \mathbb{N}, 1\le n\implies \forall R\in \mathbb{R}, 1\le R\implies \forall z\in \mathbb{C}, \lvert z\rvert \le R\implies\\\lvert \operatorname{D}\left(b, w\mapsto \operatorname{p}\left(a, n, w\right)-\sum_{0\le r\le K} \frac{(-1)^{r}}{n^{r}}\operatorname{correctionOperator}\left(r, F, w\right), z\right)\rvert \le \frac{2}{n^{K+1}}\operatorname{weightedNorm}\left(a, 2K+2+b, R\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/JensenAnalyticCoefficientRemainder.analytic_coefficient_operator_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every order b the coefficient derivative series has terms a(j)*descFactorial(j,b)*z^(j-b). On an open disk of radius R+1, descFactorial(j,b)<=j^b and the radius-power bound give a summable uniform majorant. Mathlib's complex differentiation theorem justifies each induction step; the derivative identity is proved rather than assumed.

Multiplying the k-th derivative series by c(r,k)*z^k and summing the finite k range gives the correction operator series. Terms j<k vanish exactly. Subtracting the finite correction sum from the polynomial gives the actual error series rho(n,K,j)*a(j)*z^j, where rho is the complete finite bonferroniResidual.

The finite residual estimate gives weighted summability for these error coefficients at every radius. Applying the all-order derivative series to this actual error and then the weighted residual bound proves the stated inequality. The theorem includes n=1, j=0, K=0, b=0, j<b and j>n.

The actual theta-source consumer supplies its entire series and weighted summability, and identifies sourcePolynomial with coefficientPolynomial sourceA n. This estimate does not establish the local scaled Hermite estimates, node enumeration, the original boundary comparison, compact-window exhaustion, or RH.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/JensenAnalyticCoefficientRemainder.analytic_coefficient_operator_error`
- Truth anchor: `D5/S3/Zeros/Jensen/JensenAnalyticCoefficientRemainder.coefficientPolynomial`
- Truth anchor: `D5/S3/Zeros/Jensen/JensenAnalyticCoefficientRemainder.correctionOperator`
- Truth anchor: `D5/S3/Zeros/Jensen/JensenAnalyticCoefficientRemainder.weightedNorm`
- Dependency: [D5/S3/Zeros/Jensen/JensenFiniteCoefficientRemainder](JensenFiniteCoefficientRemainder.md)
