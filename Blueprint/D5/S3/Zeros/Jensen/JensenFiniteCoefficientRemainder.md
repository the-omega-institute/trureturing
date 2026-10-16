# Finite Jensen coefficients and remainder

## Abstract

Finite coefficients and an ordered product remainder serve the complete actual-source fixed-window consumer.

**Definition 1.1 (Natural falling factorial).**

$$\forall j,k\in \mathbb{N}, \operatorname{fallingReal}\left(j, k\right)=\operatorname{descFactorial}\left(j, k\right)$$

*Formalization.* `D5/S3/Zeros/Jensen/JensenFiniteCoefficientRemainder.fallingReal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural falling factorial is coerced to Real. It is one at k=0 and exactly zero when k>j.

**Definition 1.2 (Finite subset coefficients).**

$$\forall r,j\in \mathbb{N}, \operatorname{e}\left(r, j\right)=\sum_{S\subseteq \operatorname{range}\left(j\right),\operatorname{card}\left(S\right)=r} \prod_{i\in S} i$$

*Formalization.* `D5/S3/Zeros/Jensen/JensenFiniteCoefficientRemainder.elementarySymmetric` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

e(r,j) denotes elementarySymmetric r j. All finite subsets are retained, including those whose product contains zero; e(0,j)=1. Splitting by the new index proves e(r+1,j+1)=e(r+1,j)+j*e(r,j). The equivalent nonnegative product estimate follows by simultaneous induction from this split and Mathlib pow_add_mul_le_add_pow: r!*e(r,j)<=S(j)^r with S(j)=sum(i<j)i<=j^2/2. Thus e(r,j)<=j^(2r)/(2^r*r!), for every r,j.

**Definition 1.3 (Finite correction recurrence).**

$$\begin{aligned}\operatorname{c}\left(0, 0\right)=1, \forall k\in \mathbb{N}, \operatorname{c}\left(0, k+1\right)=0\\\forall r\in \mathbb{N}, \operatorname{c}\left(r+1, 0\right)=0, \operatorname{c}\left(r+1, 1\right)=0\\\forall r,k\in \mathbb{N}, \operatorname{c}\left(r+1, k+2\right)=\frac{(k+1)\operatorname{c}\left(r, k+1\right)+\operatorname{c}\left(r, k\right)}{k+2}\end{aligned}$$

*Formalization.* `D5/S3/Zeros/Jensen/JensenFiniteCoefficientRemainder.correctionCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

c denotes correctionCoeff. Its nonnegative support is (r,k)=(0,0), or r+1<=k<=2r. The above-support coefficient is zero, so the top recurrence gives c(r,2r)=1/(2^r*r!). No permutation-cardinality assertion is used.

**Definition 1.4 (Falling-factorial construction).**

$$\forall r,j\in \mathbb{N}, \operatorname{correctionSum}\left(r, j\right)=\sum_{0\le k\le 2r} \operatorname{c}\left(r, k\right)\operatorname{fallingReal}\left(j, k\right)$$

*Formalization.* `D5/S3/Zeros/Jensen/JensenFiniteCoefficientRemainder.correctionSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The endpoint-zero index shift proves correctionSum(r+1,j+1)-correctionSum(r+1,j)=j*correctionSum(r,j). Simultaneous induction on j for all r identifies correctionSum(r,j)=e(r,j), including r=0 and orders above the subset degree. This identity converts the finite subset coefficients into the derivative correction operators used in the analytic remainder and Hermite scaling estimates.

**Definition 1.5 (Exact finite remainder).**

$$\forall n,K,j\in \mathbb{N}, \operatorname{rho}\left(n, K, j\right)=\frac{\operatorname{descFactorial}\left(n, j\right)}{n^{j}}-\sum_{0\le r\le K} \frac{(-1)^{r}\operatorname{e}\left(r, j\right)}{n^{r}}$$

*Formalization.* `D5/S3/Zeros/Jensen/JensenFiniteCoefficientRemainder.bonferroniResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rho is bonferroniResidual, with the original quotient and all K+1 truncation coefficients. For n>=1, Pochhammer evaluation identifies the quotient with the complete product of (1-i/n) for i<j.

Define the private ordered remainder T(0,j)=product(i<j)(1-i/n) and T(k+1,j)=sum(i<j)(i/n)*T(k,i). Every recursive selection decreases the next index and retains the full product below the smallest selected index. Iterating Mathlib prod_one_sub_ordered proves T(k,j)=e(k,j)/n^k-T(k+1,j), and the exact signed residual is (-1)^(K+1)*T(K+1,j). For j<=n all retained factors lie in [0,1], giving 0<=T(k,j)<=e(k,j)/n^k.

For j>n the natural falling factorial is exactly zero. With x=j^2/n>=1, the absolute truncation is bounded by sum(r<=K)x^r/(2^r*r!)<=x^(K+1)*sum(r<=K)2^(-r)<=2*x^(K+1). The two cases prove |rho(n,K,j)|<=2*j^(2K+2)/n^(K+1) for every n>=1 and every natural K,j, retaining j=0, K=0 and zero factors.

For a:Nat->Complex, n>=1, b,K natural and R>=1, the differentiated coefficient majorant is sum_j norm(a(j))*|rho(n,K,j)|*descFactorial(j,b)*R^(j-b)<=2/n^(K+1)*sum_j norm(a(j))*j^(2K+2+b)*R^j. Its sole summability premise is that the series on the right is summable. Terms j<b vanish exactly, while descFactorial(j,b)<=j^b and R^(j-b)<=R^j provide the pointwise domination and summability of the left series.

The ordered product identity is the finite Bonferroni expansion, with its remainder retained. The analytic remainder estimate uses this finite bound; Hermite scaling and the actual-source fixed-window theorem then supply the local nodes and compact-window conclusion. This finite calculation alone has no RH conclusion.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/JensenFiniteCoefficientRemainder.bonferroniResidual`
- Truth anchor: `D5/S3/Zeros/Jensen/JensenFiniteCoefficientRemainder.correctionCoeff`
- Truth anchor: `D5/S3/Zeros/Jensen/JensenFiniteCoefficientRemainder.correctionSum`
- Truth anchor: `D5/S3/Zeros/Jensen/JensenFiniteCoefficientRemainder.elementarySymmetric`
- Truth anchor: `D5/S3/Zeros/Jensen/JensenFiniteCoefficientRemainder.fallingReal`
