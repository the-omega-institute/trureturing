# From the two-variable transform to the gamma series

## Abstract

The positive transformation and the gamma-series half of Conjecture 5.2.

**Definition 1.1 (Literal gamma-series coefficients).**

$$\forall t \in Real,\; \forall n \in Nat,\; \operatorname{gammaCoeff}\left(t, n\right) = \frac{\operatorname{Real}.\operatorname{Gamma}\left(t + n\right)}{\operatorname{Real}.\operatorname{Gamma}\left(2 \cdot t + n\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(n\right)}$$

*Formalization.* `D5/S3/Analytic/KarpZhangGamma/Series.gammaCoeff` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For real t and natural n, gammaCoeff(t,n) is Real.Gamma(t+n) divided by the product of Real.Gamma(2t+n) and n factorial. The degree-n coefficient of the gamma series is y(n) times gammaCoeff(t,n), as defined before Conjecture 5.2 on page 12 of Karp and Zhang.

**Definition 1.2 (Positive parameter factor).**

$$\forall t \in Real,\; \operatorname{scale}\left(t\right) = \operatorname{Real}.\operatorname{sqrt}\left(\operatorname{Real}.\operatorname{pi}\right) \cdot 2^{1 - 2 \cdot t}$$

*Formalization.* `D5/S3/Analytic/KarpZhangGamma/Series.scale` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For real t, scale(t) is Real.sqrt(Real.pi) times 2 to the real power 1-2t. It is positive for every real t. Its products obey scale(t+alpha)scale(t+beta)=scale(t)scale(t+alpha+beta), and scale(t+1)=scale(t)/4.

**Theorem 1.3 (The finite positive beta transformation).**

$$\forall n \in Nat,\; \forall t \in Real,\; 0 < t \Rightarrow \operatorname{gammaCoeff}\left(t, n\right) = \operatorname{scale}\left(t\right) \cdot \sum _{j \in \operatorname{Finset}.\operatorname{range}\left(\operatorname{Nat}.\operatorname{div}\left(n, 2\right) + 1\right)} (\frac{1}{\operatorname{Nat}.\operatorname{factorial}\left(n - 2 \cdot j\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(j\right) \cdot \operatorname{Real}.\operatorname{Gamma}\left(t + \frac{1}{2} + j\right) \cdot 2^{n - 2 \cdot j} \cdot 16^{j}})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Series.positive_beta_transform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural n and positive real t, gammaCoeff(t,n) equals scale(t) times the sum over j=0,...,floor(n/2) of the reciprocal of (n-2j) factorial times j factorial times Real.Gamma(t+1/2+j) times 2 to the natural power n-2j times 16 to the natural power j. This is positive_beta_transform in finite coefficient form. Strong induction in n is simultaneous in every positive t. Gamma duplication supplies degree zero, Gamma recurrence supplies degree one, and both sides obey the same two-step recurrence involving t+1. There is no convergence hypothesis.

**Definition 1.4 (The positive diagonal substitution).**

$$\forall y \in Nat \to Real,\; \forall a \in Real,\; \forall n \in Nat,\; \operatorname{transformCoeff}\left(y, a, n\right) = \sum _{j \in \operatorname{Finset}.\operatorname{range}\left(\operatorname{Nat}.\operatorname{div}\left(n, 2\right) + 1\right)} (\frac{y\left(n\right)}{\operatorname{Nat}.\operatorname{factorial}\left(n - 2 \cdot j\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(j\right) \cdot \operatorname{Real}.\operatorname{Gamma}\left(a + j\right) \cdot 2^{n - 2 \cdot j} \cdot 16^{j}})$$

*Formalization.* `D5/S3/Analytic/KarpZhangGamma/Series.transformCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For a real sequence y, real a and natural n, transformCoeff(y,a,n) is the sum over j=0,...,floor(n/2) of y(n) divided by (n-2j) factorial times j factorial times Real.Gamma(a+j) times 2 to the natural power n-2j times 16 to the natural power j. It is the degree-n coefficient obtained from H(a;z,w) by substituting z=x/2 and w=x squared/16. The relation r+2j=n ensures that only finitely many bidegrees contribute.

**Theorem 1.5 (Identification with the transformed series).**

$$\forall y \in Nat \to Real,\; \forall t \in Real,\; 0 < t \Rightarrow \left(\forall n \in Nat,\; y\left(n\right) \cdot \operatorname{gammaCoeff}\left(t, n\right) = \operatorname{scale}\left(t\right) \cdot \operatorname{transformCoeff}\left(y, t + \frac{1}{2}, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Series.series_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every real sequence y, positive real t and natural n, y(n)gammaCoeff(t,n)=scale(t)transformCoeff(y,t+1/2,n). This coefficient identity proves the formal series identification with no restriction on growth, signs or log-concavity of y. It follows by multiplying positive_beta_transform by y(n).

**Definition 1.6 (Finite Cauchy coefficient of the gamma Turanian).**

$$\forall y \in Nat \to Real,\; \forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall n \in Nat,\; \operatorname{gammaDelta}\left(y, mu, alpha, beta, n\right) = \sum _{k \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} (y\left(k\right) \cdot \operatorname{gammaCoeff}\left(mu + alpha, k\right) \cdot y\left(n - k\right) \cdot \operatorname{gammaCoeff}\left(mu + beta, n - k\right) - y\left(k\right) \cdot \operatorname{gammaCoeff}\left(mu, k\right) \cdot y\left(n - k\right) \cdot \operatorname{gammaCoeff}\left(mu + alpha + beta, n - k\right))$$

*Formalization.* `D5/S3/Analytic/KarpZhangGamma/Series.gammaDelta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For a real sequence y, real mu,alpha,beta and natural n, gammaDelta(y,mu,alpha,beta,n) is the sum over k=0,...,n of y(k)gammaCoeff(mu+alpha,k)y(n-k)gammaCoeff(mu+beta,n-k) minus y(k)gammaCoeff(mu,k)y(n-k)gammaCoeff(mu+alpha+beta,n-k). This is the literal degree-n Cauchy coefficient of the gamma-series Turanian.

**Theorem 1.7 (Every coefficient of the gamma-series Turanian is nonnegative).**

$$\forall y \in Nat \to Real,\; \operatorname{IsLogConcave}\left(y\right) \Rightarrow \left(\forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; 0 < mu \Rightarrow \left(0 \le alpha \Rightarrow \left(0 \le beta \Rightarrow \left(\forall n \in Nat,\; 0 \le \operatorname{gammaDelta}\left(y, mu, alpha, beta, n\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Series.gamma_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every real sequence y satisfying D5.S3.Analytic.KarpZhangReciprocal.Result.IsLogConcave, every positive real mu, all nonnegative real alpha,beta and every natural n, gammaDelta(y,mu,alpha,beta,n) is nonnegative. The existing predicate includes nonnegativity and no internal zeros. No shift-integrality, convergence or growth assumption is added. Apply series_identification to the four factors, cancel their common positive scale product, and use the finite diagonal Cauchy identity. The remaining coefficient is the sum over m=0,...,floor(n/2) of Result.transformDelta(y,mu+1/2,alpha,beta,n-2m,m) divided by 2 to the natural power n-2m times 16 to the natural power m. Every summand is nonnegative by Result.two_variable_nonneg.

The scalar recurrence for the diagonal transform is (n+2)T(a,n+2)=T(a,n+1)/2+T(a+1,n)/8. The literal gamma coefficient satisfies (n+2)gammaCoeff(t,n+2)=gammaCoeff(t,n+1)/2+gammaCoeff(t+1,n)/2. The factor scale(t+1)=scale(t)/4 aligns these recurrences. Finite fibers r+2j=n justify the Euler-degree identity and every reindexing. For products, the index map sends (k,i,j) to (i+j,i,k-2i), with inverse (m,i,r) maps to (r+2i,i,m-i). This identifies the coefficient of the substituted product with the positive weighted sum of its bivariate coefficients.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Series.gammaCoeff`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Series.gammaDelta`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Series.gamma_half`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Series.positive_beta_transform`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Series.scale`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Series.series_identification`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Series.transformCoeff`
- Dependency: [D5/S3/Analytic/KarpZhangGamma/Result](Result.md)
