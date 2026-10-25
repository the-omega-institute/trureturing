# Symmetric interval convolutions

## Abstract

Balancing positive parameters in reciprocal Pochhammer interval convolutions.

**Definition 1.1 (Reciprocal coefficients).**

$$\forall n \in Nat,\; \forall t \in Real,\; \operatorname{c}\left(n, t\right) = \frac{\operatorname{Polynomial}.\operatorname{eval}\left(2 \cdot t, \operatorname{ascPochhammer}\left(Real, n\right)\right)}{\operatorname{Polynomial}.\operatorname{eval}\left(t, \operatorname{ascPochhammer}\left(Real, n\right)\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(n\right)}$$

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.c` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural n and real t, c(n,t) is the evaluation of ascPochhammer at 2t divided by the product of its evaluation at t and n factorial. For t positive this is the coefficient (2t)n/((t)n n!) in the reciprocal series of Conjecture 5.2, page 12.

**Definition 1.2 (Adjacent degree ratio).**

$$\forall j \in Nat,\; \forall t \in Real,\; \operatorname{lambda}\left(j, t\right) = \frac{2 \cdot t + j}{t + j}$$

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.lambda` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural j and real t, lambda(j,t) equals (2t+j)/(t+j).

**Definition 1.3 (Score increment).**

$$\forall j \in Nat,\; \forall t \in Real,\; \operatorname{eta}\left(j, t\right) = \frac{j}{\left(2 \cdot t + j\right) \cdot \left(t + j\right)}$$

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.eta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural j and real t, eta(j,t) equals j/((2t+j)(t+j)). In particular the increment at j=0 is zero.

**Definition 1.4 (Finite score sum).**

$$\forall n \in Nat,\; \forall t \in Real,\; \operatorname{psi}\left(n, t\right) = \sum _{j \in \operatorname{Finset}.\operatorname{range}\left(n\right)} (\operatorname{eta}\left(j, t\right))$$

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.psi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural n and real t, psi(n,t) is the sum of eta(j,t) over 0 <= j < n. The zero index contributes zero, so this equals the sum over 1 <= j < n.

**Definition 1.5 (Finite curvature sum).**

$$\forall n \in Nat,\; \forall t \in Real,\; \operatorname{chi}\left(n, t\right) = \sum _{j \in \operatorname{Finset}.\operatorname{range}\left(n\right)} (\frac{j \cdot \left(4 \cdot t + 3 \cdot j\right)}{\left(2 \cdot t + j\right)^{2} \cdot \left(t + j\right)^{2}})$$

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.chi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural n and real t, chi(n,t) is the sum over 0 <= j < n of j(4t+3j)/((2t+j)^2(t+j)^2).

**Theorem 1.6 (Uniform score and curvature estimates).**

$$\forall n \in Nat,\; \forall t \in Real,\; 0 < t \Rightarrow \left(0 < \operatorname{c}\left(n, t\right) \land \left(0 < \operatorname{lambda}\left(n, t\right) \land \left(\frac{\operatorname{c}\left(n + 1, t\right)}{\operatorname{c}\left(n, t\right)} = \frac{\operatorname{lambda}\left(n, t\right)}{n + 1} \land \left(\operatorname{HasDerivAt}\left(\operatorname{c}\left(n\right), \operatorname{c}\left(n, t\right) \cdot \operatorname{psi}\left(n, t\right), t\right) \land \left(\operatorname{HasDerivAt}\left(\operatorname{psi}\left(n\right), -\operatorname{chi}\left(n, t\right), t\right) \land \left(0 \le \operatorname{chi}\left(n, t\right) \land \left(n \cdot \operatorname{eta}\left(n - 1, t\right)^{2} \le \operatorname{chi}\left(n, t\right) \land \operatorname{Antitone}\left(\operatorname{fun} (j:Nat) \mapsto \operatorname{lambda}\left(j, t\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.coefficient_calculus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural n and positive real t, c(n,t) and lambda(n,t) are positive; c(n+1,t)/c(n,t) equals lambda(n,t)/(n+1); the derivative of c(n,t) is c(n,t)psi(n,t), the derivative of psi(n,t) is -chi(n,t). Curvature is nonnegative and at least n times eta(n-1,t) squared. The function j -> lambda(j,t) is antitone. Natural subtraction makes the n=0 curvature estimate meaningful, with both sides zero.

**Definition 1.7 (Interval convolution).**

$$\forall m \in Nat,\; \forall L \in Nat,\; \forall U \in Nat,\; \forall s \in Real,\; \forall t \in Real,\; \operatorname{F}\left(m, L, U, s, t\right) = \sum _{i \in \operatorname{Finset}.\operatorname{range}\left(U - L + 1\right)} (\operatorname{c}\left(L + i, s\right) \cdot \operatorname{c}\left(m - \left(L + i\right), t\right))$$

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.F` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For natural m, L, U and real s, t, F(m,L,U,s,t) is the sum of c(L+i,s)c(m-(L+i),t) over 0 <= i < U-L+1, with natural subtraction. When L <= U <= m this is exactly the convolution over L <= k <= U.

**Theorem 1.8 (Balancing inequality).**

$$\forall m \in Nat,\; \forall q \in Nat,\; 2 \cdot q \le m \Rightarrow \left(\forall a \in Real,\; \forall b \in Real,\; \forall c \in Real,\; \forall d \in Real,\; 0 < a \Rightarrow \left(a \le b \Rightarrow \left(b \le c \Rightarrow \left(c \le d \Rightarrow \left(a + d = b + c \Rightarrow \operatorname{F}\left(m, q, m - q, a, d\right) \le \operatorname{F}\left(m, q, m - q, b, c\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.symmetric_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural m and q with 2q <= m, and reals 0 < a <= b <= c <= d satisfying a+d=b+c, F(m,q,m-q,a,d) <= F(m,q,m-q,b,c). Singleton intervals and equal parameters are included. This proves the symmetric-tail inequality needed for the reciprocal-Pochhammer half of Conjecture 5.2; it makes no assertion about the other half.

**Theorem 1.9 (Arbitrary nonnegative shifts).**

$$\forall m \in Nat,\; \forall q \in Nat,\; 2 \cdot q \le m \Rightarrow \left(\forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; 0 < mu \Rightarrow \left(0 \le alpha \Rightarrow \left(0 \le beta \Rightarrow \operatorname{F}\left(m, q, m - q, mu, mu + alpha + beta\right) \le \operatorname{F}\left(m, q, m - q, mu + alpha, mu + beta\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.shift_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural m and q with 2q <= m, positive real mu, and nonnegative real alpha and beta, F(m,q,m-q,mu,mu+alpha+beta) <= F(m,q,m-q,mu+alpha,mu+beta). The shifts need not be ordered. This is the tail estimate consumed by the Abel reduction.

On a translated interval 0,...,n, normalize the positive coefficient products to probabilities. Use birth rate (m-k)lambda(k,s) below the upper endpoint and death rate k lambda(m-k,t) above the lower endpoint, with zero outward rates. The coefficient recurrence gives detailed balance. Antitonicity of lambda bounds edge curvature below by lambda(k,s)+lambda(m-k-1,t). The finite birth-and-death variance bound, a weighted square inequality, and chi(j,t) >= j eta(j-1,t)^2 absorb score variance into expected curvature. Differentiating log F(s,S-s) twice therefore gives a nonpositive second derivative. Mathlib's concavity criterion applies on the open interval (0,S). Reindexing k to m-k makes the two endpoint values equal, and the minimum principle for a concave function gives the balancing inequality.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.F`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.c`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.chi`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.coefficient_calculus`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.eta`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.lambda`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.psi`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.shift_tail`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.symmetric_tail`
- Dependency: [D5/S3/Analytic/KarpZhangReciprocal/BirthDeath](BirthDeath.md)
- Dependency: [D5/S3/Analytic/KummerRatio/Series](../KummerRatio/Series.md)
