# Symmetric interval convolutions

## Abstract

Balancing positive parameters in reciprocal Pochhammer interval convolutions.

**Definition 1.1 (Interval convolution).**

Lean statement: `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.F`

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.F` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For natural m, L, U and real s, t, F(m,L,U,s,t) is the sum of c(L+i,s)c(m-(L+i),t) over 0 <= i < U-L+1, with natural subtraction. When L <= U <= m this is exactly the convolution over L <= k <= U.

**Theorem 1.2 (Balancing inequality).**

Lean statement: `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.symmetric_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.symmetric_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural m and q with 2q <= m, and reals 0 < a <= b <= c <= d satisfying a+d=b+c, F(m,q,m-q,a,d) <= F(m,q,m-q,b,c). Singleton intervals and equal parameters are included. This proves the symmetric-tail inequality needed for the reciprocal-Pochhammer half of Conjecture 5.2; it makes no assertion about the other half.

**Theorem 1.3 (Arbitrary nonnegative shifts).**

Lean statement: `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.shift_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.shift_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural m and q with 2q <= m, positive real mu, and nonnegative real alpha and beta, F(m,q,m-q,mu,mu+alpha+beta) <= F(m,q,m-q,mu+alpha,mu+beta). The shifts need not be ordered. This is the tail estimate consumed by the Abel reduction.

On a translated interval 0,...,n, normalize the positive coefficient products to probabilities. Use birth rate (m-k)lambda(k,s) below the upper endpoint and death rate k lambda(m-k,t) above the lower endpoint, with zero outward rates. The coefficient recurrence gives detailed balance. Antitonicity of lambda bounds edge curvature below by lambda(k,s)+lambda(m-k-1,t). The finite birth-and-death variance bound, a weighted square inequality, and chi(j,t) >= j eta(j-1,t)^2 absorb score variance into expected curvature. Differentiating log F(s,S-s) twice therefore gives a nonpositive second derivative. Mathlib's concavity criterion applies on the open interval (0,S). Reindexing k to m-k makes the two endpoint values equal, and the minimum principle for a concave function gives the balancing inequality.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.F`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.shift_tail`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution.symmetric_tail`
- Dependency: [D5/S3/Analytic/KarpZhangReciprocal/BirthDeath](BirthDeath.md)
- Dependency: [D5/S3/Analytic/KarpZhangReciprocal/Coeff](Coeff.md)
