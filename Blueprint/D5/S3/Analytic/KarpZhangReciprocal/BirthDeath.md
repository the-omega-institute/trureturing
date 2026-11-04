# Variance and edge curvature

## Abstract

A finite variance inequality for reversible birth-and-death rates.

**Definition 1.1 (Edge curvature).**

$$\forall p \in Nat \to Real,\; \forall r \in Nat \to Real,\; \forall i \in Nat,\; \operatorname{kappa}\left(p, r, i\right) = p\left(i\right) - p\left(i + 1\right) + r\left(i + 1\right) - r\left(i\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/BirthDeath.kappa` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For all real sequences p and r and every natural i, kappa(p,r,i) equals p(i)-p(i+1)+r(i+1)-r(i).

**Definition 1.2 (Finite variance).**

$$\forall n \in Nat,\; \forall pi \in Nat \to Real,\; \forall h \in Nat \to Real,\; \operatorname{variance}\left(n, pi, h\right) = \sum _{i \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} (pi\left(i\right) \cdot \left(h\left(i\right) - \sum _{j \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} (pi\left(j\right) \cdot h\left(j\right))\right)^{2})$$

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/BirthDeath.variance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For a natural n and real sequences pi and h, set a equal to the sum of pi(j)h(j) over 0 <= j <= n. Then variance(n,pi,h) is the sum over 0 <= i <= n of pi(i) times (h(i)-a) squared. Under probability normalization this is the usual variance.

**Theorem 1.3 (Curvature-weighted variance bound).**

$$\forall n \in Nat,\; \forall pi \in Nat \to Real,\; \forall p \in Nat \to Real,\; \forall r \in Nat \to Real,\; \forall h \in Nat \to Real,\; \left(\forall i \in Nat,\; i \le n \Rightarrow 0 < pi\left(i\right)\right) \Rightarrow \left(\sum _{i \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} (pi\left(i\right)) = 1 \Rightarrow \left(p\left(n\right) = 0 \Rightarrow \left(r\left(0\right) = 0 \Rightarrow \left(\left(\forall i \in Nat,\; i < n \Rightarrow 0 < p\left(i\right)\right) \Rightarrow \left(\left(\forall i \in Nat,\; 0 < i \Rightarrow \left(i \le n \Rightarrow 0 < r\left(i\right)\right)\right) \Rightarrow \left(\left(\forall i \in Nat,\; i < n \Rightarrow pi\left(i\right) \cdot p\left(i\right) = pi\left(i + 1\right) \cdot r\left(i + 1\right)\right) \Rightarrow \left(\left(\forall i \in Nat,\; i < n \Rightarrow 0 < \operatorname{kappa}\left(p, r, i\right)\right) \Rightarrow \operatorname{variance}\left(n, pi, h\right) \le \sum _{i \in \operatorname{Finset}.\operatorname{range}\left(n\right)} (\frac{pi\left(i\right) \cdot p\left(i\right)}{\operatorname{kappa}\left(p, r, i\right)} \cdot \left(h\left(i + 1\right) - h\left(i\right)\right)^{2})\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangReciprocal/BirthDeath.variance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Let n be any natural number. Suppose pi is positive on the vertices 0,...,n and sums to one there. Let p(n)=r(0)=0, let p(i)>0 for i<n, and let r(i)>0 for 0<i<=n. Assume detailed balance pi(i)p(i)=pi(i+1)r(i+1) and positive kappa(p,r,i) for every i<n. Then, for every real sequence h, variance(n,pi,h) is at most the sum over 0 <= i < n of pi(i)p(i)/kappa(p,r,i) times (h(i+1)-h(i)) squared. The hypotheses allow n=0, when the variance and the edge sum vanish.

Center h by its pi mean. An edge flux z is obtained by taking the negative cumulative centered mass and dividing by the edge weight. It satisfies h(i)=r(i)z(i)-p(i)z(i+1). Detailed balance converts the variance into the edge sum of pi(i)p(i)(h(i+1)-h(i))z(i+1). A pointwise square inequality and the same balance identity bound the sum of pi(i)p(i)kappa(i)z(i+1) squared by the variance. Weighted Cauchy-Schwarz then gives the stated estimate. All sums are finite, and no inverse operator or limiting argument is needed.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/BirthDeath.kappa`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/BirthDeath.variance`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/BirthDeath.variance_bound`
