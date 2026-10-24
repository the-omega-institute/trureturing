# Karp and Zhang's Conjecture 3.8

## Abstract

Triple rising-factorial series preserve coefficientwise log-concavity.

**Definition 1.1 (The Turanian coefficient).**

$$\forall f \in Nat \to Real,\; \forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; delta\left(f, mu, alpha, beta, m\right) = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} f\left(k\right) \cdot f\left(m - k\right) \cdot \operatorname{Kernel}.\operatorname{raw}\left(mu, alpha, beta, m, k\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Result.delta` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

The source defines the Turanian as f(mu+alpha;x)f(mu+beta;x)-f(mu;x)f(mu+alpha+beta;x). Its coefficientwise convention, page 2, is: “if the coefficients δₖ at all powers of x in (2) are non-negative (non-positive) for all α, β ≥ 0 we will say that µ → f(µ; x) is coefficient-wise log-concave”. Here Kernel.a has zero constant coefficient, so the endpoint summands vanish. A single coefficient sequence is fixed independently of all three real parameters.

**Definition 1.2 (The unweighted convolution).**

$$\forall m \in Nat,\; \forall u \in Real,\; \forall v \in Real,\; Z\left(m, u, v\right) = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} \operatorname{Kernel}.\operatorname{a}\left(k, u\right) \cdot \operatorname{Kernel}.\operatorname{a}\left(m - k, v\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Result.Z` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Multiplication by (3m)! identifies this convolution with the beta lift of Homogeneous.P. Homogeneous balancing therefore passes to the rising-factorial convolution.

**Definition 1.3 (The exact coefficient assertion).**

$$claim \Leftrightarrow \left(\forall f \in Nat \to Real,\; \forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; \operatorname{KarpZhangReciprocal}.\operatorname{Result}.\operatorname{IsLogConcave}\left(f\right) \Rightarrow \left(0 \le mu \Rightarrow \left(0 \le alpha \Rightarrow \left(0 \le beta \Rightarrow 0 \le delta\left(f, mu, alpha, beta, m\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Result.claim` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Conjecture 3.8, page 8: “Assume that {fₙ}ₙ₌₀∞ is log-concave and independent of µ. Then the function µ → f(µ; x) = Σₙ₌₁∞ fₙ (µ)₃ₙ/(3n − 1)! xⁿ is coefficient-wise log-concave.”

The reused KarpZhangReciprocal.Result.IsLogConcave is Definition 1.1, including nonnegativity, nontriviality, adjacent inequalities and interval support. Every natural coefficient degree and all nonnegative real base parameters and shifts are quantified. The finite Cauchy sums require no analytic convergence assumption.

**Theorem 1.4 (Nonnegativity in every degree).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/karp-zhang-2023-conjecture-3-8` (proved) by `D5/S3/Analytic/KarpZhangNinh/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"karp-zhang-2023-conjecture-3-8","declaration_gid":"D5/S3/Analytic/KarpZhangNinh/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Trisection binomial identities prove homogeneous balancing. The general symmetric beta-lifting theorem transfers balancing to Z and makes its full Turanian sum nonnegative. The paired rising-factorial sign lemma and the existing KarpZhangGamma.Weighting.weighted_sum_nonneg give nonnegative central tails. The existing KarpZhangReciprocal.Result.abel_layers decomposes delta into these tails with increments of f(k)f(m-k); balanced_step makes every increment nonnegative. Polynomial continuity includes zero parameters and zero shifts.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Result.Z`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Result.claim`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Result.delta`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Result.result`
- Dependency: [D5/S3/Analytic/KarpZhangGamma/Result](../KarpZhangGamma/Result.md)
- Dependency: [D5/S3/Analytic/KarpZhangNinh/Beta](Beta.md)
- Dependency: [D5/S3/Analytic/KarpZhangNinh/Homogeneous](Homogeneous.md)
- Dependency: [D5/S3/Analytic/KarpZhangNinh/Kernel](Kernel.md)
