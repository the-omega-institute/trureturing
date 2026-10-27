# Karp and Zhang's Conjecture 3.8

## Abstract

Triple rising-factorial series preserve coefficientwise log-concavity.

**Definition 1.1 (The positive-degree coefficient).**

$$\forall n \in Nat,\; \forall t \in Real,\; \operatorname{a}\left(n, t\right) = \operatorname{ite}\left(n = 0, 0, \frac{\operatorname{Polynomial.eval}\left(t, \operatorname{ascPochhammer}\left(Real, 3 \cdot n\right)\right)}{(\operatorname{Nat.sub}\left(3 \cdot n, 1\right))!}\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Result.a` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Conjecture 3.8, page 8: “Assume that {fₙ}ₙ₌₀∞ is log-concave and independent of µ. Then the function µ → f(µ; x) = ∑ₙ₌₁∞ fₙ (µ)₃ₙ/(3n − 1)! xⁿ is coefficient-wise log-concave.” The coefficient in positive degree is the displayed rising-factorial quotient. Its degree-zero extension is zero because the series starts at one.

**Definition 1.2 (The unpaired Turanian kernel).**

$$\forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; \forall k \in Nat,\; \operatorname{raw}\left(mu, alpha, beta, m, k\right) = \operatorname{a}\left(k, mu + alpha\right) \cdot \operatorname{a}\left(\operatorname{Nat.sub}\left(m, k\right), mu + beta\right) - \operatorname{a}\left(k, mu\right) \cdot \operatorname{a}\left(\operatorname{Nat.sub}\left(m, k\right), mu + alpha + beta\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Result.raw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two products are the degree-k and degree-(m-k) factors in the two Cauchy products. Natural subtraction is used only for indices in the finite coefficient sum.

**Definition 1.3 (The reflected kernel).**

$$\forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; \forall k \in Nat,\; \operatorname{paired}\left(mu, alpha, beta, m, k\right) = \operatorname{ite}\left(2 \cdot k = m, \operatorname{raw}\left(mu, alpha, beta, m, k\right), \operatorname{raw}\left(mu, alpha, beta, m, k\right) + \operatorname{raw}\left(mu, alpha, beta, m, \operatorname{Nat.sub}\left(m, k\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Result.paired` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reflection sends k to m-k. The central index contributes once, while every other paired term is the sum of both reflected terms.

**Definition 1.4 (The factorial-free paired difference).**

$$\forall a \in Real,\; \forall b \in Real,\; \forall c \in Real,\; \forall N \in Nat,\; \forall k \in Nat,\; \operatorname{pairPoch}\left(a, b, c, N, k\right) = \operatorname{Polynomial.eval}\left(a + b, \operatorname{ascPochhammer}\left(Real, k\right)\right) \cdot \operatorname{Polynomial.eval}\left(a + c, \operatorname{ascPochhammer}\left(Real, \operatorname{Nat.sub}\left(N, k\right)\right)\right) + \operatorname{Polynomial.eval}\left(a + c, \operatorname{ascPochhammer}\left(Real, k\right)\right) \cdot \operatorname{Polynomial.eval}\left(a + b, \operatorname{ascPochhammer}\left(Real, \operatorname{Nat.sub}\left(N, k\right)\right)\right) - \operatorname{Polynomial.eval}\left(a, \operatorname{ascPochhammer}\left(Real, k\right)\right) \cdot \operatorname{Polynomial.eval}\left(a + b + c, \operatorname{ascPochhammer}\left(Real, \operatorname{Nat.sub}\left(N, k\right)\right)\right) - \operatorname{Polynomial.eval}\left(a + b + c, \operatorname{ascPochhammer}\left(Real, k\right)\right) \cdot \operatorname{Polynomial.eval}\left(a, \operatorname{ascPochhammer}\left(Real, \operatorname{Nat.sub}\left(N, k\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Result.pairPoch` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Lemma 3.1, printed page 4: “Let k, m ∈ N₀ with k ≤ m/2, µ ≥ 0 and α, β > 0. Set”. Formula (8) defines Tₖ,ₘ as (µ+α)ₖ(µ+β)ₘ₋ₖ + (µ+α)ₘ₋ₖ(µ+β)ₖ − (µ)ₖ(µ+α+β)ₘ₋ₖ − (µ)ₘ₋ₖ(µ+α+β)ₖ. The displayed pairPoch uses a, b, c and N for µ, α, β and m. It is the paired kernel before positive factorial denominators are removed.

**Theorem 1.5 (Polynomial parameter dependence).**

$$\forall n \in Nat,\; \operatorname{Continuous}\left(\operatorname{a}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Result.a_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every coefficient is a polynomial divided by a fixed positive factorial. Continuity supplies the boundary values of parameter inequalities.

**Theorem 1.6 (Strict backward propagation).**

$$\forall a \in Real,\; \forall b \in Real,\; \forall c \in Real,\; \forall N \in Nat,\; \forall k \in Nat,\; (0 < a) \Rightarrow ((0 < b) \Rightarrow ((0 < c) \Rightarrow ((1 \le k) \Rightarrow ((2 \cdot k \le N) \Rightarrow ((\operatorname{pairPoch}\left(a, b, c, N, k\right) \le 0) \Rightarrow (\operatorname{pairPoch}\left(a, b, c, N, \operatorname{Nat.sub}\left(k, 1\right)\right) < 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Result.paired_sign_step` (`✓ std3`). ∎

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Lemma 3.1, printed page 4: “If Tₖ,ₘ ≤ 0 for some 1 ≤ k ≤ m/2, then Tₖ₋₁,ₘ < 0.” The source allows µ ≥ 0; the theorem uses its positive-µ specialization a > 0. Comparing the four reciprocal multipliers after moving one factor from the shorter length to the longer length proves the stated backward implication.

**Theorem 1.7 (At most one sign change).**

$$\forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; (0 < mu) \Rightarrow ((0 < alpha) \Rightarrow ((0 < beta) \Rightarrow (\forall i \in Nat,\; (i \le \operatorname{Nat.div}\left(m, 2\right)) \Rightarrow (\forall j \in Nat,\; (j \le \operatorname{Nat.div}\left(m, 2\right)) \Rightarrow ((i < j) \Rightarrow ((0 < \operatorname{paired}\left(mu, alpha, beta, m, i\right)) \Rightarrow (0 \le \operatorname{paired}\left(mu, alpha, beta, m, j\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Result.paired_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Backward propagation between rising-factorial lengths 3i and 3j excludes a positive triple-Pochhammer pair followed by a negative one. Positive factorial denominators preserve signs; the middle pair has an additional positive factor of two.

**Definition 1.8 (The Turanian coefficient).**

$$\forall f \in Nat \to Real,\; \forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; delta\left(f, mu, alpha, beta, m\right) = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} f\left(k\right) \cdot f\left(m - k\right) \cdot \operatorname{Kernel}.\operatorname{raw}\left(mu, alpha, beta, m, k\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Result.delta` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

The source defines the Turanian as f(mu+alpha;x)f(mu+beta;x)-f(mu;x)f(mu+alpha+beta;x). Its coefficientwise convention, printed page 1, is: “if the coefficients δₖ at all powers of x in (2) are non-negative (non-positive) for all α, β ≥ 0 we will say that µ → f(µ; x) is coefficient-wise log-concave (log-convex ).” Here Kernel.a has zero constant coefficient, so the endpoint summands vanish. A single coefficient sequence is fixed independently of all three real parameters.

**Definition 1.9 (The unweighted convolution).**

$$\forall m \in Nat,\; \forall u \in Real,\; \forall v \in Real,\; Z\left(m, u, v\right) = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} \operatorname{Kernel}.\operatorname{a}\left(k, u\right) \cdot \operatorname{Kernel}.\operatorname{a}\left(m - k, v\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Result.Z` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Multiplication by (3m)! identifies this convolution with the beta lift of Homogeneous.P. Homogeneous balancing therefore passes to the rising-factorial convolution.

**Definition 1.10 (The exact coefficient assertion).**

$$claim \Leftrightarrow \left(\forall f \in Nat \to Real,\; \forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; \operatorname{KarpZhangReciprocal}.\operatorname{Result}.\operatorname{IsLogConcave}\left(f\right) \Rightarrow \left(0 \le mu \Rightarrow \left(0 \le alpha \Rightarrow \left(0 \le beta \Rightarrow 0 \le delta\left(f, mu, alpha, beta, m\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Result.claim` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Conjecture 3.8, page 8: “Assume that {fₙ}ₙ₌₀∞ is log-concave and independent of µ. Then the function µ → f(µ; x) = Σₙ₌₁∞ fₙ (µ)₃ₙ/(3n − 1)! xⁿ is coefficient-wise log-concave.”

The reused KarpZhangReciprocal.Result.IsLogConcave is Definition 1.1, including nonnegativity, nontriviality, adjacent inequalities and interval support. Every natural coefficient degree and all nonnegative real base parameters and shifts are quantified. The finite Cauchy sums require no analytic convergence assumption.

**Theorem 1.11 (Nonnegativity in every degree).**

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
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Result.a`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Result.a_continuous`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Result.claim`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Result.delta`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Result.pairPoch`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Result.paired`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Result.paired_sign`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Result.paired_sign_step`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Result.raw`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Result.result`
- Dependency: [D5/S3/Analytic/KarpZhangGamma/Result](../KarpZhangGamma/Result.md)
- Dependency: [D5/S3/Analytic/KarpZhangNinh/Beta](Beta.md)
- Dependency: [D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations](../SeriesInequalities/KarpQuadraticTruncations.md)
