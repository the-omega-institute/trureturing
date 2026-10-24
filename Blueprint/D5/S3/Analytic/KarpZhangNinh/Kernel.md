# Paired Pochhammer kernels

## Abstract

Single sign change of the paired triple-Pochhammer kernels.

**Definition 1.1 (The positive-degree coefficient).**

$$\forall n \in Nat,\; \forall t \in Real,\; \operatorname{a}\left(n, t\right) = \operatorname{ite}\left(n = 0, 0, \frac{\operatorname{Polynomial.eval}\left(t, \operatorname{ascPochhammer}\left(Real, 3 \cdot n\right)\right)}{(\operatorname{Nat.sub}\left(3 \cdot n, 1\right))!}\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Kernel.a` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Conjecture 3.8, page 8: “Assume that {fₙ}ₙ₌₀∞ is log-concave and independent of µ. Then the function µ → f(µ; x) = ∑ₙ₌₁∞ fₙ (µ)₃ₙ/(3n − 1)! xⁿ is coefficient-wise log-concave.” The coefficient in positive degree is the displayed rising-factorial quotient. Its degree-zero extension is zero because the series starts at one.

**Definition 1.2 (The unpaired Turanian kernel).**

$$\forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; \forall k \in Nat,\; \operatorname{raw}\left(mu, alpha, beta, m, k\right) = \operatorname{a}\left(k, mu + alpha\right) \cdot \operatorname{a}\left(\operatorname{Nat.sub}\left(m, k\right), mu + beta\right) - \operatorname{a}\left(k, mu\right) \cdot \operatorname{a}\left(\operatorname{Nat.sub}\left(m, k\right), mu + alpha + beta\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Kernel.raw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two products are the degree-k and degree-(m-k) factors in the two Cauchy products. Natural subtraction is used only for indices in the finite coefficient sum.

**Definition 1.3 (The reflected kernel).**

$$\forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; \forall k \in Nat,\; \operatorname{paired}\left(mu, alpha, beta, m, k\right) = \operatorname{ite}\left(2 \cdot k = m, \operatorname{raw}\left(mu, alpha, beta, m, k\right), \operatorname{raw}\left(mu, alpha, beta, m, k\right) + \operatorname{raw}\left(mu, alpha, beta, m, \operatorname{Nat.sub}\left(m, k\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Kernel.paired` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reflection sends k to m-k. The central index contributes once, while every other paired term is the sum of both reflected terms.

**Definition 1.4 (The factorial-free paired difference).**

$$\forall a \in Real,\; \forall b \in Real,\; \forall c \in Real,\; \forall N \in Nat,\; \forall k \in Nat,\; \operatorname{pairPoch}\left(a, b, c, N, k\right) = \operatorname{Polynomial.eval}\left(a + b, \operatorname{ascPochhammer}\left(Real, k\right)\right) \cdot \operatorname{Polynomial.eval}\left(a + c, \operatorname{ascPochhammer}\left(Real, \operatorname{Nat.sub}\left(N, k\right)\right)\right) + \operatorname{Polynomial.eval}\left(a + c, \operatorname{ascPochhammer}\left(Real, k\right)\right) \cdot \operatorname{Polynomial.eval}\left(a + b, \operatorname{ascPochhammer}\left(Real, \operatorname{Nat.sub}\left(N, k\right)\right)\right) - \operatorname{Polynomial.eval}\left(a, \operatorname{ascPochhammer}\left(Real, k\right)\right) \cdot \operatorname{Polynomial.eval}\left(a + b + c, \operatorname{ascPochhammer}\left(Real, \operatorname{Nat.sub}\left(N, k\right)\right)\right) - \operatorname{Polynomial.eval}\left(a + b + c, \operatorname{ascPochhammer}\left(Real, k\right)\right) \cdot \operatorname{Polynomial.eval}\left(a, \operatorname{ascPochhammer}\left(Real, \operatorname{Nat.sub}\left(N, k\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Kernel.pairPoch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four rising-factorial products are the paired kernel before positive factorial denominators are removed.

**Theorem 1.5 (Polynomial parameter dependence).**

$$\forall n \in Nat,\; \operatorname{Continuous}\left(\operatorname{a}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Kernel.a_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every coefficient is a polynomial divided by a fixed positive factorial. Continuity supplies the boundary values of parameter inequalities.

**Theorem 1.6 (Strict backward propagation).**

$$\forall a \in Real,\; \forall b \in Real,\; \forall c \in Real,\; \forall N \in Nat,\; \forall k \in Nat,\; (0 < a) \Rightarrow ((0 < b) \Rightarrow ((0 < c) \Rightarrow ((1 \le k) \Rightarrow ((2 \cdot k \le N) \Rightarrow ((\operatorname{pairPoch}\left(a, b, c, N, k\right) \le 0) \Rightarrow (\operatorname{pairPoch}\left(a, b, c, N, \operatorname{Nat.sub}\left(k, 1\right)\right) < 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Kernel.paired_sign_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the paired difference is nonpositive, the larger unmixed product exceeds both mixed products. Comparing the four reciprocal multipliers after moving one factor from the shorter length to the longer length makes the preceding paired difference strictly negative.

**Theorem 1.7 (At most one sign change).**

$$\forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; (0 < mu) \Rightarrow ((0 < alpha) \Rightarrow ((0 < beta) \Rightarrow (\forall i \in Nat,\; (i \le \operatorname{Nat.div}\left(m, 2\right)) \Rightarrow (\forall j \in Nat,\; (j \le \operatorname{Nat.div}\left(m, 2\right)) \Rightarrow ((i < j) \Rightarrow ((0 < \operatorname{paired}\left(mu, alpha, beta, m, i\right)) \Rightarrow (0 \le \operatorname{paired}\left(mu, alpha, beta, m, j\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Kernel.paired_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Backward propagation between rising-factorial lengths 3i and 3j excludes a positive triple-Pochhammer pair followed by a negative one. Positive factorial denominators preserve signs; the middle pair has an additional positive factor of two.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Kernel.a`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Kernel.a_continuous`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Kernel.pairPoch`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Kernel.paired`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Kernel.paired_sign`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Kernel.paired_sign_step`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Kernel.raw`
