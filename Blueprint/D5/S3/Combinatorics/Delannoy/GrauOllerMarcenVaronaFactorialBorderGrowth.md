# The factorial-border Delannoy conjecture

## Abstract

The factorial-border Delannoy diagonal ratio differs from n + 1 by a quantity tending to zero.

**Definition 1.1 (The bordered Delannoy array).**

$$\begin{aligned}\forall b \in \mathbb{N} \to \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{f}\left(b, 0, n\right) = b\left(n\right)\\\forall b \in \mathbb{N} \to \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{f}\left(b, m + 1, 0\right) = b\left(m + 1\right)\\\forall b \in \mathbb{N} \to \mathbb{N},\; \forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{f}\left(b, m + 1, n + 1\right) = \operatorname{f}\left(b, m, n + 1\right) + \operatorname{f}\left(b, m + 1, n\right) + \operatorname{f}\left(b, m, n\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.f` (`✓ std3`).

*Citation.* J. M. Grau, A. M. Oller-Marcén and J. L. Varona (2022). *A class of weighted Delannoy numbers*. DOI: [10.48550/arXiv.2501.09726](https://doi.org/10.48550/arXiv.2501.09726). URL: <https://arxiv.org/abs/2501.09726v2>.

*Commentary.*

The source array satisfies f_{m,n} = α f_{m−1,n} + β f_{m,n−1} + γ f_{m−1,n−1}, with prescribed borders. Section 6, arXiv page 18: "This happens, for instance, if α = β = γ = 1 and f_{n,0} = f_{0,n} = n!." Here b is any natural border, both axes use b, and the origin has value b(0). The three displayed equations give every recursion case.

**Definition 1.2 (The additive-error factorial-border limit).**

$$claimFactorial \Leftrightarrow \operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (n:\mathbb{N}) \mapsto \frac{(\operatorname{f}\left(\operatorname{Nat}.\operatorname{factorial}, n + 1, n + 1\right) : \mathbb{R})}{(\operatorname{f}\left(\operatorname{Nat}.\operatorname{factorial}, n, n\right) : \mathbb{R})} - ((n : \mathbb{R}) + 1)), \operatorname{Filter}.\operatorname{atTop}, (\mathcal{N}(0))\right)$$

*Formalization.* `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.claimFactorial` (`✓ std3`).

*Citation.* J. M. Grau, A. M. Oller-Marcén and J. L. Varona (2022). *A class of weighted Delannoy numbers*. DOI: [10.48550/arXiv.2501.09726](https://doi.org/10.48550/arXiv.2501.09726). URL: <https://arxiv.org/abs/2501.09726v2>.

*Commentary.*

Section 6, arXiv page 18: "In this example [19, OEIS A346374] we conjecture that f_{n+1,n+1}/f_{n,n} ≈ n + 1 (where a_n ≈ b_n means, as usual, that a_n − b_n → 0 when n → ∞)." The border is Nat.factorial, including 0! = 1. The diagonal entries and n are cast to the reals, and the ratio uses real division.

**Definition 1.3 (Border increments).**

$$\begin{aligned}\forall b \in \mathbb{N} \to \mathbb{N},\; \operatorname{delta}\left(b, 0\right) = (b\left(0\right) : \mathbb{R})\\\forall b \in \mathbb{N} \to \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{delta}\left(b, n + 1\right) = (b\left(n + 1\right) : \mathbb{R}) - (b\left(n\right) : \mathbb{R})\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first increment is b(0); every later increment is the real difference of consecutive border values.

**Definition 1.4 (The finite border convolution).**

$$\forall a \in \mathbb{N} \to \mathbb{R},\; \forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{conv}\left(a, m, n\right) = \sum_{j \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} (a\left(j\right) \cdot (\operatorname{f}\left((\operatorname{fun} (_:\mathbb{N}) \mapsto 1), m - j, n\right) : \mathbb{R}))$$

*Formalization.* `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.conv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum includes j = 0 through m. The second factor is the unit-border array. The index m−j uses natural subtraction.

**Theorem 1.5 (The exact diagonal convolution).**

$$\forall b \in \mathbb{N} \to \mathbb{N},\; \forall n \in \mathbb{N},\; (\operatorname{f}\left(b, n, n\right) : \mathbb{R}) = 2 \cdot \operatorname{conv}\left(\operatorname{delta}\left(b\right), n, n\right) - (b\left(0\right) : \mathbb{R}) \cdot (\operatorname{f}\left((\operatorname{fun} (_:\mathbb{N}) \mapsto 1), n, n\right) : \mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.diagonal_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction in the two coordinates gives the full border convolution; its two symmetric terms agree on the diagonal.

**Definition 1.6 (The limiting factorial weights).**

$$\forall k \in \mathbb{N},\; \operatorname{W}\left(k\right) = \frac{(2 : \mathbb{R})^{k}}{(\operatorname{Nat}.\operatorname{factorial}\left(k\right) : \mathbb{R})}$$

*Formalization.* `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.W` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive exponential-series weights are 2^k/k!.

**Definition 1.7 (A summable majorant).**

$$\forall k \in \mathbb{N},\; \operatorname{M}\left(k\right) = \frac{(6 : \mathbb{R})^{k}}{(\operatorname{Nat}.\operatorname{factorial}\left(k\right) : \mathbb{R})}$$

*Formalization.* `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.M` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weights 6^k/k! bound the entire normalized convolution, including indices past n.

**Definition 1.8 (The normalized unit-border kernel).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{Q}\left(n, k\right) = \operatorname{if} (k \le n) \operatorname{then} \frac{\operatorname{Polynomial}.\operatorname{eval}\left(1, \operatorname{qAB}\left(k, n\right)\right)}{(\operatorname{Nat}.\operatorname{factorial}\left(k\right) : \mathbb{R}) \cdot (\operatorname{Nat}.\operatorname{choose}\left(n, k\right) : \mathbb{R})} \operatorname{else} 0$$

*Formalization.* `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For k ≤ n the numerator is the polynomial qAB(k,n) evaluated at one, the binomial sum for the unit-border Delannoy array. For k > n the kernel is zero.

**Theorem 1.9 (The kernel vanishes past n).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; n < k \Rightarrow (\operatorname{Q}\left(n, k\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.Q_of_gt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero branch gives finite support in k.

**Theorem 1.10 (The kernel is nonnegative).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; 0 \le \operatorname{Q}\left(n, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.Q_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every binomial summand and denominator is nonnegative.

**Theorem 1.11 (The majorant bounds the limiting weights).**

$$\forall k \in \mathbb{N},\; \operatorname{W}\left(k\right) \le \operatorname{M}\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.W_le_M` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inequality follows from 2^k ≤ 6^k and the positive factorial denominator.

**Theorem 1.12 (A global first-order bound).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \left|(n : \mathbb{R}) \cdot \left(\operatorname{Q}\left(n, k\right) - \operatorname{W}\left(k\right)\right)\right| \le (k : \mathbb{R}) \cdot \operatorname{M}\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.Q_scaled_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower-degree terms in the binomial kernel are bounded by k times the majorant, uniformly in n. The zero extension obeys the same bound.

**Definition 1.13 (The fixed-index first-order coefficient).**

$$\forall k \in \mathbb{N},\; \operatorname{G}\left(k\right) = \frac{1}{(\operatorname{Nat}.\operatorname{factorial}\left(k\right) : \mathbb{R})} \cdot \sum_{i \in \operatorname{Finset}.\operatorname{range}\left(k\right)} ((2 : \mathbb{R})^{i} \cdot (\operatorname{Nat}.\operatorname{choose}\left(k, i\right) : \mathbb{R}) \cdot \operatorname{if} (k = i + 1) \operatorname{then} (k : \mathbb{R}) \operatorname{else} 0)$$

*Formalization.* `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite sum has at most one nonzero term, namely i = k − 1 when k is positive.

**Theorem 1.14 (The fixed-index first-order limit).**

$$\forall k \in \mathbb{N},\; \operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (n:\mathbb{N}) \mapsto (n : \mathbb{R}) \cdot \left(\operatorname{Q}\left(n, k\right) - \operatorname{W}\left(k\right)\right)), \operatorname{Filter}.\operatorname{atTop}, (\mathcal{N}(\operatorname{G}\left(k\right)))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.Q_scaled_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The asymptotic formula for Nat.choose reduces each fixed-index quotient to a power of 1/n; only the immediately lower degree survives scaling by n.

**Theorem 1.15 (The majorant is summable).**

$$\operatorname{Summable}\left(M\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.summable_M` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the summability of the exponential series at six.

**Theorem 1.16 (The linearly weighted majorant is summable).**

$$\operatorname{Summable}\left((\operatorname{fun} (k:\mathbb{N}) \mapsto \left((k : \mathbb{R}) + 1\right) \cdot \operatorname{M}\left(k\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.summable_succ_M` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The additional polynomial factor is bounded by an exponential weight.

**Theorem 1.17 (First-order convergence implies convergence).**

$$\forall r \in \mathbb{N} \to \mathbb{R},\; \forall C \in \mathbb{R},\; \forall K \in \mathbb{R},\; \operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (n:\mathbb{N}) \mapsto (n : \mathbb{R}) \cdot \left(r\left(n\right) - C\right)), \operatorname{Filter}.\operatorname{atTop}, (\mathcal{N}(K))\right) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left((r), \operatorname{Filter}.\operatorname{atTop}, (\mathcal{N}(C))\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.tendsto_of_scaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the scaled error by 1/n gives convergence of the unscaled error to zero.

**Definition 1.18 (The preceding-border correction).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{P}\left(n, k\right) = \operatorname{if} (k < n) \operatorname{then} \frac{\operatorname{Q}\left(n, k\right)}{((n - k : \mathbb{N}) : \mathbb{R})} \operatorname{else} 0$$

*Formalization.* `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For k < n divide Q(n,k) by the real cast of the natural number n−k. Otherwise the correction is zero.

**Theorem 1.19 (The correction has a summable bound).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \left|(n : \mathbb{R}) \cdot \operatorname{P}\left(n, k\right)\right| \le \left((k : \mathbb{R}) + 1\right) \cdot \operatorname{M}\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.P_scaled_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The elementary inequality n ≤ (k+1)(n−k) bounds the additional factor on the nonzero branch.

**Theorem 1.20 (The fixed-index correction limit).**

$$\forall k \in \mathbb{N},\; \operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (n:\mathbb{N}) \mapsto (n : \mathbb{R}) \cdot \operatorname{P}\left(n, k\right)), \operatorname{Filter}.\operatorname{atTop}, (\mathcal{N}(\operatorname{W}\left(k\right)))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.P_scaled_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed k, n/(n−k) tends to one and Q(n,k) tends to W(k).

**Theorem 1.21 (The diagonal kernel is negligible).**

$$\operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (n:\mathbb{N}) \mapsto (n : \mathbb{R}) \cdot \operatorname{Q}\left(n, n\right)), \operatorname{Filter}.\operatorname{atTop}, (\mathcal{N}(0))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.diagonal_Q_scaled_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal term is squeezed by n M(n), which tends to zero by summability.

**Theorem 1.22 (The factorial form of the kernel).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; k \le n \Rightarrow (\operatorname{Q}\left(n, k\right) = \frac{(\operatorname{Nat}.\operatorname{factorial}\left(n - k\right) : \mathbb{R}) \cdot (\operatorname{f}\left((\operatorname{fun} (_:\mathbb{N}) \mapsto 1), k, n\right) : \mathbb{R})}{(\operatorname{Nat}.\operatorname{factorial}\left(n\right) : \mathbb{R})})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.Q_factorial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factorial identity for Nat.choose converts the denominator to the normalized factorial border.

**Theorem 1.23 (First-order ratio transfer).**

$$\forall a \in \mathbb{N} \to \mathbb{R},\; \forall b \in \mathbb{N} \to \mathbb{R},\; \forall r \in \mathbb{N} \to \mathbb{R},\; \forall C \in \mathbb{R},\; \forall K \in \mathbb{R},\; \forall L \in \mathbb{R},\; \left(\left(\forall n \in \mathbb{N},\; b\left(n\right) \ne 0\right) \land \left(\left(\forall n \in \mathbb{N},\; a\left(n\right) = b\left(n\right) \cdot r\left(n\right)\right) \land \left(C \ne 0 \land \left(\operatorname{Filter}.\operatorname{Tendsto}\left((r), \operatorname{Filter}.\operatorname{atTop}, (\mathcal{N}(C))\right) \land \left(\operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (n:\mathbb{N}) \mapsto (n : \mathbb{R}) \cdot \left(r\left(n\right) - C\right)), \operatorname{Filter}.\operatorname{atTop}, (\mathcal{N}(K))\right) \land \operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (n:\mathbb{N}) \mapsto \frac{\frac{b\left(n + 1\right)}{b\left(n\right)}}{(n : \mathbb{R}) + 1}), \operatorname{Filter}.\operatorname{atTop}, (\mathcal{N}(L))\right)\right)\right)\right)\right)\right) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (n:\mathbb{N}) \mapsto \frac{a\left(n + 1\right)}{a\left(n\right)} - \frac{b\left(n + 1\right)}{b\left(n\right)}), \operatorname{Filter}.\operatorname{atTop}, (\mathcal{N}(0))\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.ratio_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A first-order expansion of r gives (n+1)(r(n+1)−r(n)) → 0. If a = b r with a nonzero limiting r, the diagonal and border ratios differ by a quantity tending to zero.

**Theorem 1.24 (The factorial-border limit holds).**

$$\operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (n:\mathbb{N}) \mapsto \frac{(\operatorname{f}\left(\operatorname{Nat}.\operatorname{factorial}, n + 1, n + 1\right) : \mathbb{R})}{(\operatorname{f}\left(\operatorname{Nat}.\operatorname{factorial}, n, n\right) : \mathbb{R})} - ((n : \mathbb{R}) + 1)), \operatorname{Filter}.\operatorname{atTop}, (\mathcal{N}(0))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. M. Grau, A. M. Oller-Marcén and J. L. Varona (2022). *A class of weighted Delannoy numbers*. DOI: [10.48550/arXiv.2501.09726](https://doi.org/10.48550/arXiv.2501.09726). URL: <https://arxiv.org/abs/2501.09726v2>.

*Commentary.*

The exact convolution splits the normalized diagonal into Q, P and its diagonal correction. Their global summable bounds permit first-order dominated convergence. The limiting normalizing constant is positive because W(0) = 1. First-order ratio transfer then gives the stated additive-error limit. No explicit rate or second-order expansion is asserted.

## References

- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.G`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.M`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.P`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.P_scaled_bound`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.P_scaled_limit`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.Q`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.Q_factorial`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.Q_nonneg`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.Q_of_gt`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.Q_scaled_bound`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.Q_scaled_limit`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.W`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.W_le_M`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.claimFactorial`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.conv`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.delta`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.diagonal_Q_scaled_limit`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.diagonal_convolution`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.f`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.ratio_transfer`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.result`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.summable_M`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.summable_succ_M`
- Truth anchor: `D5/S1/Recurrence/GrauOllerMarcenVaronaFactorialBorderGrowth.tendsto_of_scaled`
- Dependency: [D5/S3/Combinatorics/Matroids/SpeyerUniformNormality](../../S3/Combinatorics/Matroids/SpeyerUniformNormality.md)
