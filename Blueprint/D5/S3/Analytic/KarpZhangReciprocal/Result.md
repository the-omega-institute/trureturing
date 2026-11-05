# Reciprocal coefficients and Abel reduction

## Abstract

The reciprocal-Pochhammer half of Karp-Zhang Conjecture 5.2.

**Definition 1.1 (The sequence convention).**

$$\forall y \in Nat \to Real,\; \operatorname{IsLogConcave}\left(y\right) \Leftrightarrow \left(\left(\forall k \in Nat,\; 0 \le y\left(k\right)\right) \land \left(\left(\exists k \in Nat,\; y\left(k\right) \ne 0\right) \land \left(\left(\forall k \in Nat,\; 1 \le k \Rightarrow y\left(k - 1\right) \cdot y\left(k + 1\right) \le y\left(k\right)^{2}\right) \land \left(\forall N \in Nat,\; y\left(N\right) = 0 \Rightarrow \left(\left(\forall i \in Nat,\; y\left(N + i\right) = 0\right) \lor \left(\forall i \in Nat,\; i \le N \Rightarrow y\left(N - i\right) = 0\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/Result.IsLogConcave` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Definition 1.1, page 2: Let $\{f_{k}\}_{k=0}^{\infty}$ be a non-negative nontrivial real sequence. We call $\{f_{k}\}_{k=0}^{\infty}$ log-concave (or Pólya frequency two – $PF_{2}$, or doubly positive) if $f_{k}^{2} \ge f_{k - 1}f_{k + 1}$ for each $k\in \mathbb{N}$, and $\{f_{k}\}_{k=0}^{\infty}$ is supported on an interval of integers (i.e., $f_{N} = 0$ implies either $f_{N + i} = 0$ for all $i\in \mathbb{N}_{0}$ or $f_{N - i} = 0$ for $i=0,...,N$).

The Lean predicate retains all four conditions: nonnegativity at every natural index, an index with nonzero value, the adjacent-product inequality for k ≥ 1, and the stated disjunction for every zero entry. Natural subtraction is used only with the stated bounds.

**Definition 1.2 (Finite Cauchy coefficient).**

$$\forall y \in Nat \to Real,\; \forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; \operatorname{delta}\left(y, mu, alpha, beta, m\right) = \sum _{k \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} (y\left(k\right) \cdot y\left(m - k\right) \cdot \left(\operatorname{c}\left(k, mu + alpha\right) \cdot \operatorname{c}\left(m - k, mu + beta\right) - \operatorname{c}\left(k, mu\right) \cdot \operatorname{c}\left(m - k, mu + alpha + beta\right)\right))$$

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/Result.delta` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For a real sequence y, real mu, alpha, beta and natural m, delta(y,mu,alpha,beta,m) is the sum over k=0,...,m of y(k)y(m-k) times [c(k,mu+alpha)c(m-k,mu+beta)-c(k,mu)c(m-k,mu+alpha+beta)]. It is exactly the degree-m coefficient of the difference of the two formal Cauchy products of the reciprocal series. No analytic convergence hypothesis is imposed.

**Definition 1.3 (Initial value and successive increments).**

$$\forall W \in Nat \to Real,\; \forall q \in Nat,\; \operatorname{increment}\left(W, q\right) = (\operatorname{if} q = 0 \operatorname{then} W\left(0\right) \operatorname{else} W\left(q\right) - W\left(q - 1\right))$$

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/Result.increment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

At q=0 the increment is W(0); at a positive natural index it is W(q)-W(q-1). Telescoping these increments recovers W at the last index.

**Theorem 1.4 (Reindexing a symmetric tail).**

$$\forall K \in Nat \to Real,\; \forall m \in Nat,\; \forall q \in Nat,\; 2 \cdot q \le m \Rightarrow \sum _{k \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} ((\operatorname{if} q \le k \land q \le m - k \operatorname{then} K\left(k\right) \operatorname{else} 0)) = \sum _{i \in \operatorname{Finset}.\operatorname{range}\left(m - q - q + 1\right)} (K\left(q + i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangReciprocal/Result.tail_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

When 2q ≤ m, the indices satisfying q ≤ k and q ≤ m-k are exactly q+i with 0 ≤ i < m-q-q+1. Natural subtraction is used with these bounds.

**Theorem 1.5 (Abel decomposition into symmetric layers).**

$$\forall y \in Nat \to Real,\; \forall K \in Nat \to Real,\; \forall m \in Nat,\; \sum _{k \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} (y\left(k\right) \cdot y\left(m - k\right) \cdot K\left(k\right)) = \sum _{q \in \operatorname{Finset}.\operatorname{range}\left(\operatorname{Nat}.\operatorname{div}\left(m, 2\right) + 1\right)} (\operatorname{increment}\left((i: Nat \mapsto y\left(i\right) \cdot y\left(m - i\right)), q\right) \cdot (\sum _{i \in \operatorname{Finset}.\operatorname{range}\left(m - q - q + 1\right)} (K\left(q + i\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangReciprocal/Result.abel_layers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For arbitrary real sequences y and K, telescoping the balanced products y(i)y(m-i) and interchanging the finite sums expresses their weighted sum as increments times symmetric tails. No positivity hypothesis is needed; the even middle index is counted once.

**Theorem 1.6 (Balancing one pair of indices).**

$$\forall y \in Nat \to Real,\; \operatorname{IsLogConcave}\left(y\right) \Rightarrow \left(\forall m \in Nat,\; \forall k \in Nat,\; k < \operatorname{Nat}.\operatorname{div}\left(m, 2\right) \Rightarrow y\left(k\right) \cdot y\left(m - k\right) \le y\left(k + 1\right) \cdot y\left(m - \left(k + 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangReciprocal/Result.balanced_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every real sequence y satisfying IsLogConcave, natural m and natural k strictly less than floor(m/2), y(k)y(m-k) <= y(k+1)y(m-(k+1)). The interval-support condition justifies the distant ratio comparison when the endpoint product is positive; a zero endpoint product is handled by nonnegativity.

**Theorem 1.7 (Abel summation identity).**

$$\forall y \in Nat \to Real,\; \forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; \operatorname{delta}\left(y, mu, alpha, beta, m\right) = y\left(0\right) \cdot y\left(m\right) \cdot \left(\operatorname{F}\left(m, 0, m, mu + alpha, mu + beta\right) - \operatorname{F}\left(m, 0, m, mu, mu + alpha + beta\right)\right) + \sum _{q \in \operatorname{Finset}.\operatorname{range}\left(\operatorname{Nat}.\operatorname{div}\left(m, 2\right)\right)} (\left(y\left(q + 1\right) \cdot y\left(m - \left(q + 1\right)\right) - y\left(q\right) \cdot y\left(m - q\right)\right) \cdot \left(\operatorname{F}\left(m, q + 1, m - \left(q + 1\right), mu + alpha, mu + beta\right) - \operatorname{F}\left(m, q + 1, m - \left(q + 1\right), mu, mu + alpha + beta\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangReciprocal/Result.abel_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every real sequence y, real mu, alpha, beta and natural m, put h=floor(m/2), W(q)=y(q)y(m-q), and T(q)=F(m,q,m-q,mu+alpha,mu+beta)-F(m,q,m-q,mu,mu+alpha+beta). Then delta=W(0)T(0)+sum over q=0,...,h-1 of [W(q+1)-W(q)]T(q+1). The identity holds without positivity assumptions. The even central index is counted once, because each T is an unpaired interval sum.

**Theorem 1.8 (All coefficients are nonnegative).**

$$\forall y \in Nat \to Real,\; \operatorname{IsLogConcave}\left(y\right) \Rightarrow \left(\forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; 0 < mu \Rightarrow \left(0 \le alpha \Rightarrow \left(0 \le beta \Rightarrow \left(\forall m \in Nat,\; 0 \le \operatorname{delta}\left(y, mu, alpha, beta, m\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangReciprocal/Result.reciprocal_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every sequence y satisfying IsLogConcave, positive real mu, nonnegative real alpha and beta, and every natural m, 0 <= delta(y,mu,alpha,beta,m). This proves the reciprocal-Pochhammer assertion of Conjecture 5.2 on page 12 under exactly the sequence convention of Definition 1.1. It does not assert the corresponding gamma-series half.

The interval-support condition forces every entry between two positive entries to be positive. Divide the adjacent log-concavity inequalities only on such positive intervals and induct to compare distant successive ratios. Consequently W(q+1) >= W(q) below the middle; if W(q)=0, nonnegativity gives the same conclusion directly. Telescoping the increments of W expresses W(min(k,m-k)) as a sum of layers. Interchanging two finite sums turns each layer into a symmetric tail and proves the Abel identity. The interval-convolution balancing theorem makes each tail nonnegative, and every Abel weight is nonnegative. Thus each formal coefficient is nonnegative independently of growth or convergence of the infinite series.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/Result.IsLogConcave`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/Result.abel_layers`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/Result.abel_reduction`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/Result.balanced_step`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/Result.delta`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/Result.increment`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/Result.reciprocal_half`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/Result.tail_sum`
- Dependency: [D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution](IntervalConvolution.md)
