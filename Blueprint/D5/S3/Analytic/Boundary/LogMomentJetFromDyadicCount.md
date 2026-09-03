# Boundary Logarithmic Jets from Dyadic Counts

## Abstract

A logarithmic dyadic counting gain yields finite lower-order boundary log moments.

**Theorem 1.1 (A k-fold counting gain gives every log moment below k minus one).**

$$\begin{aligned}A \subseteq \{n \in \mathbb{N} \mid 2\le n\}, m,k \in \mathbb{N}, C \in \mathbb{R},\\0\le C, m+1< k,\\\forall j \in \mathbb{N}, S_{j}=\{n \in A \mid \operatorname{NatLog}_{2}(n)=j\}, \lvert S_{j}\rvert\le\frac{C 2^{j}}{(j+1)^{k}} \Rightarrow\\\sum_{n \in A}\frac{(\log(n))^{m}}{n} < \infty.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/LogMomentJetFromDyadicCount.summable_log_moment_of_dyadic_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A contain only natural numbers at least two. Its j-th shell S_j is the exact fiber on which the natural base-two logarithm equals j. If the shell cardinality is at most C 2^j/(j+1)^k, then every logarithmic boundary moment of integral order m with m+1<k is summable.

Inside shell j, 2^j <= n < 2^(j+1). Monotonicity and the power law for the real logarithm bound (log n)^m/n by (((j+1)log 2)^m)/2^j. Multiplying by the shell count cancels the exponential factor and m powers of j+1. Since k is at least m+2, the shell sum is bounded by a constant multiple of 1/(j+1)^2, a shifted p-series.

Mathlib's summable_partition then reassembles the exact shell fibers, and summable_subtype_iff_indicator returns the original series over A rather than merely a series of shell bounds. Exact shell coverage is an explicit hypothesis, so no elements of A can be omitted from the counting data.

The source uses a Vinogradov bound with a real exponent beta. The formal statement specializes it to the integer pattern exponent k used by the source's jet table and makes the hidden constant C explicit. Passing from the cumulative estimate N_A(x) << x/(log x)^k to the displayed dyadic estimate only changes C by fixed powers of 2 and log 2. The condition m<k-1 is written m+1<k to avoid truncated natural subtraction. The restriction n>=2 excludes Lean's totalized log-zero and division-by-zero branches; finitely many smaller indices do not affect convergence. No critical-order divergence or numerical pattern-count certificate is claimed.

Six duplicate routes were checked: Lean keywords; mathematical notation and naming variants; current accepted-event receipts; digestion backfill and digest text by source hash; generalized Abel-summation, partition, p-series, and smooth-series searches; and all in-flight math lanes. No equivalent D5 or pinned-Mathlib theorem was found. The exact upstream lemmas reused are summable_partition, summable_subtype_iff_indicator, Real.summable_nat_pow_inv, Nat.pow_log_le_self, Nat.lt_pow_succ_log_self, Real.log_le_log, and Real.log_pow. The legacy formalization-receipt directory is retired on the current branch.

## References

- Truth anchor: `D5/S3/Analytic/Boundary/LogMomentJetFromDyadicCount.summable_log_moment_of_dyadic_count`
