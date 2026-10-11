# Actual Robin Maxima on Forced Multiples

## Abstract

An actual GA2 witness yields an attained Robin maximum on every divisible forced base.

For positive integers n at least three, R(n) is the existing robinRatio(n) = sigma_1(n)/(exp(gamma)*n*log(log(n))). Thus G(n) = exp(gamma)*R(n), with gamma the Euler constant. The fixed positive scalar cancels from GA2, maximization, and the tail bound. C(q) denotes actualGA2(q). All logarithms are real natural logarithms.

**Definition 1.1 (All positive multipliers).**

$$\forall q \in \mathbb{N},\; C\left(q\right) \Leftrightarrow \left(3 \le q \land \left(\forall a \in \mathbb{N},\; 1 \le a \Rightarrow R\left(a \cdot q\right) \le R\left(q\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Robin/GA2ForcedPrimeSource.actualGA2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The condition includes q >= 3, so every tested integer aq has positive log(log(aq)). It compares the literal divisor-sum objective for every natural multiplier a >= 1.

**Theorem 1.2 (The lcm tail envelope).**

$$\forall q \in \mathbb{N},\; \forall n \in \mathbb{N},\; \left(C\left(q\right) \land 3 \le n\right) \Rightarrow R\left(n\right) \le R\left(q\right) \cdot \left(1 + \frac{\log\left(q\right)}{\log\left(n\right) \cdot \log\left(\log\left(n\right)\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GA2ForcedPrimeSource.robinRatio_le_ga2_tail_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any integer n >= 3 and actual GA2 integer q, the inequality holds even when n is not a multiple of q. Every denominator is positive.

Put L = lcm(q,n). The reciprocal divisor-sum identity from GoldenResourceOptimalInteger and inclusion of divisor sets give sigma_1(n)/n <= sigma_1(L)/L. Since q divides L, actual GA2 bounds R(L) by R(q). Finally L <= q*n, logarithmic monotonicity and log(1+t) <= t give the displayed explicit envelope. Its correction tends to zero as n tends to infinity with q fixed.

**Theorem 1.3 (Attainment on the entire multiples domain).**

$$\forall m \in \mathbb{N},\; \forall q \in \mathbb{N},\; \left(\left(3 \le m \land m \mid q\right) \land C\left(q\right)\right) \Rightarrow \left(\exists N \in \mathbb{N},\; \left(\left(\left(m \le N \land m \mid N\right) \land R\left(q\right) \le R\left(N\right)\right) \land C\left(N\right)\right) \land \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(m \mid n \Rightarrow R\left(n\right) \le R\left(N\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GA2ForcedPrimeSource.exists_robin_maximizer_multiple_of_ga2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The base m is any natural integer at least three. It divides the supplied actual GA2 integer q. There exists N >= m divisible by m, with R(N) >= R(q), itself actual GA2, and maximizing R over every positive multiple of m.

If no multiple improves q, choose q. Otherwise a strictly better multiple and the explicit vanishing envelope bound all sufficiently large integers strictly below that witness. A finite maximum below this derived cutoff is then a maximum on the entire infinite domain. Every positive multiple of N remains a multiple of m, giving actual GA2(N). All maximizing ties are allowed. The fixed-price maximum in GoldenFutureExtensionMaximum concerns a different objective.

This proves actual attainment without assuming an unbounded GA2 supplier, RH failure, or an analytic prime estimate. The subsequent own-price insertion and permitted deletion thresholds, lcm inventory characterization, forced 5040p singleton accounting and uniform activation-loss estimate remain separate obligations. The exact finite lcm comparison must retain its same-integer terminal clock and all defect terms. The same-source signed Tpsi lower budget and formal U/GM suppliers are unresolved; the full RH/Robin/5040 inequality remains unproved.

The completed ordinary audit is a design input, not a fresh adjudication of this implementation. The mathematical module and its retained Reg mirror have passed scoped Lean compilation using only propext, Classical.choice and Quot.sound. The Reg mirror supplies the complete law equivalence, variation, whole-family sensitivity and observational dependence proofs. Raw source-occurrence binding is explicitly unfinished; no declared_validated registration is claimed. These checks cover this increment and its imports, not the whole repository or the full RH goal.

## References

- Truth anchor: `D5/S3/Arith/Robin/GA2ForcedPrimeSource.actualGA2`
- Truth anchor: `D5/S3/Arith/Robin/GA2ForcedPrimeSource.exists_robin_maximizer_multiple_of_ga2`
- Truth anchor: `D5/S3/Arith/Robin/GA2ForcedPrimeSource.robinRatio_le_ga2_tail_envelope`
- Dependency: [D5/S3/Arith/GoldenResourceOptimalInteger](../GoldenResourceOptimalInteger.md)
- Dependency: [D5/S3/Arith/Robin/PaddingRatio](PaddingRatio.md)
