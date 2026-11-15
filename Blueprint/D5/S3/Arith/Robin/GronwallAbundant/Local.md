# Local

## Abstract

Prime-deletion constraints, missing-prime mass and finite-code entropy for proper GA1 integers.

The source defines composite GA1 integers by all prime-deletion comparisons of the Gronwall quotient. Properness means at least three prime factors with multiplicity. Its section 8 gives Q1(x) at most exp(c*log(x)/log(log(x))) for some positive c and asks for an improvement.

**Remark 1.1 (The counting estimate and improvement question in section eight).**

Lean statement: `D5/S3/Arith/Robin/GronwallAbundant/Local.Q1`

*Formalization.* `D5/S3/Arith/Robin/GronwallAbundant/Local.Q1` (`✓ std3`).

*Citation.* Geoffrey Caveney, Jean-Louis Nicolas, and Jonathan Sondow (2012). *On SA, CA, and GA numbers*. URL: <https://arxiv.org/abs/1112.6010v2>.

*Commentary.*

Section 8 states Q1(x) <= exp(c*log(x)/log(log(x))) for some positive c and suggests improving the estimate by counting good divisors. This cited estimate is distinct from the stronger upper bound proved here.

**Definition 1.2 (The Gronwall quotient with its unmodified natural-logarithm denominator.).**

$$\forall n: \mathbb{N}, \operatorname{G}\left(n\right) = \frac{\operatorname{sigma}\left(1, n\right)}{n \cdot \operatorname{log}\left(\operatorname{log}\left(n\right)\right)}$$

*Formalization.* `D5/S3/Arith/Robin/GronwallAbundant/Local.gronwallQ` (`✓ std3`).

*Citation.* Geoffrey Caveney, Jean-Louis Nicolas, and Jonathan Sondow (2012). *On SA, CA, and GA numbers*. URL: <https://arxiv.org/abs/1112.6010v2>.

*Commentary.*

The Gronwall quotient with its unmodified natural-logarithm denominator.

**Definition 1.3 (A composite integer whose Gronwall quotient does not increase on deleting a prime.).**

$$\forall N: \mathbb{N}, \operatorname{IsGAone}\left(N\right) \Leftrightarrow \left(\neg \operatorname{Prime}\left(N\right) \land \left(1 < N \land \forall p: \mathbb{N}, p \in \operatorname{primeFactors}\left(N\right) \Rightarrow \operatorname{G}\left(\operatorname{natdiv}\left(N, p\right)\right) \le \operatorname{G}\left(N\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Robin/GronwallAbundant/Local.IsGA1` (`✓ std3`).

*Citation.* Geoffrey Caveney, Jean-Louis Nicolas, and Jonathan Sondow (2012). *On SA, CA, and GA numbers*. URL: <https://arxiv.org/abs/1112.6010v2>.

*Commentary.*

A composite integer whose Gronwall quotient does not increase on deleting a prime.

**Definition 1.4 (Proper GA1 integers have at least three prime factors with multiplicity.).**

$$\forall N: \mathbb{N}, \operatorname{IsProperGAone}\left(N\right) \Leftrightarrow \left(\operatorname{IsGAone}\left(N\right) \land 3 \le \operatorname{Omega}\left(N\right)\right)$$

*Formalization.* `D5/S3/Arith/Robin/GronwallAbundant/Local.IsProperGA1` (`✓ std3`).

*Citation.* Geoffrey Caveney, Jean-Louis Nicolas, and Jonathan Sondow (2012). *On SA, CA, and GA numbers*. URL: <https://arxiv.org/abs/1112.6010v2>.

*Commentary.*

Proper GA1 integers have at least three prime factors with multiplicity.

**Definition 1.5 (The number of proper GA1 integers at most a real cutoff.).**

$$\forall x: \mathbb{R}, \left(Q_{1}\right)\left(x\right) = \operatorname{card}\left(\operatorname{filter}\left(\operatorname{IsProperGAone}, \operatorname{range}\left(\operatorname{floorpos}\left(x\right) + 1\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Robin/GronwallAbundant/Local.Q1` (`✓ std3`).

*Citation.* Geoffrey Caveney, Jean-Louis Nicolas, and Jonathan Sondow (2012). *On SA, CA, and GA numbers*. URL: <https://arxiv.org/abs/1112.6010v2>.

*Commentary.*

The number of proper GA1 integers at most a real cutoff.

**Theorem 1.6 (Deleting a prime from a proper GA1 integer leaves an integer at least four.).**

Lean statement: `D5/S3/Arith/Robin/GronwallAbundant/Local.proper_div_ge_four`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GronwallAbundant/Local.proper_div_ge_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Deleting a prime from a proper GA1 integer leaves an integer at least four.

**Theorem 1.7 (The iterated logarithm after deleting a prime from a proper GA1 integer is positive.).**

Lean statement: `D5/S3/Arith/Robin/GronwallAbundant/Local.proper_loglog_div_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GronwallAbundant/Local.proper_loglog_div_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The iterated logarithm after deleting a prime from a proper GA1 integer is positive.

**Definition 1.8 (The finite geometric sum attached to the complete exponent of a prime.).**

Lean statement: `D5/S3/Arith/Robin/GronwallAbundant/Local.primeDeletionSum`

*Formalization.* `D5/S3/Arith/Robin/GronwallAbundant/Local.primeDeletionSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite geometric sum attached to the complete exponent of a prime.

**Theorem 1.9 (The exact local comparison before changing logarithmic coordinates.).**

Lean statement: `D5/S3/Arith/Robin/GronwallAbundant/Local.ga1_local_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GronwallAbundant/Local.ga1_local_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact local comparison before changing logarithmic coordinates.

**Theorem 1.10 (Concavity of the logarithm charges deletion by at least its relative log-size.).**

Lean statement: `D5/S3/Arith/Robin/GronwallAbundant/Local.prime_deletion_log_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GronwallAbundant/Local.prime_deletion_log_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Concavity of the logarithm charges deletion by at least its relative log-size.

**Theorem 1.11 (The GA1 comparison bounds every full local geometric sum.).**

Lean statement: `D5/S3/Arith/Robin/GronwallAbundant/Local.ga1_prime_power_log_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GronwallAbundant/Local.ga1_prime_power_log_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The GA1 comparison bounds every full local geometric sum.

**Theorem 1.12 (Every prime-power divisor obeys the GA1 logarithmic barrier.).**

Lean statement: `D5/S3/Arith/Robin/GronwallAbundant/Local.ga1_prime_power_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GronwallAbundant/Local.ga1_prime_power_le` (`✓ std3`). ∎

*Citation.* Geoffrey Caveney, Jean-Louis Nicolas, and Jonathan Sondow (2012). *On SA, CA, and GA numbers*. URL: <https://arxiv.org/abs/1112.6010v2>.

*Commentary.*

CNS Theorem 9, section 6.1, printed pages 20-21: Every prime-power divisor obeys the GA1 logarithmic barrier.

**Theorem 1.13 (Every prime factor is at most the natural logarithm of a proper GA1 integer.).**

Lean statement: `D5/S3/Arith/Robin/GronwallAbundant/Local.prime_le_log`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GronwallAbundant/Local.prime_le_log` (`✓ std3`). ∎

*Citation.* Geoffrey Caveney, Jean-Louis Nicolas, and Jonathan Sondow (2012). *On SA, CA, and GA numbers*. URL: <https://arxiv.org/abs/1112.6010v2>.

*Commentary.*

CNS Theorem 9, section 6.1, printed pages 20-21: Every prime factor is at most the natural logarithm of a proper GA1 integer.

**Theorem 1.14 (Repeated prime factors lie below the square-root cutoff.).**

Lean statement: `D5/S3/Arith/Robin/GronwallAbundant/Local.square_le_two_log`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GronwallAbundant/Local.square_le_two_log` (`✓ std3`). ∎

*Citation.* Geoffrey Caveney, Jean-Louis Nicolas, and Jonathan Sondow (2012). *On SA, CA, and GA numbers*. URL: <https://arxiv.org/abs/1112.6010v2>.

*Commentary.*

CNS Theorem 9, section 6.1, printed pages 20-21: Repeated prime factors lie below the square-root cutoff.

**Theorem 1.15 (A proper GA1 integer has logarithm strictly greater than two.).**

Lean statement: `D5/S3/Arith/Robin/GronwallAbundant/Local.proper_log_gt_two`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GronwallAbundant/Local.proper_log_gt_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A proper GA1 integer has logarithm strictly greater than two.

**Theorem 1.16 (The non-strict logarithmic threshold used in common GA1 budgets.).**

Lean statement: `D5/S3/Arith/Robin/GronwallAbundant/Local.proper_log_ge_two`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GronwallAbundant/Local.proper_log_ge_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The non-strict logarithmic threshold used in common GA1 budgets.

## References

- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Local.IsGA1`
- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Local.IsProperGA1`
- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Local.Q1`
- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Local.Q1`
- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Local.ga1_local_criterion`
- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Local.ga1_prime_power_le`
- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Local.ga1_prime_power_log_bound`
- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Local.gronwallQ`
- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Local.primeDeletionSum`
- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Local.prime_deletion_log_gap`
- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Local.prime_le_log`
- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Local.proper_div_ge_four`
- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Local.proper_log_ge_two`
- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Local.proper_log_gt_two`
- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Local.proper_loglog_div_pos`
- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Local.square_le_two_log`
- Dependency: [D5/S3/Arith/Robin/PrimeFiberPropagation](../PrimeFiberPropagation.md)
