# Divisor Count and Sum Bounds

## Abstract

Uniform fourth-power estimates for the divisor count and divisor sum.

These estimates hold for every natural number, including zero. They supply the analytic premises for the bound on positive solutions of Ivan N. Ianakiev's equality conjecture in OEIS A336687.

**Theorem 1.1 (Uniform divisor-count bound).**

$$\forall n \in \mathbb{N}, \operatorname{tau}(n)^{4} \le 9^{4} \cdot n$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/TauSigmaPowerBounds.tau_pow_four_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan N. Ianakiev; Bernard Schott (2020). *OEIS A336687, divisor compositions and a three-solution equality conjecture*. URL: <https://oeis.org/A336687>.

*Commentary.*

On prime powers, the consecutive quotient decreases after a finite initial segment. The six exceptional prime costs have product 127401984/25025, less than 9^4. Multiplying over the distinct prime factors proves tau(n)^4 <= 9^4*n.

**Theorem 1.2 (Uniform divisor-sum bound).**

$$\forall n \in \mathbb{N}, \operatorname{sigma}(n)^{4} \le 3 \cdot n^{5}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/TauSigmaPowerBounds.sigma_pow_four_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan N. Ianakiev; Bernard Schott (2020). *OEIS A336687, divisor compositions and a three-solution equality conjecture*. URL: <https://oeis.org/A336687>.

*Commentary.*

The prime-power geometric sums have exceptional costs 81/32 at two and 256/243 at three. All primes at least five have cost one. Their product is 8/3, less than three. This proves sigma(n)^4 <= 3*n^5 by multiplicativity.

## References

- Truth anchor: `D5/S3/Factorization/TauSigmaPowerBounds.sigma_pow_four_le`
- Truth anchor: `D5/S3/Factorization/TauSigmaPowerBounds.tau_pow_four_le`
