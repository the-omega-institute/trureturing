# Positive-seed k-bonacci shifts

## Abstract

Positive-seed k-bonacci shifts

These historical proof bodies apply the Ma-Zhang backward-zero mechanism, deriving the negative zero from the recurrence. The order-three and order-four scalar seeds motivate the result. The all-order normalized impulse block theorem remains a separate obligation.

**Theorem 1.1 (adjacent_doubling_no_repair).**

Lean statement: `D5/S3/Arith/LocalDold/KBonacciShifts.adjacent_doubling_no_repair`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/KBonacciShifts.adjacent_doubling_no_repair` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Scalar local-Dold criterion and backward-zero obstruction (communicated notes)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For a bilateral integer order n+1 k-bonacci recurrence with every positive seed through n+1 positive, an adjacent doubling at 0<i<n+1 forces a strictly negative-time zero. At every prime and every nonnegative shift there is no fixed positive local-Dold repair. The proof constructs the integral invertible companion action and proves positivity from the actual seeds.

**Theorem 1.2 (one_two_seeds_no_repair).**

Lean statement: `D5/S3/Arith/LocalDold/KBonacciShifts.one_two_seeds_no_repair`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/KBonacciShifts.one_two_seeds_no_repair` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Scalar local-Dold criterion and backward-zero obstruction (communicated notes)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For k>=3, a bilateral integer k-bonacci recurrence with a(1)=...=a(k-1)=1 and a(k)=2 has no positive local-Dold repair at any prime and any nonnegative shift. The positive-seed hypothesis is not the normalized impulse block initial condition.

## References

- Truth anchor: `D5/S3/Arith/LocalDold/KBonacciShifts.adjacent_doubling_no_repair`
- Truth anchor: `D5/S3/Arith/LocalDold/KBonacciShifts.one_two_seeds_no_repair`
- Dependency: [D5/S3/Arith/LocalDold/BackwardZero](BackwardZero.md)
