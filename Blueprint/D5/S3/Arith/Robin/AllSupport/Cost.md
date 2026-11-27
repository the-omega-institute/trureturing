# Robin margin for arbitrary prime support

## Abstract

An exact decomposition of the Robin margin for arbitrary prime support.

**Theorem 1.1 (Exact prime-cost and correction identity).**

Lean statement: `D5/S3/Arith/Robin/AllSupport/Cost.robin_margin_eq_all_support_ledger`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/AllSupport/Cost.robin_margin_eq_all_support_ledger` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive integer n with log n at least 2, the Robin log margin is the sum of the prime cost at log n, the signed theta tail and three nonnegative corrections. The valuation defect uses the union of the occupied primes and the primes up to log n. A missing prime has valuation zero, so it can still supply a positive contribution to the cost. The other terms account for the logarithmic remainder and omitted Euler factors.

**Theorem 1.2 (A lower bound for the Robin margin).**

Lean statement: `D5/S3/Arith/Robin/AllSupport/Cost.robin_margin_ge_prime_cost_add_theta_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/AllSupport/Cost.robin_margin_ge_prime_cost_add_theta_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prime cost and signed theta tail give a lower bound for the log margin at the literal height log n. The bound applies to every integer in the stated range, including supports with gaps.

## References

- Truth anchor: `D5/S3/Arith/Robin/AllSupport/Cost.robin_margin_eq_all_support_ledger`
- Truth anchor: `D5/S3/Arith/Robin/AllSupport/Cost.robin_margin_ge_prime_cost_add_theta_tail`
- Dependency: [D5/S3/Arith/Robin/OriginalEndpointPrimeTail](../OriginalEndpointPrimeTail.md)
- Dependency: [D5/S3/Arith/Robin/ThetaTailRobinWitness](../ThetaTailRobinWitness.md)
