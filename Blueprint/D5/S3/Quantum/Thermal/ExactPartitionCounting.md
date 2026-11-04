# ExactPartitionCounting

## Abstract

Explicit ExactPartitionCounting constructions. The linked declarations do not certify unproved analytic or quantum extensions.

**Theorem 1.1 (exact cnf counting recovery).**

Lean statement: `D5/S3/Quantum/Thermal/ExactPartitionCounting.exact_cnf_counting_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ExactPartitionCounting.exact_cnf_counting_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input is a CNF syntax tree. Assignments, clause evaluation, violations, the rational Gibbs partition, and the extra visible bit are constructed. Taking the floor after multiplying the total partition by two thirds returns the satisfying-assignment count.

**Theorem 1.2 (clause three local).**

Lean statement: `D5/S3/Quantum/Thermal/ExactPartitionCounting.clause_three_local`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ExactPartitionCounting.clause_three_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A clause of length at most three depends only on its explicit support, whose cardinality is at most three. Repeated literals and empty clauses are allowed.

**Theorem 1.3 (clauseProjector idempotent).**

Lean statement: `D5/S3/Quantum/Thermal/ExactPartitionCounting.clauseProjector_idempotent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ExactPartitionCounting.clauseProjector_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal 0/1 violation operator is a projection in the rational matrix algebra.

**Theorem 1.4 (clauseProjectors commute).**

Lean statement: `D5/S3/Quantum/Thermal/ExactPartitionCounting.clauseProjectors_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ExactPartitionCounting.clauseProjectors_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicitly defined clause projections commute; no commutativity certificate is assumed.

**Theorem 1.5 (common denominator).**

Lean statement: `D5/S3/Quantum/Thermal/ExactPartitionCounting.common_denominator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ExactPartitionCounting.common_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by two to the power (n+1) times the clause count yields the explicitly constructed natural numerator. This is an exact encoding identity, not a running-time or approximation-hardness theorem.

**Theorem 1.6 (boltzmann weight).**

Lean statement: `D5/S3/Quantum/Thermal/ExactPartitionCounting.boltzmann_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ExactPartitionCounting.boltzmann_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rational weight agrees with the actual real exponential at inverse temperature log 2 and energy (n+1) times the violation count.

**Theorem 1.7 (penalty sum).**

Lean statement: `D5/S3/Quantum/Thermal/ExactPartitionCounting.penalty_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ExactPartitionCounting.penalty_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The total diagonal penalty is the sum of the syntactically constructed individual clause penalties.

## References

- Truth anchor: `D5/S3/Quantum/Thermal/ExactPartitionCounting.boltzmann_weight`
- Truth anchor: `D5/S3/Quantum/Thermal/ExactPartitionCounting.clauseProjector_idempotent`
- Truth anchor: `D5/S3/Quantum/Thermal/ExactPartitionCounting.clauseProjectors_commute`
- Truth anchor: `D5/S3/Quantum/Thermal/ExactPartitionCounting.clause_three_local`
- Truth anchor: `D5/S3/Quantum/Thermal/ExactPartitionCounting.common_denominator`
- Truth anchor: `D5/S3/Quantum/Thermal/ExactPartitionCounting.exact_cnf_counting_recovery`
- Truth anchor: `D5/S3/Quantum/Thermal/ExactPartitionCounting.penalty_sum`
