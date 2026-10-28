# Exact CNF Partition Counting

## Abstract

An explicit finite CNF penalty model gives an exact rational partition identity. The satisfying-assignment count is recovered by a floor operation, and the local clause penalties are commuting diagonal projections.

**Theorem 1.1 (Exact CNF counting recovery).**

For every finite CNF syntax tree, the constructed rational partition and visible factor recover the exact number of satisfying assignments by the stated floor identity.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ExactPartitionCounting.exact_cnf_counting_recovery` (`✓ std3`). ∎

**Theorem 1.2 (Three-local clause support).**

A clause of length at most three depends only on its explicit finite support, whose cardinality is at most three.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ExactPartitionCounting.clause_three_local` (`✓ std3`). ∎

**Theorem 1.3 (Clause projections).**

The diagonal violation operator of a clause is idempotent, and the operators for any two clauses commute.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ExactPartitionCounting.clauseProjector_idempotent` and `D5/S3/Quantum/Thermal/ExactPartitionCounting.clauseProjectors_commute` (`✓ std3`). ∎

**Theorem 1.4 (Common denominator).**

Multiplying the rational partition by the explicit power-of-two denominator yields the natural numerator constructed from the finite penalty data.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ExactPartitionCounting.common_denominator` (`✓ std3`). ∎

**Theorem 1.5 (Boltzmann and penalty identities).**

The rational clause weight is the corresponding inverse-temperature exponential, and the total penalty is the sum of the individual clause penalties.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ExactPartitionCounting.boltzmann_weight` and `D5/S3/Quantum/Thermal/ExactPartitionCounting.penalty_sum` (`✓ std3`). ∎

## References

- Truth anchors: the declarations listed in the theorem statements above.
