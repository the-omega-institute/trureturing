# Convergent Sequences of Finite Capacity States

## Abstract

Convergent Sequences of Finite Capacity States.

**Theorem 1.1 (Convergence is eventual equality).**

Lean statement: `D5/S3/Analytic/WeightedCapacity/ProbeTopologySequences.tendsto_tauPlus_iff_eventually_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WeightedCapacity/ProbeTopologySequences.tendsto_tauPlus_iff_eventually_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each coordinate has a finite natural capacity, and every state has finite support. Equip these states with the initial topology of their golden coordinate phases and all circle characters defined by total rational coefficient sequences. A sequence converges to a state exactly when it eventually equals that state. No bound on the number of active coordinates or on total weighted capacity is needed. Single coordinate characters force each coordinate to stabilize. If unequal terms persist, their signed differences admit a subsequence with separated finite supports. One rational coefficient sequence then evaluates to one half on every selected difference, contradicting convergence of its circle character.

## References

- Truth anchor: `D5/S3/Analytic/WeightedCapacity/ProbeTopologySequences.tendsto_tauPlus_iff_eventually_eq`
- Dependency: [D5/S3/Analytic/WeightedCapacity/DyadicTailFilling](DyadicTailFilling.md)
