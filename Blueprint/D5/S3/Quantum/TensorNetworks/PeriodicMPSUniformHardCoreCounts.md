# Cyclic insertions, hops and deletions

## Abstract

Move counts on independent configurations of a cycle

**Theorem 1.1 (Legal insertions).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts.insertion_count_balance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts.insertion_count_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a ring of length n ≥ 7, let r be the size of an independent set, d the number of occupied starts whose forward distance-two site is occupied, and a the number of legal insertions. Then a + 3r = n + d. Each cyclic triple contributes the insertion indicator at its middle site and the three occupancy indicators. An occupied pair of endpoints gives the extra contribution.

**Theorem 1.2 (Legal directed hops).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts.directed_hop_count`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts.directed_hop_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number h of actual ordered nearest-neighbor moves is 2r − 2d. Each occupied site offers two directions. An occupied pair at distance two blocks both moves into its middle site. Forward and backward triple windows enumerate the ordered moves, including those across the seam.

**Theorem 1.3 (Cancellation in the weighted row).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts.move_count_row_balance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts.move_count_row_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two triple counts give 2a + h + 4r = 2n. There are r legal deletions, so the combined weight of insertions, deletions and half-weight directed hops is a + r + h/2 = n − r.

**Theorem 1.4 (Deletion paths to the empty configuration).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts.deletion_reaches_empty`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts.deletion_reaches_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any cycle length, deleting an occupied site preserves independence and decreases cardinality by one. Induction on cardinality gives a path from each independent configuration to the empty configuration.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts.deletion_reaches_empty`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts.directed_hop_count`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts.insertion_count_balance`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts.move_count_row_balance`
