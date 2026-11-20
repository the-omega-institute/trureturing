# Calibrating probability grids by scaled block allocations

## Abstract

Equivariant readout from scaled allocations on profile stabilizer blocks.

**Theorem 1.1 (A calibrating law from scaled common block allocations).**

$$\forall k m n c w, 2 \le k \land 0 < m \land 0 < c \land \operatorname{Divides}\left((k-1), m\right) \land k\cdot(k-1)\cdot\operatorname{TotalWeight}\left(w\right) = c\cdot m \land \operatorname{ScaledBlockCover}\left(k, m, n, c, w\right) \Rightarrow \operatorname{SeedBudget}\left(k, m, \operatorname{factorial}\left(k\right)\cdot n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/GridReadoutConstruction.law_of_scaled_block_allocations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be the number of labels, m the denominator, n the number of proposed regular seed orbits, and c a positive integer scale. The nonnegative integer orbit weights w have total c times m divided by k times (k minus one). ScaledBlockCover means the following. For every positive number of groups t, block count U at least k times (t minus one), and natural demands x whose sum times k times (k minus one) equals U times m, there is a common allocation. It assigns U blocks per orbit and gives each group weighted mass c times its demand.

For each profile, split the labels into equal-coordinate groups. The group demands are integral because k minus one divides m. Use the allocations to construct a readout on its stabilizer blocks and transport the readout from one representative per profile orbit. Remove the zero-weight orbits and normalize the remaining mass to obtain a shared calibrating law.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/GridReadoutConstruction.law_of_scaled_block_allocations`
- Dependency: [D5/S3/Combinatorics/Partitions/CommonBlockWeights](../../Combinatorics/Partitions/CommonBlockWeights.md)
- Dependency: [D5/S3/Combinatorics/Partitions/StabilizerFactorialDivisibility](../../Combinatorics/Partitions/StabilizerFactorialDivisibility.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/PrimeCycleSeedFreeness](PrimeCycleSeedFreeness.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ThreeOutcomeGridSupport](ThreeOutcomeGridSupport.md)
