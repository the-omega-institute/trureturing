# Positive Energy Partition Coordinates

## Abstract

Pure positive-energy coordinates and their ordinary partition equivalence.

This common G dependency contains the pure finite-support positive-energy coordinate construction reused by the ordinary coloured occupation bridge and by the concrete polynomial Fock consumers. The public declaration namespaces remain those of the original consumers.

**Definition 1.1 (Positive weighted energy).**

Lean statement: `D5/S3/Combinatorics/Partitions/PositiveEnergyPartition.energy`

*Formalization.* `D5/S3/Combinatorics/Partitions/PositiveEnergyPartition.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An exponent vector assigns the positive weight i + 1 to the variable indexed by i.

**Definition 1.2 (Fixed positive-energy exponent fibres).**

Lean statement: `D5/S3/Combinatorics/Partitions/PositiveEnergyPartition.EnergyFiber`

*Formalization.* `D5/S3/Combinatorics/Partitions/PositiveEnergyPartition.EnergyFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

EnergyFiber N is the subtype of finitely supported natural exponent vectors whose positive weighted energy is N, including the zero-energy fibre.

**Theorem 1.3 (Positive-energy fibres are ordinary integer partitions).**

Lean statement: `D5/S3/Combinatorics/Partitions/PositiveEnergyPartition.energyFiberEquivPartition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/PositiveEnergyPartition.energyFiberEquivPartition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N, the positive weighted exponent vectors are equivalent to Nat.Partition N. The forward map repeats i + 1 according to the exponent at i, and predecessor decoding is inverse on positive partition parts.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/PositiveEnergyPartition.EnergyFiber`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PositiveEnergyPartition.energy`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PositiveEnergyPartition.energyFiberEquivPartition`
