# Finite Partition Cell Measure

## Abstract

A nonempty finite measurable partition of a probability space has a cell whose measure is at least the uniform share.

**Theorem 1.1 (A finite partition has a cell of at least uniform measure).**

$$\forall mu, cell,\ \operatorname{ProbabilityMeasure}(mu), \operatorname{FiniteMeasurablePartition}(cell),\ \exists i, mu(cell(i))\ge reciprocal(card(I)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/FinitePartitionCellMeasure.exists_cell_measure_ge_reciprocal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite nonempty index type, let the measurable cells be pairwise disjoint and cover the whole carrier. Under a probability measure, at least one cell has measure no smaller than the reciprocal of the number of cells.

Mathlib's measure_iUnion identifies the total cell measure with one, and ENNReal.exists_le_of_sum_le supplies the finite averaging step. The Lean declaration only composes these library results.

This is a partial closure of the finite-codebook partition clause of source theorem 9.1. The construction of a naming system, countability and height claims, partial decoding, uncountability of positive-measure cells, nullity of representative points, and rate-distortion lower bound remain unresolved.

## References

- Truth anchor: `D5/S0/Asymptotics/FinitePartitionCellMeasure.exists_cell_measure_ge_reciprocal`
