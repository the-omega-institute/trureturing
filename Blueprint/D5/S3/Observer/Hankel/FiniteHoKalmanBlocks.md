# Finite Ho-Kalman Data Blocks

## Abstract

Finite Markov samples, explicit block inversion, and all-time exact reconstruction.

**Definition 1.1 (Finite sample array).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.Samples`

*Formalization.* `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.Samples` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input contains exactly 2h Markov matrices. The convention is m(k)=C A^k B; a direct-feedthrough term is outside this array.

**Definition 1.2 (Selected observation and reachability indices).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.Pivot`

*Formalization.* `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.Pivot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A pivot chooses r time/output rows and r time/input columns. Nonsingularity, when required, excludes repetitions automatically.

**Definition 1.3 (Unshifted Hankel minor).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.baseBlock`

*Formalization.* `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.baseBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every access is an index into the finite input array, with a proved bound.

**Definition 1.4 (One-step shifted minor).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.shiftBlock`

*Formalization.* `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.shiftBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shift uses the same selected rows and columns and one additional time step.

**Definition 1.5 (Input data block).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.inputBlock`

*Formalization.* `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.inputBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All input coordinates are retained at the selected observation rows.

**Definition 1.6 (Output data block).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.outputBlock`

*Formalization.* `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.outputBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All output coordinates are retained at the selected reachability columns.

**Definition 1.7 (Explicit adjugate inverse).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.adjInverse`

*Formalization.* `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.adjInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse candidate is computed from the determinant and adjugate. Its correctness requires a nonzero determinant, which the executable search checks.

**Theorem 1.8 (Left inverse correctness).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.adjInverse_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.adjInverse_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's adjugate identity proves that the computed candidate is a left inverse.

**Theorem 1.9 (Right inverse correctness).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.mul_adjInverse`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.mul_adjInverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second adjugate identity proves the right inverse equation.

**Definition 1.10 (Computed state transition).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.fittedA`

*Formalization.* `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.fittedA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transition is the computed inverse times the shifted data block.

**Definition 1.11 (Computed input map).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.fittedB`

*Formalization.* `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.fittedB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input map is the computed inverse times the input data block.

**Definition 1.12 (Computed output map).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.fittedC`

*Formalization.* `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.fittedC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The output data block directly gives the output map in the selected reachable coordinates.

**Definition 1.13 (Selected observation matrix).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.selectedO`

*Formalization.* `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.selectedO` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This reference-system matrix is used only in the correctness proof. It is not an input to the reconstruction.

**Definition 1.14 (Selected reachability matrix).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.selectedR`

*Formalization.* `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.selectedR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Its columns define the recovered state coordinates. The algorithm does not need to know the reference system.

**Theorem 1.15 (Data semantics imply four factorizations).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.sample_factorizations`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.sample_factorizations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four block equations follow from finite Markov-parameter equality by matrix multiplication and addition of time exponents.

**Theorem 1.16 (Finite factors imply all-time reproduction).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.factorized_exact_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.factorized_exact_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A computed inverse supplies two-sided coordinate maps. An induction transports every matrix power, including systems with Jordan blocks.

**Theorem 1.17 (Exact finite-sample reconstruction theorem).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.finite_samples_exact_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.finite_samples_exact_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any order-r reference realization matching the finite samples and giving a nonsingular selected minor has exactly the computed all-time behavior. The reference dimension is an explicit model-class hypothesis, not inferred from arbitrary finite data.

**Theorem 1.18 (Minimum state-order certificate).**

Lean statement: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.finite_samples_order_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.finite_samples_order_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonsingular r-by-r data minor forces every finite-dimensional realization matching those samples to have dimension at least r. This reuses Mathlib matrix-rank inequalities and allows the comparison dimension to differ from r.

## References

- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.Pivot`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.Samples`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.adjInverse`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.adjInverse_mul`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.baseBlock`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.factorized_exact_recovery`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.finite_samples_exact_recovery`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.finite_samples_order_lower_bound`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.fittedA`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.fittedB`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.fittedC`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.inputBlock`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.mul_adjInverse`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.outputBlock`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.sample_factorizations`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.selectedO`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.selectedR`
- Truth anchor: `D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.shiftBlock`
