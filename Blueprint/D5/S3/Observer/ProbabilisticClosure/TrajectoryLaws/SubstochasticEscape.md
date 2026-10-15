# Strict substochastic escape and nonsingularity

## Abstract

SubstochasticEscape

A real nonnegative matrix has row sums at most one. A common positive power has every row sum bounded by a real constant strictly below one. Monotonicity of row sums and the block estimate make every matrix-power entry tend to zero. A vector fixed by the matrix is fixed by every power, so the kernel of I minus the matrix is zero. No irreducibility or integer invertibility is used.

The rowSum function records the total mass remaining after a fixed number of transitions. Nonnegative powers allow each entry to be bounded by its row sum. Splitting a power into two blocks gives a row-sum bound by the product of the earlier row sum and a uniform bound on the later block.

Substochasticity makes each row sum nonincreasing in time. If every row loses a uniform positive amount of mass after N transitions, with N positive, repeated N-step blocks give a geometric upper bound. Division by N extends this bound to arbitrary times and forces each power entry to converge to zero.

If I minus the matrix were singular, a nonzero vector would be fixed by the matrix and hence by every matrix power. Entrywise convergence and finiteness of the carrier force the same vector to be zero, a contradiction. This nonsingularity result applies to the internal substochastic matrix in the finite fair-bit exit denominator argument.

**Theorem 1.1 (pow_nonneg).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.pow_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.pow_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled statement includes its complete displayed premises.

**Theorem 1.2 (rowSum_zero).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled statement includes its complete displayed premises.

**Theorem 1.3 (rowSum_one).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_one`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled statement includes its complete displayed premises.

**Theorem 1.4 (rowSum_add).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_add`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled statement includes its complete displayed premises.

**Theorem 1.5 (rowSum_nonneg).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled statement includes its complete displayed premises.

**Theorem 1.6 (entry_le_rowSum).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.entry_le_rowSum`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.entry_le_rowSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled statement includes its complete displayed premises.

**Theorem 1.7 (rowSum_add_le).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_add_le`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_add_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled statement includes its complete displayed premises.

**Theorem 1.8 (rowSum_succ_le).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_succ_le`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_succ_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled statement includes its complete displayed premises.

**Theorem 1.9 (rowSum_antitone).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled statement includes its complete displayed premises.

**Theorem 1.10 (rowSum_mul_le).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_mul_le`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_mul_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled statement includes its complete displayed premises.

**Theorem 1.11 (tendsto_pow_entry).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.tendsto_pow_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.tendsto_pow_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled statement includes its complete displayed premises.

**Theorem 1.12 (det_one_sub_ne_zero).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.det_one_sub_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.det_one_sub_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled statement includes its complete displayed premises.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.det_one_sub_ne_zero`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.entry_le_rowSum`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.pow_nonneg`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_add`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_add_le`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_antitone`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_mul_le`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_nonneg`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_one`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_succ_le`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_zero`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.tendsto_pow_entry`
