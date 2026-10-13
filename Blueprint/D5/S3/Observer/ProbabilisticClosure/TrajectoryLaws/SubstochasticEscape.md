# Strict substochastic escape and nonsingularity

## Abstract

SubstochasticEscape

A real nonnegative matrix has row sums at most one. A common positive power has every row sum bounded by a real constant strictly below one. Monotonicity of row sums and the block estimate make every matrix-power entry tend to zero. A vector fixed by the matrix is fixed by every power, so the kernel of I minus the matrix is zero. No irreducibility or integer invertibility is used.

The statements and proof bodies are the live dependency slice of EAB.Paper.Chain.IsSubstochastic.det_one_sub_ne_zero, from YuZh98/aldous-broder-lean at bd20382923d987fc54a9773e04a4bc22b851872c. The source EAB/Paper/ConfinedChain.lean has SHA256 d235b9788731933c6f9b315b164ed71859748ca44658eef3cf033acfefbb8fba. Copyright 2026 Hugh Zheng; the full Apache 2.0 licence and original notice are in docs/reports/licenses/aldous-broder-substochastic.md.

The supplier pins Lean 4.30.0 and Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f; the repository pins Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The owning namespace and imports are adapted. MatrixFoundation is omitted because this slice consumes no declarations from it; Matrix.pow_apply_nonneg is supplied directly by Mathlib.Data.Matrix.Mul. SpecificLimits.Basic, Matrix.ToLinearEquiv and Topology.Instances.Matrix supply the other live dependencies. No statement type or proof body is adapted.

The unused rowSum_le_one leaf and the entire Neumann series, scaling/positive determinant, irreducible and confined-chain development are omitted. Every retained helper is consumed by the next row-sum or convergence proof, and det_one_sub_ne_zero is consumed by FiniteFairBitDenominator.det_ne_zero. Retire this port when this repository's pinned Mathlib contains equivalent declarations and replace the live applications by direct reuse.

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
