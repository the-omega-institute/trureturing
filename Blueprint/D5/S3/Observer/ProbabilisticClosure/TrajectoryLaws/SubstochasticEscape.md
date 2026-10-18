# Strict substochastic escape, nonsingularity and the Neumann series

## Abstract

SubstochasticEscape

A real nonnegative matrix has row sums at most one. A common positive power has every row sum bounded by a real constant strictly below one. Monotonicity of row sums and the block estimate make every matrix-power entry tend to zero. A vector fixed by the matrix is fixed by every power, so the kernel of I minus the matrix is zero. The geometric finite-sum identity also gives the entrywise Neumann series: the powers sum to the inverse of I minus the matrix. No irreducibility or integer invertibility is used.

The statements and proof bodies are the substochastic escape and Neumann-series results in EAB.Paper.Chain, from YuZh98/aldous-broder-lean at bd20382923d987fc54a9773e04a4bc22b851872c. The source EAB/Paper/ConfinedChain.lean has SHA256 d235b9788731933c6f9b315b164ed71859748ca44658eef3cf033acfefbb8fba. Copyright 2026 Hugh Zheng; the full Apache 2.0 licence and original notice are in docs/reports/licenses/aldous-broder-substochastic.md.

The supplier pins Lean 4.30.0 and Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f; the repository pins Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The owning namespace and imports are adapted. MatrixFoundation is omitted because this slice consumes no declarations from it; Matrix.pow_apply_nonneg is supplied directly by Mathlib.Data.Matrix.Mul. SpecificLimits.Basic, Matrix.ToLinearEquiv and Topology.Instances.Matrix supply the other live dependencies. No statement type or proof body is adapted.

The scaling/positive determinant, irreducible and confined-chain developments are omitted. The decay and nonsingularity results determine the actual transient block, and the Neumann series gives summability of its first-entry weights. Retire this port when this repository's pinned Mathlib contains equivalent declarations and replace the live applications by direct reuse.

The rowSum function records the total mass remaining after a fixed number of transitions. Nonnegative powers allow each entry to be bounded by its row sum. Splitting a power into two blocks gives a row-sum bound by the product of the earlier row sum and a uniform bound on the later block.

Substochasticity makes each row sum nonincreasing in time. If every row loses a uniform positive amount of mass after N transitions, with N positive, repeated N-step blocks give a geometric upper bound. Division by N extends this bound to arbitrary times and forces each power entry to converge to zero.

If I minus the matrix were singular, a nonzero vector would be fixed by the matrix and hence by every matrix power. Entrywise convergence and finiteness of the carrier force the same vector to be zero, a contradiction. This nonsingularity result applies to the internal substochastic matrix in the finite fair-bit exit denominator argument.

**Theorem 1.1 (pow_nonneg).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.pow_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.pow_nonneg` (`✓ std3`). ∎

*Citation.* Hugh Zheng (2026). *Substochastic escape and the Neumann series in aldous-broder-lean*. URL: <https://github.com/YuZh98/aldous-broder-lean/blob/bd20382923d987fc54a9773e04a4bc22b851872c/EAB/Paper/ConfinedChain.lean>.

*Commentary.*

Every natural power of a finite real substochastic matrix has nonnegative entries.

**Theorem 1.2 (rowSum_zero).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_zero` (`✓ std3`). ∎

*Citation.* Hugh Zheng (2026). *Substochastic escape and the Neumann series in aldous-broder-lean*. URL: <https://github.com/YuZh98/aldous-broder-lean/blob/bd20382923d987fc54a9773e04a4bc22b851872c/EAB/Paper/ConfinedChain.lean>.

*Commentary.*

For every finite real square matrix and row, the row sum of its zeroth power is one.

**Theorem 1.3 (rowSum_one).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_one`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_one` (`✓ std3`). ∎

*Citation.* Hugh Zheng (2026). *Substochastic escape and the Neumann series in aldous-broder-lean*. URL: <https://github.com/YuZh98/aldous-broder-lean/blob/bd20382923d987fc54a9773e04a4bc22b851872c/EAB/Paper/ConfinedChain.lean>.

*Commentary.*

For every finite real square matrix, the row sum of its first power is the sum of the original entries in that row.

**Theorem 1.4 (rowSum_add).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_add`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_add` (`✓ std3`). ∎

*Citation.* Hugh Zheng (2026). *Substochastic escape and the Neumann series in aldous-broder-lean*. URL: <https://github.com/YuZh98/aldous-broder-lean/blob/bd20382923d987fc54a9773e04a4bc22b851872c/EAB/Paper/ConfinedChain.lean>.

*Commentary.*

For every finite real square matrix and natural exponents a and b, the row sum at a plus b is the sum over intermediate states of the a-th power entry times the b-th power row sum.

**Theorem 1.5 (rowSum_nonneg).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_nonneg` (`✓ std3`). ∎

*Citation.* Hugh Zheng (2026). *Substochastic escape and the Neumann series in aldous-broder-lean*. URL: <https://github.com/YuZh98/aldous-broder-lean/blob/bd20382923d987fc54a9773e04a4bc22b851872c/EAB/Paper/ConfinedChain.lean>.

*Commentary.*

Every row sum of every natural power of a finite real substochastic matrix is nonnegative.

**Theorem 1.6 (entry_le_rowSum).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.entry_le_rowSum`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.entry_le_rowSum` (`✓ std3`). ∎

*Citation.* Hugh Zheng (2026). *Substochastic escape and the Neumann series in aldous-broder-lean*. URL: <https://github.com/YuZh98/aldous-broder-lean/blob/bd20382923d987fc54a9773e04a4bc22b851872c/EAB/Paper/ConfinedChain.lean>.

*Commentary.*

Each entry of a natural power of a finite real substochastic matrix is bounded above by the sum of its row.

**Theorem 1.7 (rowSum_add_le).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_add_le`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_add_le` (`✓ std3`). ∎

*Citation.* Hugh Zheng (2026). *Substochastic escape and the Neumann series in aldous-broder-lean*. URL: <https://github.com/YuZh98/aldous-broder-lean/blob/bd20382923d987fc54a9773e04a4bc22b851872c/EAB/Paper/ConfinedChain.lean>.

*Commentary.*

If every row sum of the b-th power of a finite real substochastic matrix is at most a real number c, then each row sum at exponent a plus b is at most c times the corresponding row sum at exponent a.

**Theorem 1.8 (rowSum_succ_le).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_succ_le`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_succ_le` (`✓ std3`). ∎

*Citation.* Hugh Zheng (2026). *Substochastic escape and the Neumann series in aldous-broder-lean*. URL: <https://github.com/YuZh98/aldous-broder-lean/blob/bd20382923d987fc54a9773e04a4bc22b851872c/EAB/Paper/ConfinedChain.lean>.

*Commentary.*

For a finite real substochastic matrix, each row sum at exponent t plus one is at most its row sum at exponent t.

**Theorem 1.9 (rowSum_antitone).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_antitone` (`✓ std3`). ∎

*Citation.* Hugh Zheng (2026). *Substochastic escape and the Neumann series in aldous-broder-lean*. URL: <https://github.com/YuZh98/aldous-broder-lean/blob/bd20382923d987fc54a9773e04a4bc22b851872c/EAB/Paper/ConfinedChain.lean>.

*Commentary.*

For a finite real substochastic matrix and fixed row, the sequence of power row sums is antitone.

**Theorem 1.10 (rowSum_mul_le).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_mul_le`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.rowSum_mul_le` (`✓ std3`). ∎

*Citation.* Hugh Zheng (2026). *Substochastic escape and the Neumann series in aldous-broder-lean*. URL: <https://github.com/YuZh98/aldous-broder-lean/blob/bd20382923d987fc54a9773e04a4bc22b851872c/EAB/Paper/ConfinedChain.lean>.

*Commentary.*

If every row sum of the N-th power of a finite real substochastic matrix is at most c, then every row sum of its m times N-th power is at most c to the power m, for every natural m.

**Theorem 1.11 (tendsto_pow_entry).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.tendsto_pow_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.tendsto_pow_entry` (`✓ std3`). ∎

*Citation.* Hugh Zheng (2026). *Substochastic escape and the Neumann series in aldous-broder-lean*. URL: <https://github.com/YuZh98/aldous-broder-lean/blob/bd20382923d987fc54a9773e04a4bc22b851872c/EAB/Paper/ConfinedChain.lean>.

*Commentary.*

For a finite real substochastic matrix, assume a positive natural N and a real c strictly below one bound every row sum of the N-th power. Every entry of the natural matrix powers then tends to zero.

**Theorem 1.12 (det_one_sub_ne_zero).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.det_one_sub_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.det_one_sub_ne_zero` (`✓ std3`). ∎

*Citation.* Hugh Zheng (2026). *Substochastic escape and the Neumann series in aldous-broder-lean*. URL: <https://github.com/YuZh98/aldous-broder-lean/blob/bd20382923d987fc54a9773e04a4bc22b851872c/EAB/Paper/ConfinedChain.lean>.

*Commentary.*

For a finite real substochastic matrix, assume a positive natural N and a real c strictly below one bound every row sum of the N-th power. The determinant of the identity minus the matrix is then nonzero.

**Theorem 1.13 (hasSum_pow_entry).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.hasSum_pow_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.hasSum_pow_entry` (`✓ std3`). ∎

*Citation.* Hugh Zheng (2026). *Substochastic escape and the Neumann series in aldous-broder-lean*. URL: <https://github.com/YuZh98/aldous-broder-lean/blob/bd20382923d987fc54a9773e04a4bc22b851872c/EAB/Paper/ConfinedChain.lean>.

*Commentary.*

For a finite real substochastic matrix, assume a positive natural N and a real c strictly below one bound every row sum of the N-th power. The series of each matrix-power entry, starting at exponent zero, sums to the corresponding entry of the inverse of the identity minus the matrix.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.det_one_sub_ne_zero`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.entry_le_rowSum`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.hasSum_pow_entry`
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
