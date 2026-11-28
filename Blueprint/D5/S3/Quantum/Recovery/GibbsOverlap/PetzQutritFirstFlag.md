# Strict two-flag overlap deficit

## Abstract

The certified qutrit deficit dominates the complementary-flag bound.

Use the integer Hermitian matrices A and B from the polar-overlap witness. Put N = Re Tr exp(2B), Q = exp(2B)/N, ε = 2⁻¹⁰⁰, M = exp(2A), D₁ = εM, and D₂ = I − εM. Both effects are positive definite, their sum is I, and Q is a faithful density matrix.

**Lemma 1.1 (The two effects sum to the identity).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.effects_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.effects_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D₁ + D₂ = I.

**Lemma 1.2 (The retained Gibbs state is faithful).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.Q_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.Q_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix of Q is positive definite.

**Lemma 1.3 (The matrix representation preserves the exponential).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.mat_exp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.mat_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every qutrit CStarMatrix, the matrix of its exponential is the exponential of its matrix.

**Lemma 1.4 (The first effect is strictly positive).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.D1_strictlyPositive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.D1_strictlyPositive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential of 2A is strictly positive, as is its scale ε.

**Lemma 1.5 (The complementary effect is strictly positive).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.D2_strictlyPositive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.D2_strictlyPositive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bound εM ≤ I/2 gives D₂ ≥ I/2.

**Theorem 1.6 (The sum of overlap norms is strictly below the partition trace).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.two_flag_overlap_lt_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.two_flag_overlap_lt_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Ωᵢ = exp(log Q + log Dᵢ), the sum of ‖√Ωᵢ √Dᵢ √Q‖₁ is strictly below the sum of Re Tr Ωᵢ. The first flag rescales the certified word exp(A+B) exp(A) exp(B) by ε/N and has deficit less than −ε exp(18)/(2N). The complementary-flag bound gives a deficit at most ε² exp(44)/2. Since N ≤ 3 exp(32) and ε exp(44) < exp(−14)/3, the sum is strictly negative.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.D1_strictlyPositive`
- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.D2_strictlyPositive`
- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.Q_posDef`
- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.effects_sum`
- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.mat_exp`
- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.two_flag_overlap_lt_partition`
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../../Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/Recovery/GibbsOverlap/PetzIntegerQutritOverlap](PetzIntegerQutritOverlap.md)
- Dependency: [D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritSecondFlag](PetzQutritSecondFlag.md)
