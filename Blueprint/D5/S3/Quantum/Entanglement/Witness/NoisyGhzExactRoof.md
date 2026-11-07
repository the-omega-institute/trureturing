# Noisy GHZ finite phase characters

## Abstract

Independent-coordinate phase cancellation and exact noisy-GHZ parameter checkpoints.

**Theorem 1.1 (Independent-coordinate character orthogonality).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.phaseCharacter_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.phaseCharacter_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d and every coefficient vector v : Fin d → ZMod 3, the sum of phaseCharacter v over the full independent phase group Fin d → ZMod 3 is 3^d when v is zero and zero otherwise. The proof factors the finite sum into one coordinate at a time and applies the primitive standard additive character sum on ZMod 3. This is the arbitrary-dimensional cancellation needed for the full matrix witness.

**Theorem 1.2 (Ordered-pair phase cancellation).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pair_phase_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pair_phase_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient vector for an ordered pair (i,j) is the coordinate indicator of i minus the coordinate indicator of j. It is zero exactly when i=j, so averaging its phase character over independent coordinates keeps precisely the diagonal terms. No claim that scalar differences of indices are distinct modulo three is used.

**Theorem 1.3 (Exact qutrit parameter checkpoint).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qutrit_source_arithmetic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qutrit_source_arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At n=d=3 the checked source parameters are M=27, K=3, R=21, k=8/9 and p_W=3/4. The same module evaluates the exact two-mean formula at f=23/36 and y=11/12 to (14−√115)/27.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pair_phase_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.phaseCharacter_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qutrit_source_arithmetic`
