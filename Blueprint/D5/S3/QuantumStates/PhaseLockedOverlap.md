# Phase-Locked Overlaps

## Abstract

Unit-phase conjugation locks a complex overlap to a rotated real line.

**Theorem 1.1 (A phase-locked overlap lies on a rotated real line).**

$$\forall u,c\in \mathbb{C},\ \Vert u \Vert=1 \land \overline{c}=(u^{-1})^{2} c \Rightarrow \exists r\in \mathbb{R},\ c=u r$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/PhaseLockedOverlap.phase_locked_overlap_is_rotated_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let u be a complex unit phase and c a complex overlap. If conjugating c multiplies it by the square of the inverse phase, then c equals u times a real number. Thus the overlap lies on the real axis rotated by u.

The proof rotates the overlap back by the inverse phase. Mathlib identifies the inverse of a unit-modulus complex number with its conjugate; the locking equation then makes the rotated value self-adjoint, and Mathlib's self-adjoint complex-number lemma realizes it as a real scalar.

This declaration closes only the scalar phase-line conclusion of the source's two-torsion theorem. It does not construct Weyl displacement operators, certify the dimension-eight or dimension-twenty-four data, classify three-torsion or six-torsion orbits, or claim the later visibility mechanism.

## References

- Truth anchor: `D5/S3/QuantumStates/PhaseLockedOverlap.phase_locked_overlap_is_rotated_real`
