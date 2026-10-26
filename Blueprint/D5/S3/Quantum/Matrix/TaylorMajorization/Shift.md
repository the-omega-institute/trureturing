# Scalar translation of Taylor defects.

## Abstract

Scalar translation of Taylor defects.

**Theorem 1.1 (Scalar translation of the ordered coefficients).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Shift.taylorQ_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TaylorMajorization/Shift.taylorQ_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex square matrices A and B, a complex scalar s and every natural k, Q(A+sI,B) at order k is the sum over j from zero to k of choose(k,j) times s to the k-j times Q(A,B) at order j. Left multiplication by A and right multiplication by B commute as linear endomorphisms. The matrix coefficient is their binomial power applied to the identity, and translating A adds s times the identity endomorphism.

**Theorem 1.2 (Real trace of Hermitian symmetrization).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Shift.trace_taylorR`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TaylorMajorization/Shift.trace_taylorR` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any complex matrices A and B and any order k, the real traces of R and Q agree. This directly specializes the existing IncoherentCone.trace_hermitianPart theorem to the identity weight; the explicit Hermitian part is the same symmetrization.

**Theorem 1.3 (The binomial transform of the trace defect).**

Lean statement: `D5/S3/Quantum/Matrix/TaylorMajorization/Shift.defect_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/TaylorMajorization/Shift.defect_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real scalar s, the defect at (A+sI,B) and order k is the sum over j from zero to k of choose(k,j) times s to the k-j times the defect at (A,B) and order j. Apply the ordered coefficient translation identity and the commuting binomial theorem for A+B and sI, then take real traces.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Shift.defect_shift`
- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Shift.taylorQ_shift`
- Truth anchor: `D5/S3/Quantum/Matrix/TaylorMajorization/Shift.trace_taylorR`
- Dependency: [D5/S3/Quantum/Matrix/TaylorMajorization/Defs](Defs.md)
- Dependency: [D5/S3/Quantum/Measurement/IncoherentCone](../../Measurement/IncoherentCone.md)
