# FIB hidden-joint coherence boundary

## Abstract

The diagonal hidden-joint readout bounds, but does not determine, the corresponding coherence.

The existing finite FIB instrument has a branch whose diagonal input trace is the source coordinate 25. This document extends that boundary to arbitrary matrix inputs and records the positivity constraint on the 2-4 off-diagonal entry. The source coordinate rho(4,4) is the hidden joint mass kappa; the off-diagonal entry rho(2,4) is a separate coherence coordinate.

**Theorem 1.1 (Positivity bounds the coherence radius).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/CoherenceBoundary.coherence_radius_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/CoherenceBoundary.coherence_radius_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive semidefinite five-state matrix, the squared magnitude of the 2-4 coherence is at most the product of the two corresponding diagonal masses. This is a principal-minor consequence of positivity and supplies only a radius bound; it does not determine a phase or a nonzero coherence.

**Theorem 1.2 (The odd-rejection branch is diagonal-blind).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/CoherenceBoundary.arbitrary_branch_trace_reads_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/CoherenceBoundary.arbitrary_branch_trace_reads_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary five-state matrix input, the concrete odd-rejection Kraus branch has trace equal to its source diagonal entry 4. Its off-diagonal entries, including the 2-4 coherence, do not enter this trace.

**Theorem 1.3 (The hidden joint mass leaves a coherence fibre).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/CoherenceBoundary.hidden_joint_bounds_coherence`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/CoherenceBoundary.hidden_joint_bounds_coherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining the two exact statements gives the current quantum boundary: the branch reads rho(4,4), while positivity restricts rho(2,4) to a disk of squared radius at most rho(2,2) times rho(4,4). The branch record alone therefore cannot recover the phase or select a point in that coherence fibre.

This is a finite matrix statement for the stipulated instrument. It does not assert physical state preparation, a Fock-space realization, Hamiltonian dynamics, phase tomography, or gravitational sourcing. A phase-sensitive reference and a separate non-diagonal readout remain open.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/CoherenceBoundary.arbitrary_branch_trace_reads_diagonal`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/CoherenceBoundary.coherence_radius_bound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/CoherenceBoundary.hidden_joint_bounds_coherence`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument](ReadoutInstrument.md)
