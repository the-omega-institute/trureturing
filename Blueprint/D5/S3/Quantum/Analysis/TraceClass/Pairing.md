# The continuous observable trace pairing

## Abstract

Analytic trace norms and bounded trace pairings on arbitrary complete complex Hilbert spaces.

**Theorem 1.1 (The continuous observable trace pairing).**

$$\operatorname{tracePairingContinuousLinearMap}\left(A\right) = \operatorname{tracePairing}\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/Pairing.tracePairingContinuousLinearMap_apply` (`✓ std3`). ∎

*Citation.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

The map sending a bounded A to the functional T maps to Tr(A T) is complex linear and continuous from the operator norm into the strong dual of the genuine trace-class Banach space. Its norm is bounded by one. The trace-class slot uses the trace norm.

Attributed to Tom Ole Diem, Physlib at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. The original copyright notice and license are preserved. No mathematical originality is claimed for these suppliers.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Pairing.tracePairingContinuousLinearMap_apply`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Banach](Banach.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/TraceAlgebra](TraceAlgebra.md)
