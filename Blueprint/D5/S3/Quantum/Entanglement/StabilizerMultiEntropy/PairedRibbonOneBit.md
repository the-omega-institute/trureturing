# Joint nonlinear records preserve negativity after paired ribbon erasure

## Abstract

Sharp one-bit classical record capacity for paired signed-ribbon erasure.

**Theorem 1.1 (The exact joint one-bit trace norm is 5/4; separate and linear trace norms are 1).**

$$\forall u \in \operatorname{NonemptyLiteralPairedRibbonMasks}\left(\right),\; \operatorname{JointAffineAndOneBankFlaggedTraceOptima}\left(u, \operatorname{ExactFiveQuarters}\left(\right), \operatorname{ExactOne}\left(\right), \operatorname{ExactOne}\left(\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/PairedRibbonOneBit.actual_joint_bit_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any nonempty packet of consecutive interlaced two-band blocks in one literal marked signed ribbon chart. Retain the twisted band of each block and delete the other, with arbitrary twists on the deleted bands. The two computational-basis outcomes per deleted block have the uniform Born mass proved for the actual mask. The right local Hadamard turns the normalized conditional phase amplitude into a tensor of Bell states, up to a phase that cancels from the projector.

Keep both classical message blocks with their original outcome weights. The flagged partial-transpose trace norm becomes the mean of max(1, absolute transformed record), where the transform is the orthogonal Bell sign matrix. The quadratic envelope gives 5/4, attained by a deterministic yes/no test of one full Pauli label. Any affine parity of the full raw label, or any stochastic function of one fixed bank alone, instead gives norm 1. A protocol computing two bank messages and combining them is not a one-bank record. The result is an exact norm separation; it does not determine optimal distillable entanglement or claim an advantage in sampling.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/PairedRibbonOneBit.actual_joint_bit_gap`
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonErasure](MarkedRibbonErasure.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/PairedRibbonMask](PairedRibbonMask.md)
