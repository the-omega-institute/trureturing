# Pure qutrit local compression in joint trace distance

## Abstract

For the normalized qutrit Bell state, the least joint trace-distance error among channels supported in a prescribed output plane is 2/3. An explicit qubit-memory protocol achieves strictly smaller error.

The source is the normalized qutrit Bell state. The reference factor stays untouched. Distortion is half the trace norm of the joint state difference. The qubit protocol uses one fixed encoder and one fixed decoder, connected solely by the qubit. Kato Section VII proposes approximate local compression. Nayak and Sen Theorem 2.1 characterizes reversible finite channels. Schumacher Eq. (10) expresses entanglement fidelity in terms of Kraus operators. Farber and Gour Theorem 5 gives the exact unassisted root fidelity and uses projection with reset to attain it. Cha, Park and Lee Proposition 3.7 exhibits a nonisometric-decoder advantage for phase-ensemble fidelity. Their Appendix D treats Haar-average fidelity and Appendix L gives bounds for ensemble-average trace distance.

**Theorem 1.1 (Exact least distortion with output in a prescribed plane).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/QutritPure.plane_optimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/QutritPure.plane_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kohtaro Kato (2025). *Exact and Local Compression of Quantum Bipartite States*. DOI: [10.1109/TIT.2025.3562884](https://doi.org/10.1109/TIT.2025.3562884). URL: <https://arxiv.org/abs/2309.07434>.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Omri Farber and Gilad Gour (2026). *Classical Communication Helps Single-Shot Quantum Compression*. URL: <https://arxiv.org/abs/2610.14785v1>.

*Commentary.*

For every unitary frame, the minimum over CPTP maps into its first two levels is 2/3. In the coordinate frame the effect is the projector onto the normalized vector with coefficients (1, 1, 2) on the matched coordinates. Its expectation on the source is 8/9. With output in the plane, the effect expectation is at most 2/9 by positivity and the uniform Choi reference marginal. Projection to the two kept coordinates with the discarded input reset to level 1 attains the bound. For this channel the difference is bounded above by a positive rank-one matrix of trace 2/3. Conjugating the input and output by a common change of basis acts by unitary congruence on the joint difference, preserving the trace norm.

**Theorem 1.2 (A strict qubit-memory witness).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/QutritPure.qubit_memory_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/QutritPure.qubit_memory_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kohtaro Kato (2025). *Exact and Local Compression of Quantum Bipartite States*. DOI: [10.1109/TIT.2025.3562884](https://doi.org/10.1109/TIT.2025.3562884). URL: <https://arxiv.org/abs/2309.07434>.

*Acknowledgement.* Benjamin Schumacher (1996). *Sending entanglement through noisy quantum channels*. DOI: [10.1103/PhysRevA.54.2614](https://doi.org/10.1103/PhysRevA.54.2614). URL: <https://arxiv.org/abs/quant-ph/9604023>.

*Acknowledgement.* Omri Farber and Gilad Gour (2026). *Classical Communication Helps Single-Shot Quantum Compression*. URL: <https://arxiv.org/abs/2610.14785v1>.

*Acknowledgement.* Hyunho Cha, Chae-Yeun Park and Jungwoo Lee (2026). *Toward the Goldilocks Blind Compression of Quantum States*. URL: <https://arxiv.org/abs/2605.01258v2>.

*Commentary.*

The encoder preserves the plane and resets input level 2 to memory level 1. The decoder uses amplitudes (1, 4/5) on the embedded qubit and sends level 1 to output level 2 with amplitude 3/5 in a second Kraus operator. Both families sum to the identity in their Kraus completeness equations. On the matched coordinates the source-minus-output difference is dominated by the outer product of (60, 73, 107) divided by 31500. The slack is a sum of positive rank-one matrices on the full joint space, including the two unmatched output coordinates. The majorant has trace 10189/15750, strictly below 13/20 and 2/3.

**Theorem 1.3 (The witness decoder has no single-isometry representation).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/QutritPure.witness_decoder_not_isometric`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/QutritPure.witness_decoder_not_isometric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Hyunho Cha, Chae-Yeun Park and Jungwoo Lee (2026). *Toward the Goldilocks Blind Compression of Quantum States*. URL: <https://arxiv.org/abs/2605.01258v2>.

*Commentary.*

The pure input at memory level 1 has output probabilities 16/25 and 9/25 on levels 1 and 2 with zero off-diagonal entries. A single matrix conjugation would send that input to an outer product, whose two diagonal entries multiply to the squared magnitude of the off-diagonal entry.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/QutritPure.plane_optimum`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/QutritPure.qubit_memory_witness`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/QutritPure.witness_decoder_not_isometric`
- Dependency: [D5/S3/Quantum/ProcessReconstruction/LiuWildChoiObstruction](../../ProcessReconstruction/LiuWildChoiObstruction.md)
