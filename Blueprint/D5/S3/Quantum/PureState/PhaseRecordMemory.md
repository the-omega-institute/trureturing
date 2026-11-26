# Finite memory for flat phase records

## Abstract

The phase-decoding dual gap controls the success of decoding through a finite CPTP memory.

**Theorem 1.1 (The dual slack dominates the complement of a normalized phase row).**

Lean statement: `D5/S3/Quantum/PureState/PhaseRecordMemory.phaseDual_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseRecordMemory.phaseDual_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yonina C. Eldar, Alexandre Megretski, George C. Verghese (2003). *Designing optimal quantum detectors via semidefinite programming*. DOI: [10.1109/TIT.2003.809510](https://doi.org/10.1109/TIT.2003.809510). URL: <https://arxiv.org/abs/quant-ph/0205178>.

*Commentary.*

Let N be the nonzero carrier size, t the real amplitude profile, S its sum, and m a nonnegative lower bound for all amplitudes. For a row with unit-modulus entries, let P be the projection onto that normalized phase row. The unscaled diagonal dual slack dominates S m (I − P) in positive-semidefinite order. Multiplying by the uniform prior 1 / N gives the coefficient S m / N.

Eldar, Megretski and Verghese formulate the finite discrimination dual in Eqs. (15)–(18) and its complementary slackness in Eqs. (19)–(20) of arXiv:quant-ph/0205178. The phase estimate compares the slack to the complementary projection by subtracting a common lower bound from the amplitudes.

**Theorem 1.2 (Two upper bounds for success through a finite CPTP memory).**

Lean statement: `D5/S3/Quantum/PureState/PhaseRecordMemory.phase_success_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseRecordMemory.phase_success_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg and Dennj Osele (2025). *Physlib QuantumInfo: unbundled channels, channel duals and Hermitian-matrix order*. URL: <https://github.com/leanprover-community/physlib/tree/6a09b2d1761a0d4430083045a247eb121d8da260>.

*Acknowledgement.* Yonina C. Eldar, Alexandre Megretski, George C. Verghese (2003). *Designing optimal quantum detectors via semidefinite programming*. DOI: [10.1109/TIT.2003.809510](https://doi.org/10.1109/TIT.2003.809510). URL: <https://arxiv.org/abs/quant-ph/0205178>.

*Commentary.*

Let t have sum of squares one, g = S² / N, and M be the encoder output dimension. For any nonnegative lower bound m on the amplitudes, every CPTP encoder and output POVM give uniform success at most min(M / N, g − (1 − M / N) S m). For a nonnegative profile, substitute m = minᵢ tᵢ. The phase entries need only have unit modulus for this upper bound.

The proof uses the Physlib matrix-map trace dual to pull back the POVM. Positivity and unitality preserve the POVM constraints, and the trace-one output states give the dimension estimate. The prior-art search for this packet found no statement of the explicit phase-memory penalty for arbitrary CPTP encoders and final POVMs.

For AURIC, let the preprocessing encoder output an M-dimensional register and let the fixed ProjectiveTree.flaggedChannel act on it. A final effect Dₓ on the binary terminal flag and residual register pulls back to the effect flaggedChannel* (Dₓ) on the M-dimensional register. These effects form a POVM with the same success probability by trace duality, so the bound uses the preprocessing dimension M even though the flagged output has dimension 2M. At equal amplitudes a one-leaf tree with identity unitary and fixed flag permits the orthogonal saturation construction.

**Theorem 1.3 (Positive orthogonal phase profiles require the full carrier dimension).**

Lean statement: `D5/S3/Quantum/PureState/PhaseRecordMemory.phase_optimum_attainable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseRecordMemory.phase_optimum_attainable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yonina C. Eldar, Alexandre Megretski, George C. Verghese (2003). *Designing optimal quantum detectors via semidefinite programming*. DOI: [10.1109/TIT.2003.809510](https://doi.org/10.1109/TIT.2003.809510). URL: <https://arxiv.org/abs/quant-ph/0205178>.

*Commentary.*

Assume the flat phase matrix has column Gram matrix N times the identity and every amplitude is positive. A CPTP encoder and output POVM attain the full-carrier guessing probability exactly when the output dimension is at least N. The forward implication uses the strictly positive dual gap. An isometric encoder realizes the converse.

For these linearly independent pure signals, the prior-weighted Gram square root has constant diagonal S / N. Sasaki, Kato, Izutsu and Hirota give the resulting square-root measurement criterion in §II, Theorem 1 of arXiv:quant-ph/9801012.

The exact threshold also follows from published ingredients. Kennedy’s uniqueness theorem on the signal span (MIT RLE Quarterly Progress Report 113, pp. 129–130) forces any POVM pulled back from an optimum-preserving encoder to equal the phase PVM. The encoded phase basis tests can then be distinguished perfectly, which forces M ≥ N by the one-shot dimension bound, the uniform-label case of the bound in Nayak’s Theorem 2.4(2). Measuring the phase PVM and storing its outcome in N orthogonal states gives the reverse implication.

**Theorem 1.4 (Equal amplitudes attain the dimension bound).**

Lean statement: `D5/S3/Quantum/PureState/PhaseRecordMemory.orthogonal_phase_success_attains_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseRecordMemory.orthogonal_phase_success_attains_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For normalized orthogonal phase rows and a memory with 1 ≤ M ≤ N, an encoder retains M orthogonal labels and resets the complementary subspace to a fixed memory state. A labelled POVM attains uniform success M / N.

## References

- Truth anchor: `D5/S3/Quantum/PureState/PhaseRecordMemory.orthogonal_phase_success_attains_dimension`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseRecordMemory.phaseDual_gap`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseRecordMemory.phase_optimum_attainable_iff`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseRecordMemory.phase_success_le`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/PureState/JointRecordTransport](JointRecordTransport.md)
- Dependency: [D5/S3/Quantum/Recovery/KrausCompletion](../Recovery/KrausCompletion.md)
