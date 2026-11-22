# Coarse coordinate pinching of pure phase records

## Abstract

Entropy and complementary records of a coarse coordinate PVM on pure phase signals.

Let c map the finite coordinate set to Fin k. The input for label j has vector ψⱼ(i) = tᵢ uⱼᵢ, with |uⱼᵢ| = 1 and Σᵢ tᵢ² = 1. Let P_b project onto the fiber of c at b and q_b = Σ_{c(i)=b} tᵢ². The actual unread channel applies Π(X) = Σ_b P_b X P_b. Entropies and logarithms use nats. The statements concern finite states, channels and readouts at a fixed measurement.

**Theorem 1.1 (The pinched signal is an orthogonal mixture).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.pinchedPhaseStates_eq_mixture`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.pinchedPhaseStates_eq_mixture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

Normalize each nonzero vector P_b ψⱼ by √q_b. Vectors from different blocks have disjoint coordinate support. The weighted projector onto each normalized vector reconstructs its unnormalized rank-one summand, and the masked vector vanishes for q_b = 0.

**Theorem 1.2 (The entropy gain is H(q)).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.phase_pinching_entropy_gain`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.phase_pinching_entropy_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

Apply OrthogonalRecordEntropy.orthogonal_mixture_entropy to the normalized nonzero block states. Their entropies and the input entropy are zero. Restoring the zero-weight terms to the Shannon sum adds zero, including for empty fibers. Watrous Definition 5.17 and equations (5.82)–(5.84) give the spectral entropy convention.

**Theorem 1.3 (The logarithm on the positive-weight block states).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.pinchedPhaseStates_log`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.pinchedPhaseStates_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The matrix logarithm is the sum of log(q_b) times the projectors onto the normalized nonzero block vectors. The finite-spectrum calculus uses Real.log 0 = 0 on the joint kernel. Watrous equation (1.145) gives the spectral functional calculus.

**Theorem 1.4 (The coherent input is supported in the pinched signal).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.phase_supportContained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.phase_supportContained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

A kernel vector has zero quadratic pairing with the pinched output. The pairing is a sum of squared overlaps with the masked vectors. Every overlap vanishes, so the kernel vector is orthogonal to their sum ψⱼ.

**Theorem 1.5 (The actual support-aware relative entropy also equals H(q)).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.phase_pinching_relative_entropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.phase_pinching_relative_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The support inclusion places the actual Umegaki divergence in its finite branch. Each P_b commutes with the logarithm of the output, so cyclicity of trace identifies its pairing with the input and with the pinched output. Watrous Definition 5.18 and equation (5.85) give the support convention and trace formula.

**Theorem 1.6 (One recording isometry gives both actual marginals).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.copiedPhaseState_marginals`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.copiedPhaseState_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The coherent copy sends |i⟩ to |i⟩⊗|c(i)⟩. The joint blocks are P_b ρⱼ P_d. Tracing the flag gives the actual unread signal, and tracing the residual gives diag(q) for every label. Watrous equation (2.34) specifies the partial trace on product-basis entries.

**Theorem 1.7 (The environment has zero Holevo label information).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.copied_environment_holevo_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.copied_environment_holevo_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

For every normalized prior the averaged environment state equals each individual environment state. Its entropy therefore equals the prior-weighted average entropy. Holevo, arXiv:quant-ph/9611023v1, sections 2–3, defines the entropy difference on p. 2 and displays it in equation (5) on p. 3.

**Theorem 1.8 (The residual coordinate PVM recovers the dephased flag).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.classicalPhaseRecord_readout`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.classicalPhaseRecord_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Dephase the flag within the actual copied state. The joint probability of flag b and residual outcome d is q_b when b = d and zero otherwise.

**Theorem 1.9 (The dephased flag has zero conditional entropy given the residual).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.classicalPhaseRecord_conditional_entropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.classicalPhaseRecord_conditional_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the same pure-state coarse pinching entropy calculation on the product register. Its lifted block weights remain q, so the dephased joint state and its residual marginal both have entropy H(q).

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.classicalPhaseRecord_conditional_entropy`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.classicalPhaseRecord_readout`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.copiedPhaseState_marginals`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.copied_environment_holevo_zero`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.phase_pinching_entropy_gain`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.phase_pinching_relative_entropy`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.phase_supportContained`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.pinchedPhaseStates_eq_mixture`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.pinchedPhaseStates_log`
- Dependency: [D5/S3/Quantum/Decoherence/RecordingIsometry](../../Decoherence/RecordingIsometry.md)
- Dependency: [D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy](../../Divergence/SupportAwareRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](../../Information/OrthogonalRecordEntropy.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/CoordinatePinching](CoordinatePinching.md)
