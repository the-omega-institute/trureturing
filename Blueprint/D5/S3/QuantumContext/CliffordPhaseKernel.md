# An Extended Clifford Phase Invariant

## Abstract

The frequency-48 cosine kernel is constant on extended Clifford phase orbits.

**Theorem 1.1 (The frequency-48 cosine kernel is Clifford invariant).**

$$\forall \theta\in \mathbb{R}, k\in \mathbb{Z},\ 2 \operatorname{cos}(48 {\theta+k\cdot\frac{2\pi}{24}})=2 \operatorname{cos}(48 \theta) \land 2 \operatorname{cos}(48 {-\theta+k\cdot\frac{2\pi}{24}})=2 \operatorname{cos}(48 \theta).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/CliffordPhaseKernel.clifford_phase_kernel_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real phase theta and integer shift k, the kernel 2 cos(48 theta) is unchanged after adding k times 2 pi / 24. It remains unchanged when the phase is first reversed, so it is constant under both unitary phase shifts and the antiunitary branch.

Pinned Mathlib supplies the exact integer-period theorem Real.cos_add_int_mul_two_pi and the evenness theorem Real.cos_neg. The Lean proof only normalizes the frequency and phase-step factors before applying those two upstream results.

This declaration closes only the kernel-invariance sentence of residual remark 27.602, clause 3. It does not formalize the two displayed numerical multisets, prove that those multisets differ, classify the extended Clifford orbits, or certify the stated Galois identity.

## References

- Truth anchor: `D5/S3/QuantumContext/CliffordPhaseKernel.clifford_phase_kernel_invariant`
