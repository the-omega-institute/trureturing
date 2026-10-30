# QubitNormalFormState

## Abstract

The actual closed-disk qubit entropy

**Theorem 1.1 (The actual closed-disk qubit entropy).**

$$\forall x,z:\mathbb{R},\ {(x^{2})+(z^{2})\le 1}\implies \operatorname{S}(\operatorname{qubitState}(x, z))=\operatorname{h}(\frac{(1)+(\sqrt{(x^{2})+(z^{2})})}{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/QubitNormalFormState.qubit_state_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex CLI (2026). *A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

The matrix is (I+xX+zZ)/2 in the computational basis, with real x and z and x squared plus z squared at most one. Its constructor proves positivity and trace one, including the pure boundary. The entropy on the left is the canonical CFC von Neumann entropy in natural logarithms. The proof reuses FormationBounds.qubit_entropy_det, cancels its log(2) conversion from bits, and uses the original spectral/CFC bridge.

## References

- Truth anchor: `D5/S3/Quantum/Information/QubitNormalFormState.qubit_state_entropy`
- Dependency: [D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds](../Entanglement/GraphDensity/FormationBounds.md)
