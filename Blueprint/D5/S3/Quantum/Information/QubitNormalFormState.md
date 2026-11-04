# QubitNormalFormState

## Abstract

The actual closed-disk qubit entropy

**Theorem 1.1 (The spectral determinant formula).**

$$\forall T:\operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{C}),\ {\operatorname{PosSemidef}(T)\land \operatorname{trace}(T)=1}\implies \operatorname{spectralEntropy}(T)=\operatorname{h}(\frac{1-\sqrt{1-4\cdot \operatorname{re}(\operatorname{det}(T))}}{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/QubitNormalFormState.qubit_spectral_entropy_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex CLI (2026). *A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

For every complex positive semidefinite two by two matrix of trace one, its natural-log spectral entropy is the binary entropy of the smaller eigenvalue computed from its determinant. This is the shared eigenvalue proof underlying FormationBounds.qubit_entropy_det; its original statement in bits is retained there.

**Theorem 1.2 (The actual closed-disk qubit entropy).**

$$\forall x,z:\mathbb{R},\ {(x^{2})+(z^{2})\le 1}\implies \operatorname{S}(\operatorname{qubitState}(x, z))=\operatorname{h}(\frac{(1)+(\sqrt{(x^{2})+(z^{2})})}{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/QubitNormalFormState.qubit_state_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex CLI (2026). *A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

The matrix is (I+xX+zZ)/2 in the computational basis, with real x and z and x squared plus z squared at most one. Its constructor proves positivity and trace one, including the pure boundary. The entropy on the left is the canonical CFC von Neumann entropy in natural logarithms. The proof shares the qubit determinant spectral proof with FormationBounds and uses the original spectral/CFC bridge.

## References

- Truth anchor: `D5/S3/Quantum/Information/QubitNormalFormState.qubit_spectral_entropy_det`
- Truth anchor: `D5/S3/Quantum/Information/QubitNormalFormState.qubit_state_entropy`
- Dependency: [D5/S3/Quantum/Information/InputInformationBalance](InputInformationBalance.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](PartialTraceMutualInformation.md)
