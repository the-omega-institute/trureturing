# Mixed-State Robertson Uncertainty

## Abstract

Mixed-state standard deviations bound the expected commutator magnitude.

**Theorem 1.1 (Mixed-state Robertson uncertainty).**

$$\begin{aligned}\forall d: \operatorname{Type}, [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\\\forall \rho: \operatorname{DensityState}\left(d\right), A, B: \operatorname{Matrix}\left(d, d, \mathbb{C}\right),\\\operatorname{Hermitian}(A) \land \operatorname{Hermitian}(B) \Rightarrow \\(rhoMatrix:=\operatorname{toMatrix}\left(\rho\right)) \land (stateRoot:=\sqrt{rhoMatrix}) \land \\(u:=(A-\operatorname{Tr}(rhoMatrix\cdot A)\cdot I)\cdot stateRoot) \land (v:=(B-\operatorname{Tr}(rhoMatrix\cdot B)\cdot I)\cdot stateRoot) \Rightarrow \\\Vert u\Vert_{HS}\Vert v\Vert_{HS} \geq \frac{1}{2}\Vert \operatorname{Tr}(rhoMatrix\cdot (AB-BA))\Vert.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/Designs/MixedStateRobertson.mixed_state_robertson_uncertainty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d be a finite index type with decidable equality, rho a canonical density state, and A and B Hermitian complex square matrices. The density-state carrier supplies positivity and trace-one normalization.

The underlying density matrix and its positive continuous-functional-calculus square root construct the centered GNS vectors u and v. Their Frobenius norms are the two standard deviations.

Cauchy-Schwarz bounds the weighted cross pairing, whose imaginary part is one half of the expected commutator. This gives the displayed Robertson inequality for mixed as well as pure density states.

## References

- Truth anchor: `D5/S3/QuantumBounds/Designs/MixedStateRobertson.mixed_state_robertson_uncertainty`
- Dependency: [D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition](../../Quantum/Divergence/QuantumRelativeEntropyDefectComposition.md)
- Dependency: [D5/S3/Quantum/GNSMatrix](../../Quantum/GNSMatrix.md)
