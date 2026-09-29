# Finite Detection Dark Space

## Abstract

A finite-dimensional repeated-detection dark space is determined after dimension many no-click steps.

**Theorem 1.1 (The dark space is a finite survival-defect kernel).**

$$\forall d: \operatorname{Nat}, X: \operatorname{Type}, [\operatorname{Fintype}(X)],\\{}Q: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), L: X \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}),\\{}Q^{*} \cdot Q+\sum_{x \in X} L_{x}^{*} \cdot L_{x} = I_{d} \Rightarrow \forall psi: \operatorname{Fin}(d) \to \mathbb{C},\\{}(\forall n: \operatorname{Nat}, x: X, \operatorname{mulVec}(L_{x} \cdot Q^{n}, psi) = 0) \iff \operatorname{mulVec}(I_{d}-{Q^{*}}^{d} \cdot Q^{d}, psi) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FiniteDetectionDarkSpace.dark_space_eq_survival_defect_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q be the no-click operator and let the finite family L_x contain the click operators. Their adjoint products sum with Q^* Q to the identity. The statement also holds in dimension zero, where both sides are trivially true.

The completeness equation telescopes: the defect of the N-step survival operator is the sum, from n = 0 to N - 1 and over all outcomes x, of the Gram operators of L_x Q^n. Positivity therefore identifies its kernel with the common kernel of those event amplitudes.

At N equal to the dimension, Cayley-Hamilton expresses every later power of Q through earlier powers. Hence vanishing of the first dimension many event amplitudes propagates to every time.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/FiniteDetectionDarkSpace.dark_space_eq_survival_defect_kernel`
