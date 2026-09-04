# Finite Common-Spectrum Criterion

## Abstract

A finite rational-feature Gram exists exactly when its inverse coefficient congruence is a positive Hermitian Toeplitz matrix.

**Theorem 1.1 (Finite rational Grams are exactly positive Toeplitz transforms).**

$$\forall N \in \mathbb{N}, A \in \operatorname{Matrix}(\operatorname{Fin}(N + 1), \operatorname{Fin}(N + 1), \mathbb{C}), hA \in \operatorname{IsUnit}(A), D \in \operatorname{Polynomial}(\mathbb{C}), hD \in \left(\forall z \in Circle,\; \operatorname{eval}(D, z) \neq 0\right), G \in \operatorname{Matrix}(\operatorname{Fin}(N + 1), \operatorname{Fin}(N + 1), \mathbb{C}),\; \begin{aligned}\operatorname{let} v: Circle \to \left(\operatorname{Fin}(N + 1) \to \mathbb{C}\right) = (z: Circle \mapsto (j: \operatorname{Fin}(N + 1) \mapsto z^{\operatorname{toNat}(j)}))\;\\\operatorname{let} \psi: Circle \to \left(\operatorname{Fin}(N + 1) \to \mathbb{C}\right) = (z: Circle \mapsto (i: \operatorname{Fin}(N + 1) \mapsto \frac{\operatorname{mulVec}(A, v(z))(i)}{\operatorname{eval}(D, z)}))\;\\\operatorname{let} Gram: \operatorname{FiniteMeasure}(Circle) \to \operatorname{Matrix}(\operatorname{Fin}(N + 1), \operatorname{Fin}(N + 1), \mathbb{C}) = (mu: \operatorname{FiniteMeasure}(Circle) \mapsto \operatorname{Matrix}((i: \operatorname{Fin}(N + 1) \mapsto (j: \operatorname{Fin}(N + 1) \mapsto \operatorname{integral}(z, Circle, \psi(z)(i) \cdot \operatorname{star}(\psi(z)(j)), mu)))))\;\\\operatorname{let} T: \operatorname{Matrix}(\operatorname{Fin}(N + 1), \operatorname{Fin}(N + 1), \mathbb{C}) = \operatorname{inv}(A) \cdot G \cdot \operatorname{conjTranspose}(\operatorname{inv}(A))\;\end{aligned},\\{}\left(\exists mu \in \operatorname{FiniteMeasure}(Circle),\; G = Gram(mu)\right) \Leftrightarrow \left(\operatorname{PosSemidef}(T) \land \left(\exists y \in \mathbb{Z} \to \mathbb{C},\; \left(\forall k \in \mathbb{Z},\; y({-k}) = \operatorname{star}(y(k))\right) \land T = \operatorname{toeplitzMatrix}(y, N)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/FiniteCommonSpectrumCriterion.finite_common_spectrum_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The supplied invertible coefficient matrix and polynomial without unit-circle zeros construct the complete common-denominator rational feature family.

The forward implication applies the rational Gram congruence after reciprocal denominator weighting and circle reflection.

For the converse, the truncated Toeplitz moment theorem constructs a finite positive circle measure. Restoring the denominator weight and cancelling the invertible congruence recovers the given Gram.

Conjugate symmetry of the displayed moment sequence is the public Hermitian condition. No separate Hermitian premise on the given matrix is needed because either side of the equivalence forces it.

## References

- Truth anchor: `D5/S3/Observer/BlockStructure/FiniteCommonSpectrumCriterion.finite_common_spectrum_criterion`
- Dependency: [D5/S3/Observer/BlockStructure/RationalToeplitzCollapse](RationalToeplitzCollapse.md)
- Dependency: [D5/S3/Weil/CayleyLaguerre/TruncatedCircleMomentBridge](../../Weil/CayleyLaguerre/TruncatedCircleMomentBridge.md)
- Dependency: [D5/S3/Weil/TestFunctions/LiCurvatureCriterion](../../Weil/TestFunctions/LiCurvatureCriterion.md)
