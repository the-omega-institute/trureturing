# Entropy under entrywise modulus in dimension three

## Abstract

Entrywise modulus increases trace-log entropy for positive semidefinite three-by-three matrices.

**Theorem 1.1 (Spectral trace-log formula).**

$$\forall n \in \operatorname{Type},\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall A \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall hA \in \operatorname{Matrix.IsHermitian}\left(A\right),\; -(\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(A \cdot \operatorname{CFC.log}\left(A\right)\right)\right)) = -(\sum_{i:n} (\operatorname{Matrix.IsHermitian.eigenvalues}\left(hA, i\right) \cdot \operatorname{Real.log}\left(\operatorname{Matrix.IsHermitian.eigenvalues}\left(hA, i\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy.entropy_eq_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Hermitian functional calculus expresses trace-log entropy as the sum over all real eigenvalues, with multiplicity.

**Definition 1.2 (Entrywise complex modulus).**

$$\forall G \in \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; \operatorname{entryModulus}\left(G\right) = \operatorname{Matrix.map}\left(G, fun (z: \mathbb{C}) \mapsto (\left\lVert z \right\rVert: \mathbb{C})\right)$$

*Formalization.* `D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy.entryModulus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Matrix.map embeds the norm of every complex entry back into the complex numbers.

**Theorem 1.3 (Diagonal entries are unchanged).**

$$\forall G \in \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; \forall i \in \operatorname{Fin}\left(3\right),\; (\operatorname{Matrix.PosSemidef}\left(G\right)) \Rightarrow (\operatorname{entryModulus}\left(G\right)\left(i, i\right) = G\left(i, i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy.entryModulus_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive semidefinite matrices have nonnegative real diagonal entries.

**Theorem 1.4 (Trace is unchanged).**

$$\forall G \in \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; (\operatorname{Matrix.PosSemidef}\left(G\right)) \Rightarrow (\operatorname{Matrix.trace}\left(\operatorname{entryModulus}\left(G\right)\right) = \operatorname{Matrix.trace}\left(G\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy.entryModulus_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal identity preserves the sum of diagonal entries.

**Theorem 1.5 (Positivity in dimension three).**

$$\forall G \in \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; (\operatorname{Matrix.PosSemidef}\left(G\right)) \Rightarrow (\operatorname{Matrix.PosSemidef}\left(\operatorname{entryModulus}\left(G\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy.entryModulus_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first two elementary spectral coefficients are fixed and the determinant increases. Their nonnegativity excludes a negative eigenvalue.

**Theorem 1.6 (The modulus entropy inequality).**

$$\forall G \in \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; (\operatorname{Matrix.PosSemidef}\left(G\right)) \Rightarrow (-(\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(G \cdot \operatorname{CFC.log}\left(G\right)\right)\right)) \le -(\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{entryModulus}\left(G\right) \cdot \operatorname{CFC.log}\left(\operatorname{entryModulus}\left(G\right)\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy.entryModulus_entropy_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For three nonnegative eigenvalues with fixed mass and second elementary symmetric function, entropy increases with their product. Shifted logarithmic sums have ordered derivatives and equal limits at infinity. Entrywise modulus preserves the first two spectral coefficients and increases the determinant. No trace normalization or invertibility is required.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy.entropy_eq_spectrum`
- Truth anchor: `D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy.entryModulus`
- Truth anchor: `D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy.entryModulus_diag`
- Truth anchor: `D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy.entryModulus_entropy_mono`
- Truth anchor: `D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy.entryModulus_posSemidef`
- Truth anchor: `D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy.entryModulus_trace`
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Resource/LogDet/PathSpectralClassical](../../Resource/LogDet/PathSpectralClassical.md)
