# Negativity and structured negativity differ for a pure two-qutrit state

## Abstract

The pure state (|00⟩ + 2|11⟩ + 2|22⟩)/3 has three negative partial-transpose eigenvalues, but negativity 8/9 and structured negativity 4/3. It refutes the coincidence conjecture of Kumari and Adhikari.

**Definition 1.1 (Partial transpose on B).**

$$\forall d:\mathbb{N}, \forall rho:\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall i:\operatorname{Fin}\left(d\right), \forall j:\operatorname{Fin}\left(d\right), \forall k:\operatorname{Fin}\left(d\right), \forall l:\operatorname{Fin}\left(d\right), \operatorname{partialTransposeB}\left(rho\right)\left((i,j), (k,l)\right) = rho\left((i,l), (k,j)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.partialTransposeB` (`✓ std3`).

*Citation.* A. Kumari; S. Adhikari (2022). *Structured negativity: A physically realizable measure of entanglement based on structural physical approximation*. DOI: [10.48550/arXiv.2209.03909](https://doi.org/10.48550/arXiv.2209.03909). URL: <https://arxiv.org/abs/2209.03909v1>.

*Commentary.*

The basis indices are pairs in Fin d × Fin d for C^d ⊗ C^d. Partial transposition exchanges the second row and column coordinates, leaving the first coordinates in place.

**Definition 1.2 (Density matrices).**

$$\forall d:\mathbb{N}, \forall rho:\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{IsDensity}\left(rho\right) \Leftrightarrow ((\operatorname{PosSemidef}\left(rho\right)) \land (\operatorname{trace}\left(rho\right) = 1))$$

*Formalization.* `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.IsDensity` (`✓ std3`).

*Citation.* A. Kumari; S. Adhikari (2022). *Structured negativity: A physically realizable measure of entanglement based on structural physical approximation*. DOI: [10.48550/arXiv.2209.03909](https://doi.org/10.48550/arXiv.2209.03909). URL: <https://arxiv.org/abs/2209.03909v1>.

*Commentary.*

A density matrix is positive semidefinite and has trace one; positivity is Mathlib's complex Hermitian positive semidefiniteness.

**Definition 1.3 (Hermitian eigenvalues with multiplicity).**

$$(\forall d:\mathbb{N}, \forall A:\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall h:\operatorname{IsHermitian}\left(A\right), \operatorname{eigenvalues}\left(A\right) = \operatorname{map}\left(h.eigenvalues, \operatorname{val}\left((\operatorname{Finset.univ}:\operatorname{Finset}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right))\right)\right)) \land (\forall d:\mathbb{N}, \forall A:\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right), (\neg \operatorname{IsHermitian}\left(A\right)) \Rightarrow \operatorname{eigenvalues}\left(A\right) = 0)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.eigenvalues` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Kumari; S. Adhikari (2022). *Structured negativity: A physically realizable measure of entanglement based on structural physical approximation*. DOI: [10.48550/arXiv.2209.03909](https://doi.org/10.48550/arXiv.2209.03909). URL: <https://arxiv.org/abs/2209.03909v1>.

*Commentary.*

For a Hermitian matrix A, let h be its Hermitian proof and let h.eigenvalues be Mathlib's real eigenvalue function on Fin d × Fin d. The multiset maps every element of this index type to its eigenvalue, retaining duplicates. Matrix.IsHermitian.roots_charpoly_eq_eigenvalues identifies its complex image with the characteristic-polynomial roots, including algebraic multiplicity. For a non-Hermitian matrix this definition returns the empty multiset; this extension is not used for the density matrix or its partial transpose and SPA below.

**Definition 1.4 (Count of negative eigenvalues).**

$$\forall d:\mathbb{N}, \forall A:\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{negCount}\left(A\right) = \operatorname{card}\left(\operatorname{filter}\left(x \mapsto x < 0, \operatorname{eigenvalues}\left(A\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.negCount` (`✓ std3`).

*Citation.* A. Kumari; S. Adhikari (2022). *Structured negativity: A physically realizable measure of entanglement based on structural physical approximation*. DOI: [10.48550/arXiv.2209.03909](https://doi.org/10.48550/arXiv.2209.03909). URL: <https://arxiv.org/abs/2209.03909v1>.

*Commentary.*

The source states (p. 4): 'Let us suppose that (I ⊗ T)ρ has q (≤ (d−1)^2) number of negative eigenvalues'. Here q counts strictly negative eigenvalues with multiplicity, rather than distinct numerical values.

**Definition 1.5 (Negativity).**

$$\forall d:\mathbb{N}, \forall rho:\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{negativity}\left(d, rho\right) = \frac{2}{(\operatorname{val}\left(d\right):\mathbb{R}) - 1} \cdot \operatorname{sum}\left(\operatorname{map}\left(\operatorname{abs}, \operatorname{filter}\left(x \mapsto x < 0, \operatorname{eigenvalues}\left(\operatorname{partialTransposeB}\left(rho\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.negativity` (`✓ std3`).

*Citation.* A. Kumari; S. Adhikari (2022). *Structured negativity: A physically realizable measure of entanglement based on structural physical approximation*. DOI: [10.48550/arXiv.2209.03909](https://doi.org/10.48550/arXiv.2209.03909). URL: <https://arxiv.org/abs/2209.03909v1>.

*Commentary.*

Equation (6), p. 2: 'N(ρ) = (‖ρ^{T_B}‖_1 − 1)/(d−1) = (2/(d−1)) Σ_{λ_i<0} |λ_i(ρ^{T_B})| where ‖.‖_1 denotes trace norm and ρ^{T_B} is the partial transposition of the density matrix ρ.' The definition uses the displayed eigenvalue-sum form. The sum traverses the negative-eigenvalue multiset, so repeats contribute repeatedly. The real cast of d is taken before subtracting 1. Typed val occurrences denote the indicated natural-number coercions to the real or complex numbers.

**Definition 1.6 (Structural physical approximation).**

$$\forall d:\mathbb{N}, \forall rho:\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{spaPT}\left(rho\right) = \frac{(\operatorname{val}\left(d\right):\mathbb{C})}{(\operatorname{val}\left(d\right):\mathbb{C})^{3} + 1} \cdot 1 + \frac{1}{(\operatorname{val}\left(d\right):\mathbb{C})^{3} + 1} \cdot \operatorname{partialTransposeB}\left(rho\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.spaPT` (`✓ std3`).

*Citation.* A. Kumari; S. Adhikari (2022). *Structured negativity: A physically realizable measure of entanglement based on structural physical approximation*. DOI: [10.48550/arXiv.2209.03909](https://doi.org/10.48550/arXiv.2209.03909). URL: <https://arxiv.org/abs/2209.03909v1>.

*Commentary.*

Equation (7), p. 2: 'For d ⊗ d system described by the density operator ρ, the SPA-PT of the state ρ denoted as ρ̃ and it may be expressed as [32],' followed by ρ̃ = (d/(d^3+1)) I⊗I + (1/(d^3+1)) [I⊗T](ρ). The identity on the pair-indexed space is I⊗I; the coefficients in Lean are complex scalar multiples.

**Definition 1.7 (Least eigenvalue).**

$$\forall d:\mathbb{N}, \forall A:\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{leastEigenvalue}\left(A\right) = \operatorname{sInf}\left(\operatorname{toSet}\left(\operatorname{eigenvalues}\left(A\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.leastEigenvalue` (`✓ std3`).

*Citation.* A. Kumari; S. Adhikari (2022). *Structured negativity: A physically realizable measure of entanglement based on structural physical approximation*. DOI: [10.48550/arXiv.2209.03909](https://doi.org/10.48550/arXiv.2209.03909). URL: <https://arxiv.org/abs/2209.03909v1>.

*Commentary.*

The source states (p. 3): 'where λ_min(ρ̃) denote the minimum eigenvalue of ρ̃.' The least real eigenvalue is the infimum of the underlying set of the eigenvalue multiset. For Hermitian matrices of positive dimension the set is finite and nonempty, so this is its minimum. Multiplicity is irrelevant for the minimum.

**Definition 1.8 (Structured negativity).**

$$\forall d:\mathbb{N}, \forall rho:\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{structuredNegativity}\left(d, rho\right) = (\operatorname{val}\left(d\right):\mathbb{R}) \cdot ((\operatorname{val}\left(d\right):\mathbb{R})^{3} + 1) \cdot \operatorname{max}\left(\frac{(\operatorname{val}\left(d\right):\mathbb{R})}{(\operatorname{val}\left(d\right):\mathbb{R})^{3} + 1} - \operatorname{leastEigenvalue}\left(\operatorname{spaPT}\left(rho\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.structuredNegativity` (`✓ std3`).

*Citation.* A. Kumari; S. Adhikari (2022). *Structured negativity: A physically realizable measure of entanglement based on structural physical approximation*. DOI: [10.48550/arXiv.2209.03909](https://doi.org/10.48550/arXiv.2209.03909). URL: <https://arxiv.org/abs/2209.03909v1>.

*Commentary.*

Equation (9), p. 3: 'N_S(ρ) = K.max{d/(d^3+1) − λ_min(ρ̃),0} where K = d(d^3+1).' Lean uses precisely this scale, threshold and maximum, with leastEigenvalue applied to spaPT. All divisions in this formula are real divisions.

**Definition 1.9 (The Kumari–Adhikari coincidence conjecture).**

$$claim \Leftrightarrow (\forall d:\mathbb{N}, \forall rho:\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right), (2 \le d) \Rightarrow \left((\operatorname{IsDensity}\left(rho\right)) \Rightarrow \left((\operatorname{negCount}\left(\operatorname{partialTransposeB}\left(rho\right)\right) = \operatorname{natDiv}\left(d \cdot (d - 1), 2\right)) \Rightarrow \operatorname{negativity}\left(d, rho\right) = \operatorname{structuredNegativity}\left(d, rho\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.claim` (`✓ std3`).

*Citation.* A. Kumari; S. Adhikari (2022). *Structured negativity: A physically realizable measure of entanglement based on structural physical approximation*. DOI: [10.48550/arXiv.2209.03909](https://doi.org/10.48550/arXiv.2209.03909). URL: <https://arxiv.org/abs/2209.03909v1>.

*Commentary.*

Abstract, p. 1: 'For d ⊗ d dimensional state, we conjecture from the result obtained in this work that negativity coincide with the structured negativity when the number of negative eigenvalues of the partially transposed matrix is equal to d(d−1)/2.' Conclusion, p. 7: 'Thus, we conjecture that the negativity and structured negativity coincides when q=d(d−1)/2.' Encoding: d is a natural number at least two, rho is an arbitrary density matrix on C^d ⊗ C^d, and q is negCount(partialTransposeB(rho)). natDiv denotes natural-number division, equal to the floor of the nonnegative quotient; subtraction in d−1 here is natural subtraction. The conclusion equates the two real quantities with the normalizations in equations (6) and (9).

**Theorem 1.10 (Refutation by a pure 3⊗3 state).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kumari; S. Adhikari (2022). *Structured negativity: A physically realizable measure of entanglement based on structural physical approximation*. DOI: [10.48550/arXiv.2209.03909](https://doi.org/10.48550/arXiv.2209.03909). URL: <https://arxiv.org/abs/2209.03909v1>.

*Commentary.*

Take ψ=(|00⟩+2|11⟩+2|22⟩)/3 and ρ=|ψ⟩⟨ψ|. The partial transpose is Hermitian with eigenvalue multiset {1/9,2/9,2/9,−2/9,4/9,4/9,−2/9,−4/9,4/9}. Thus q=3=3(3−1)/2 and N=8/9. Its SPA has eigenvalues {7/63,29/252,29/252,25/252,31/252,31/252,25/252,23/252,31/252}, with minimum 23/252, giving N_S=84 max{3/28−23/252,0}=4/3. The eigenvalues follow from an explicit rational change of basis: diagonal coordinates use |ii⟩, and each off-diagonal pair uses |ij⟩+|ji⟩ and |ij⟩−|ji⟩. Similarity preserves the characteristic polynomial; Mathlib's spectral theorem relates its roots to the Hermitian eigenvalue multiset. Since 8/9 differs from 4/3, the conjecture fails.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.IsDensity`
- Truth anchor: `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.eigenvalues`
- Truth anchor: `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.leastEigenvalue`
- Truth anchor: `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.negCount`
- Truth anchor: `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.negativity`
- Truth anchor: `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.partialTransposeB`
- Truth anchor: `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.spaPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.structuredNegativity`
