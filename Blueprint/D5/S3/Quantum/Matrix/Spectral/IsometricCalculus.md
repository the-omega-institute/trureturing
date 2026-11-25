# Isometries, functional calculus and unitary dilations

## Abstract

Isometries, functional calculus and unitary dilations

FiniteType denotes an arbitrary finite type with decidable equality. All matrices use complex scalars. Adjoint is conjugate transpose. Functional calculus is defined by the finite spectrum, so an arbitrary real function is continuous on the required spectrum. The two rectangular results are the congruence and spectral intertwining results for positive-map Jensen. The dilation is the orthonormal-basis extension construction for contractions.

**Theorem 1.1 (Rectangular congruence preserves order).**

$$\forall n \in FiniteType, m \in FiniteType, A \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right), B \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right), V \in \operatorname{Matrix}\left(n, m, \mathbb{C}\right),\; (A \le B) \Rightarrow (V^{*} \cdot A \cdot V \le V^{*} \cdot B \cdot V)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Spectral/IsometricCalculus.congruence_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite coordinate types n and m, A <= B implies V* A V <= V* B V for every rectangular V. Apply positive-semidefinite congruence to B-A.

**Theorem 1.2 (Rectangular spectral intertwining).**

$$\forall n \in FiniteType, m \in FiniteType, A \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right), B \in \operatorname{Matrix}\left(m, m, \mathbb{C}\right), V \in \operatorname{Matrix}\left(n, m, \mathbb{C}\right), f \in \mathbb{R} \to \mathbb{R},\; ((\operatorname{IsHermitian}\left(A\right)) \land ((\operatorname{IsHermitian}\left(B\right)) \land (A \cdot V = V \cdot B))) \Rightarrow (\operatorname{cfc}\left(f, A\right) \cdot V = V \cdot \operatorname{cfc}\left(f, B\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Spectral/IsometricCalculus.cfc_intertwining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If Hermitian A and B satisfy A V=V B, then f(A)V=V f(B) for every real function f. In eigenvector coordinates, each coefficient of V is annihilated by the difference of the corresponding eigenvalues. Equal eigenvalues give equal function values; unequal ones force that coefficient to vanish.

**Theorem 1.3 (A contraction is a corner of a unitary).**

$$\forall n \in \mathbb{N}, C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; (\operatorname{PosSemidef}\left(1 - C^{*} \cdot C\right)) \Rightarrow (\exists U \in \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right), \mathbb{C}\right),\; (\operatorname{Unitary}\left(U\right)) \land (\forall i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{entry}\left(U, \operatorname{inl}\left(i\right), \operatorname{inl}\left(j\right)\right) = \operatorname{entry}\left(C, i, j\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Spectral/IsometricCalculus.exists_unitary_dilation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex n by n C with I-C* C positive semidefinite, there is a unitary U on Fin n direct sum Fin n whose upper-left block is C. Stack the columns of C above those of sqrt(I-C* C). Their Gram matrix is I, so the resulting orthonormal family extends to an orthonormal basis. The change-of-basis matrix gives U, including the empty case n=0.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/Spectral/IsometricCalculus.cfc_intertwining`
- Truth anchor: `D5/S3/Quantum/Matrix/Spectral/IsometricCalculus.congruence_mono`
- Truth anchor: `D5/S3/Quantum/Matrix/Spectral/IsometricCalculus.exists_unitary_dilation`
