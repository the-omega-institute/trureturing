# Functional calculus in a positive corner

## Abstract

Functional calculus in a positive corner

For every natural number n, MatrixMonotone(n,f) means that cfc(f,X) <= cfc(f,Y) for all positive semidefinite complex n by n matrices X <= Y. The calculus is the actual finite spectral functional calculus, and ReTr is the unnormalized real trace. zeroExtendedRatio(f) sends t to t/f(t), using total division, so its value at zero is zero. No continuity of this quotient at zero is implicit in the notation. Zero dimensions and singular noncommuting matrices are included wherever positivity is semidefinite. For a complete complex Hilbert space H, L(H) denotes continuous complex-linear endomorphisms, and corner is projection onto the first summand followed by inclusion. For a 2n by 2n matrix, firstCorner selects the coordinates finProdFinEquiv(0,i).

**Theorem 1.1 (One doubled Hilbert space suffices).**

$$\forall H \in \operatorname{CompleteComplexHilbertType}\left(\right), f \in \mathbb{R} \to \mathbb{R}, X \in \operatorname{L}\left(\operatorname{HSum}\left(H\right)\right),\; ((\operatorname{ContinuousOn}\left(f, \operatorname{Ici}\left(0\right)\right)) \land ((\operatorname{OperatorMonotone}\left(\operatorname{L}\left(\operatorname{HSum}\left(H\right)\right), f\right)) \land (0 \le X))) \Rightarrow (\operatorname{corner}\left(\operatorname{cfc}\left(f, X\right)\right) \le \operatorname{cfc}\left(f, \operatorname{corner}\left(X\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/FiniteOrderCompression.monotone_double_space_corner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be any complete complex Hilbert space and f be continuous on the nonnegative half-line. Monotonicity of f only on L(H direct sum H) implies that the first corner of f(X) is at most f of the first corner of every positive X. No sign condition on f(0) is needed. For each positive epsilon, a positive block diagonal operator dominates X with first block corner(X)+epsilon I. Its second block can depend on epsilon. Monotonicity and diagonal functional calculus give the perturbed bound; closedness of order and continuity remove epsilon.

**Theorem 1.2 (The first corner at finite order 2n).**

$$\forall n \in \mathbb{N}, f \in \mathbb{R} \to \mathbb{R}, X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2 \cdot n\right), \operatorname{Fin}\left(2 \cdot n\right), \mathbb{C}\right),\; ((\operatorname{ContinuousOn}\left(f, \operatorname{Ici}\left(0\right)\right)) \land ((\operatorname{MatrixMonotone}\left(2 \cdot n, f\right)) \land (\operatorname{PosSemidef}\left(X\right)))) \Rightarrow (\operatorname{firstCorner}\left(\operatorname{cfc}\left(f, X\right)\right) \le \operatorname{cfc}\left(f, \operatorname{firstCorner}\left(X\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/FiniteOrderCompression.matrix_monotone_corner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose an orthonormal coordinate equivalence between the doubled Euclidean Hilbert space and matrices indexed by Fin(2n). The equivalence preserves positivity, order and real functional calculus, so monotonicity at exactly order 2n supplies the doubled Hilbert-space hypothesis. The empty coordinate space is handled directly. Continuity is required on the closed nonnegative half-line; there is no positivity assumption on f(0).

**Theorem 1.3 (Contraction Jensen at doubled finite order).**

$$\forall n \in \mathbb{N}, f \in \mathbb{R} \to \mathbb{R}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; ((\operatorname{ContinuousOn}\left(f, \operatorname{Ici}\left(0\right)\right)) \land ((0 \le \operatorname{apply}\left(f, 0\right)) \land ((\operatorname{MatrixMonotone}\left(2 \cdot n, f\right)) \land ((\operatorname{PosSemidef}\left(A\right)) \land (C^{*} \cdot C \le 1))))) \Rightarrow (C^{*} \cdot \operatorname{cfc}\left(f, A\right) \cdot C \le \operatorname{cfc}\left(f, C^{*} \cdot A \cdot C\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/FiniteOrderCompression.matrix_monotone_contraction` (`✓ std3`). ∎

*Citation.* Dinh Trung Hoa; Hiroyuki Osaka; Ho Minh Toan (2012). *On generalized Powers-Størmer's Inequality*. DOI: [10.48550/arXiv.1204.6665](https://doi.org/10.48550/arXiv.1204.6665). URL: <https://arxiv.org/html/1204.6665v1>.

*Commentary.*

For every n, positive semidefinite A and contraction C, continuity of f, f(0)>=0 and matrix monotonicity at order 2n give C* f(A) C <= f(C* A C). A unitary dilation of C identifies this compression with the first corner of a conjugated positive block. The second block of f(diag(A,0)) contributes a nonnegative term, which may be discarded. This is the finite-order contraction argument of Hoa, Osaka and Toan, Lemma 2.1.

**Theorem 1.4 (Restriction from doubled order).**

$$\forall n \in \mathbb{N}, f \in \mathbb{R} \to \mathbb{R}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; ((\operatorname{MatrixMonotone}\left(2 \cdot n, f\right)) \land ((\operatorname{PosSemidef}\left(A\right)) \land ((\operatorname{PosSemidef}\left(B\right)) \land (A \le B)))) \Rightarrow (\operatorname{cfc}\left(f, A\right) \le \operatorname{cfc}\left(f, B\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/FiniteOrderCompression.matrix_monotone_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embed both n by n matrices as the first blocks of matrices on the direct sum. Congruence preserves their order, monotonicity applies after the coordinate equivalence, and rectangular spectral intertwining recovers f(A) and f(B) in the first corner. The restriction requires neither continuity nor a sign condition on f.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/FiniteOrderCompression.matrix_monotone_contraction`
- Truth anchor: `D5/S3/Quantum/Lieb/FiniteOrderCompression.matrix_monotone_corner`
- Truth anchor: `D5/S3/Quantum/Lieb/FiniteOrderCompression.matrix_monotone_restrict`
- Truth anchor: `D5/S3/Quantum/Lieb/FiniteOrderCompression.monotone_double_space_corner`
- Dependency: [D5/S3/Quantum/Lieb/MonotoneBlockConcavity](MonotoneBlockConcavity.md)
- Dependency: [D5/S3/Quantum/Matrix/Spectral/IsometricCalculus](../Matrix/Spectral/IsometricCalculus.md)
