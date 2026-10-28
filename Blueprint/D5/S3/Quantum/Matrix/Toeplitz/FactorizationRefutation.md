# A field of definition obstruction to uniform Toeplitz factorization

## Abstract

No fixed number of ordinary Toeplitz factors suffices after a free invertible left multiplier.

**Definition 1.1 (Ordinary Toeplitz matrices).**

$$\forall (n: \mathbb{N}), (\forall (T: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((\operatorname{IsOrdinaryToeplitz}\left(T\right)) \Leftrightarrow (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(n\right)), (\forall (hi: \operatorname{Fin.val}\left(i\right) + 1 < n), (\forall (hj: \operatorname{Fin.val}\left(j\right) + 1 < n), (T\left(i, j\right) = T\left(\operatorname{Fin.mk}\left(\operatorname{Fin.val}\left(i\right) + 1, hi\right), \operatorname{Fin.mk}\left(\operatorname{Fin.val}\left(j\right) + 1, hj\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.IsOrdinaryToeplitz` (`✓ std3`).

*Citation.* Ignacio García-Marco, Irene Márquez-Corbella, Daniel Seco (2025). *On the minimum number of Toeplitz factors of a matrix*. DOI: [10.48550/arXiv.2506.16432](https://doi.org/10.48550/arXiv.2506.16432). URL: <https://arxiv.org/abs/2506.16432v1>.

*Commentary.*

The first index is the row, and Fin n uses indices 0 through n − 1. The definition requires equality between each entry and its adjacent southeast entry whenever both successor indices exist. Fin.val takes a finite index to its natural value; Fin.mk constructs an index from its value and a proof that it is below n. This is equation (1) of the source, with its indices shifted down by one. The predicate also defines the empty-size case, although the factorization assertion only uses positive sizes.

**Definition 1.2 (The complete uniform factorization assertion).**

$$(\operatorname{claim}\left(\right)) \Leftrightarrow (\exists (C: \mathbb{N}), ((0 < C) \land (\forall (n: \mathbb{N}), ((0 < n) \Rightarrow (\forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\exists (P: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\exists (T: (\operatorname{Fin}\left(C\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right))), ((\operatorname{IsUnit}\left(P\right)) \land ((\forall (k: \operatorname{Fin}\left(C\right)), (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(n\right)), (\forall (hi: \operatorname{Fin.val}\left(i\right) + 1 < n), (\forall (hj: \operatorname{Fin.val}\left(j\right) + 1 < n), (T\left(k\right)\left(i, j\right) = T\left(k\right)\left(\operatorname{Fin.mk}\left(\operatorname{Fin.val}\left(i\right) + 1, hi\right), \operatorname{Fin.mk}\left(\operatorname{Fin.val}\left(j\right) + 1, hj\right)\right))))))) \land (M = P \cdot \operatorname{List.prod}\left(\operatorname{List.ofFn}\left(T\right)\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.claim` (`✓ std3`).

*Citation.* Ignacio García-Marco, Irene Márquez-Corbella, Daniel Seco (2025). *On the minimum number of Toeplitz factors of a matrix*. DOI: [10.48550/arXiv.2506.16432](https://doi.org/10.48550/arXiv.2506.16432). URL: <https://arxiv.org/abs/2506.16432v1>.

*Commentary.*

Conjecture 5.1 in Section 5.2 of García-Marco, Márquez-Corbella and Seco, arXiv:2506.16432v1, asserts one positive finite factor count C that works for every positive dimension n and every complex matrix M, including singular matrices. IsUnit P is genuine invertibility of the square complex matrix P. Its position is on the left.

The function T is an ordered C-tuple of matrices of exactly the same size as M. List.ofFn T lists them in increasing Fin.val order. List.prod multiplies a list by the recursion prod([]) = 1 and prod(A :: L) = A * prod(L). Thus the displayed product is ordered; no commutativity of matrix multiplication is assumed. The ordinary Toeplitz condition is expanded for every factor. The identity is Toeplitz, so allowing at most C factors gives the same assertion by padding.

All matrix products use the usual finite entry sum, with complex multiplication and addition:$\forall (n: \mathbb{N}), (\forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\forall (B: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(n\right)), (\left(A \cdot B\right)\left(i, j\right) = \sum_{(k: \operatorname{Fin}\left(n\right))} A\left(i, k\right) \cdot B\left(k, j\right))))))$

**Theorem 1.3 (The uniform factorization assertion is false).**

$$\neg (\exists (C: \mathbb{N}), ((0 < C) \land (\forall (n: \mathbb{N}), ((0 < n) \Rightarrow (\forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\exists (P: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\exists (T: (\operatorname{Fin}\left(C\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right))), ((\operatorname{IsUnit}\left(P\right)) \land ((\forall (k: \operatorname{Fin}\left(C\right)), (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(n\right)), (\forall (hi: \operatorname{Fin.val}\left(i\right) + 1 < n), (\forall (hj: \operatorname{Fin.val}\left(j\right) + 1 < n), (T\left(k\right)\left(i, j\right) = T\left(k\right)\left(\operatorname{Fin.mk}\left(\operatorname{Fin.val}\left(i\right) + 1, hi\right), \operatorname{Fin.mk}\left(\operatorname{Fin.val}\left(j\right) + 1, hj\right)\right))))))) \land (M = P \cdot \operatorname{List.prod}\left(\operatorname{List.ofFn}\left(T\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ignacio García-Marco, Irene Márquez-Corbella, Daniel Seco (2025). *On the minimum number of Toeplitz factors of a matrix*. DOI: [10.48550/arXiv.2506.16432](https://doi.org/10.48550/arXiv.2506.16432). URL: <https://arxiv.org/abs/2506.16432v1>.

*Commentary.*

Fix an arbitrary positive C. Set r = 4C and n = 2r = 8C, choose r squared complex entries algebraically independent over the rationals, and arrange them as a matrix X. Such finite independent families exist because a transcendence basis of the uncountable field of complex numbers over the countable rational field cannot be finite. Let M be the block matrix with top blocks I and X and bottom blocks zero. These choices precede any proposed factors.

Suppose M = P N, where P is invertible and N is the ordered product of C ordinary Toeplitz factors. Adjacent-diagonal equality gives a coefficient function of the integer row-minus-column offset, using LiCurvatureCriterion.toeplitzMatrix. Only 2n − 1 offsets occur. Let K be the single intermediate field of the complex numbers generated over the rationals by all C(2n − 1) coefficients. Every entry of every factor and of N lies in K, since matrix multiplication uses finite sums and products. N itself need not be Toeplitz.

From N = P inverse times M, every actual row of N lies in the graph of u ↦ uX. From M = PN, the first-r-coordinate projections of the actual rows of N span the full complex r-dimensional row space. LinearRado.exists_nonsingular_rows selects r actual rows whose first blocks form a nonsingular square matrix A. Their second blocks form B, and graph membership gives B = AX. Both A and B have entries in K; no arbitrary complex row combinations are used as K-valued coordinates.

The inclusion K into the complex numbers preserves determinants. The nonzero complex determinant therefore gives a nonzero determinant over K. Inverting A over K yields X = A inverse times B after inclusion. All r squared independent entries of X consequently lie in K, and their independence transfers along the injective rational algebra map. Hence r squared is at most the transcendence degree of K over the rationals.

For the internal copies of the generating coefficients, their intermediate-field adjoin is all of K. That field adjoin is algebraic over their algebra adjoin, and algebraicity transports to K. Thus its transcendence degree is at most C(2n − 1). But C(2n − 1) + C = r squared, contradicting C > 0. This excludes every proposed positive uniform C. The argument uses no coefficient of P in the parameter count.

The separately printed numerical consequence concerning Toep_n and Toep_n^Inv remains unresolved here. Failure of this factorization assertion does not establish an unbounded difference of those two global Toeplitz numbers. Conjectures 5.2 and 5.3 are separate statements.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.IsOrdinaryToeplitz`
- Truth anchor: `D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.result`
- Dependency: [D5/S3/Combinatorics/Matroids/LinearRado](../../../Combinatorics/Matroids/LinearRado.md)
- Dependency: [D5/S3/Weil/TestFunctions/LiCurvatureCriterion](../../../Weil/TestFunctions/LiCurvatureCriterion.md)
