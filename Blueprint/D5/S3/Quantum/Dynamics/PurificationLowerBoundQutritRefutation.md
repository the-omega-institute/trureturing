# The purification lower bound fails for a qutrit

## Abstract

A positive definite qutrit state has greater time-dependent purification spread complexity than operator Krylov complexity.

The Krylov vectors are obtained by normalized Gram-Schmidt orthogonalization of successive powers of a complex continuous linear map. Matrix coordinates use D5.S3.Quantum.Matrix.CartesianVariance.vectorize, whose (i,j) coordinate is the (i,j) matrix entry. Its Euclidean inner product is the Hilbert-Schmidt inner product on matrices. Named objects retain their Lean namespaces. Complex.ofReal denotes the real-to-complex inclusion, and scalar multiplication uses the complex scalar action.

**Definition 1.1 (Normalized Krylov vectors).**

$$\forall (E: \operatorname{Type}), ([\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, E\right)] , (\forall (L: E \to_{L[\mathbb{C}]} E), (\forall (v: E), (\forall (n: \mathbb{N}), (\operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.krylovVector}\left(L, v, n\right) = \operatorname{InnerProductSpace.gramSchmidtNormed}\left(\mathbb{C}, (\lambda (k: \mathbb{N}) \mapsto (\left((L)^{k}\right)\left(((\operatorname{Complex.ofReal}\left(\left\lVert v \right\rVert\right))^{-1}) \cdot (v)\right)): \mathbb{N} \to E), n\right))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.krylovVector` (`✓ std3`).

*Citation.* Rathindra Nath Das, Takato Mori (2026). *Krylov complexity of purification*. DOI: [10.1103/qgcx-wxpd](https://doi.org/10.1103/qgcx-wxpd). URL: <https://arxiv.org/abs/2408.00826v4>.

*Commentary.*

Supplemental equation (S.1) gives the sequence of powers of the generator applied to the initial state. InnerProductSpace.gramSchmidtNormed orthogonalizes this sequence after normalizing its seed. For a Hermitian generator, the nonzero vectors agree with the Lanczos basis up to phases. Zero residuals give zero vectors, and the zero seed is included in the definition.

**Definition 1.2 (The mean Krylov index).**

$$\forall (E: \operatorname{Type}), ([\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, E\right)] [\operatorname{FiniteDimensional}\left(\mathbb{C}, E\right)] , (\forall (L: E \to_{L[\mathbb{C}]} E), (\forall (v: E), (\forall (t: \mathbb{R}), (\operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.spreadComplexity}\left(L, v, t\right) = \sum_{(n: \operatorname{Fin}\left(\operatorname{Module.finrank}\left(\mathbb{C}, E\right)\right))} (((\operatorname{Fin.val}\left(n\right): \mathbb{R})) \cdot (\operatorname{Complex.normSq}\left(\operatorname{inner}\left(\mathbb{C}, \operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.krylovVector}\left(L, v, \operatorname{Fin.val}\left(n\right)\right), \operatorname{NormedSpace.exp}\left(((-(\operatorname{Complex.ofReal}\left(t\right))) \cdot (\operatorname{Complex.I})) \cdot (L)\right)\left(((\operatorname{Complex.ofReal}\left(\left\lVert v \right\rVert\right))^{-1}) \cdot (v)\right)\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.spreadComplexity` (`✓ std3`).

*Citation.* Rathindra Nath Das, Takato Mori (2026). *Krylov complexity of purification*. DOI: [10.1103/qgcx-wxpd](https://doi.org/10.1103/qgcx-wxpd). URL: <https://arxiv.org/abs/2408.00826v4>.

*Commentary.*

Supplemental equations (S.2)-(S.4) express spread complexity as the mean basis index weighted by the squared moduli of the evolved amplitudes. The sum here ranges over Fin (Module.finrank Complex E); vectors beyond the Krylov chain contribute zero. NormedSpace.exp gives the evolution exp(-itL) of the normalized seed. This definition allows every real t and every complex continuous linear map L.

**Definition 1.3 (The matrix of the commutator).**

$$\forall (d: \mathbb{N}), (\forall (H: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.liouvillianMatrix}\left(H\right) = (\operatorname{Matrix.kronecker}\left(H, (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))\right)) - (\operatorname{Matrix.kronecker}\left((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \operatorname{Matrix.transpose}\left(H\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.liouvillianMatrix` (`✓ std3`).

*Citation.* Rathindra Nath Das, Takato Mori (2026). *Krylov complexity of purification*. DOI: [10.1103/qgcx-wxpd](https://doi.org/10.1103/qgcx-wxpd). URL: <https://arxiv.org/abs/2408.00826v4>.

*Commentary.*

Supplemental equations (S.5)-(S.7) use the commutator with H as the operator generator. In system-first matrix coordinates its matrix is H tensor 1 minus 1 tensor the transpose of H. Matrix.kronecker denotes the Kronecker product, and each 1 is the identity matrix on Fin d.

**Definition 1.4 (The generator on the doubled Hilbert space).**

$$\forall (d: \mathbb{N}), (\forall (H: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.liouvillian}\left(H\right): \operatorname{EuclideanSpace}\left(\mathbb{C}, (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right) \to_{L[\mathbb{C}]} \operatorname{EuclideanSpace}\left(\mathbb{C}, (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)) = \operatorname{Matrix.toEuclideanCLM}\left(\operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.liouvillianMatrix}\left(H\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.liouvillian` (`✓ std3`).

*Citation.* Rathindra Nath Das, Takato Mori (2026). *Krylov complexity of purification*. DOI: [10.1103/qgcx-wxpd](https://doi.org/10.1103/qgcx-wxpd). URL: <https://arxiv.org/abs/2408.00826v4>.

*Commentary.*

Matrix.toEuclideanCLM turns the commutator matrix into a continuous complex linear map on EuclideanSpace Complex (Fin d times Fin d). Vectorization turns [H,A] into the action of H tensor 1 minus 1 tensor the transpose of H on the vectorized A. For Hermitian H, its transpose is its entrywise complex conjugate H*. Thus exp(-itL) evolves the canonical purification by U_t tensor U_t*, with U_t = exp(-itH), as in equation (2). Here the star in H* and U_t* denotes entrywise complex conjugation.

**Definition 1.5 (The canonical purification).**

$$\forall (d: \mathbb{N}), (\forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.canonicalKet}\left(rho\right) = \operatorname{D5.S3.Quantum.Matrix.CartesianVariance.vectorize}\left(d, \operatorname{CFC.sqrt}\left(rho\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.canonicalKet` (`✓ std3`).

*Citation.* Rathindra Nath Das, Takato Mori (2026). *Krylov complexity of purification*. DOI: [10.1103/qgcx-wxpd](https://doi.org/10.1103/qgcx-wxpd). URL: <https://arxiv.org/abs/2408.00826v4>.

*Commentary.*

The purification definition before equation (1) gives, for full-rank density matrices, the canonical vector with (i,j) coefficient (sqrt rho)_{ij}. CFC.sqrt supplies the matrix square root, and D5.S3.Quantum.Matrix.CartesianVariance.vectorize places its entries in the doubled Hilbert space. For a positive semidefinite matrix of trace one, this vector has norm one and its reduced density matrix is rho. The displayed definition itself is made for every complex square matrix.

**Definition 1.6 (Operator Krylov complexity).**

$$\forall (d: \mathbb{N}), (\forall (H: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (t: \mathbb{R}), (\operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.operatorComplexity}\left(H, rho, t\right) = \operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.spreadComplexity}\left(\operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.liouvillian}\left(H\right), \operatorname{D5.S3.Quantum.Matrix.CartesianVariance.vectorize}\left(d, rho\right), t\right)))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.operatorComplexity` (`✓ std3`).

*Citation.* Rathindra Nath Das, Takato Mori (2026). *Krylov complexity of purification*. DOI: [10.1103/qgcx-wxpd](https://doi.org/10.1103/qgcx-wxpd). URL: <https://arxiv.org/abs/2408.00826v4>.

*Commentary.*

Supplemental equations (S.5)-(S.11) define operator complexity using the commutator generator and the Hilbert-Schmidt-normalized initial operator. Vectorizing rho gives exactly that Hilbert-space calculation. For Hermitian rho and H, reversing the Heisenberg time sign leaves the squared Krylov amplitudes unchanged.

**Definition 1.7 (Spread complexity of the time-dependent purification).**

$$\forall (d: \mathbb{N}), (\forall (H: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (t: \mathbb{R}), (\operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.purificationComplexity}\left(H, rho, t\right) = \operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.spreadComplexity}\left(\operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.liouvillian}\left(H\right), \operatorname{D5.S3.Quantum.Matrix.CartesianVariance.vectorize}\left(d, \operatorname{CFC.sqrt}\left(rho\right)\right), t\right)))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.purificationComplexity` (`✓ std3`).

*Citation.* Rathindra Nath Das, Takato Mori (2026). *Krylov complexity of purification*. DOI: [10.1103/qgcx-wxpd](https://doi.org/10.1103/qgcx-wxpd). URL: <https://arxiv.org/abs/2408.00826v4>.

*Commentary.*

Equation (2) evolves the canonical purification with U_t tensor U_t*. Applying the same commutator generator to the vectorized CFC.sqrt rho therefore gives its spread complexity from supplemental equation (S.4). For density matrices the initial purification already has norm one.

**Definition 1.8 (The left inequality of equation (4)).**

$$(\operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.claim}) \Leftrightarrow (\forall (d: \mathbb{N}), (\forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (H: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (t: \mathbb{R}), ((\operatorname{Matrix.PosDef}\left(rho\right)) \Rightarrow ((\operatorname{Matrix.trace}\left(rho\right) = 1) \Rightarrow ((\operatorname{Matrix.IsHermitian}\left(H\right)) \Rightarrow ((0 \le t) \Rightarrow (\operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.purificationComplexity}\left(H, rho, t\right) \le \operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.operatorComplexity}\left(H, rho, t\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.claim` (`✓ std3`).

*Citation.* Rathindra Nath Das, Takato Mori (2026). *Krylov complexity of purification*. DOI: [10.1103/qgcx-wxpd](https://doi.org/10.1103/qgcx-wxpd). URL: <https://arxiv.org/abs/2408.00826v4>.

*Commentary.*

The left inequality of equation (4) asserts that the spread complexity of the time-dependent purification is bounded above by the mixed state's operator complexity. The displayed statement includes every dimension, positive definite rho of trace one, Hermitian H, and nonnegative real time. Positive definiteness restricts the source's density matrices to full rank, where its initial purification is the canonical one. A counterexample in this restricted class also disproves the source's inequality for all density matrices.

**Theorem 1.9 (A positive definite qutrit counterexample).**

$$\neg (\operatorname{D5.S3.Quantum.Dynamics.PurificationLowerBoundQutritRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/das-mori-2026-purification-lower-bound-refutation` (refuted) by `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"das-mori-2026-purification-lower-bound-refutation","declaration_gid":"D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Rathindra Nath Das, Takato Mori (2026). *Krylov complexity of purification*. DOI: [10.1103/qgcx-wxpd](https://doi.org/10.1103/qgcx-wxpd). URL: <https://arxiv.org/abs/2408.00826v4>.

*Commentary.*

Take rho = diag(1,4,16)/21, H = [[2,1,0],[1,2,0],[0,0,4]], and t = pi/2. The state is positive definite with trace one, and H is Hermitian. Its canonical purification is (|00> + 2|11> + 4|22>)/sqrt(21).

Both Krylov chains have length three. The squared successive off-diagonal Lanczos coefficients are (6/91,358/91) for the normalized vectorized density matrix and (2/21,82/21) for its canonical purification. On each cyclic subspace L cubed equals 4L, so at t = pi/2 the evolved seed is its initial value minus one half of L squared applied to it. The index-one amplitude vanishes, and the index-zero amplitudes are respectively 88/91 and 20/21.

Consequently C_K = 2(1-(88/91)^2) = 1074/8281 and C_S = 2(1-(20/21)^2) = 82/441. Thus C_K < C_S, with C_S-C_K = 4192/74529 > 0, contradicting the left inequality of equation (4).

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.canonicalKet`
- Truth anchor: `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.krylovVector`
- Truth anchor: `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.liouvillian`
- Truth anchor: `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.liouvillianMatrix`
- Truth anchor: `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.operatorComplexity`
- Truth anchor: `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.purificationComplexity`
- Truth anchor: `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.result`
- Truth anchor: `D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.spreadComplexity`
- Dependency: [D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings](../QuantumChannels/QubitWassersteinCouplings.md)
