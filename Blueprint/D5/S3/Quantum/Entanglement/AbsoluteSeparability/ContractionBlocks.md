# Contraction decompositions and separable scalar shifts

## Abstract

Every finite complex Euclidean contraction has a rank-one phase decomposition with twice as many terms as its dimension. This decomposition makes the scalar shift mI + H separable for a Hermitian Euclidean contraction on a product of dimensions m and n.

**Theorem 1.1 (A finite rank-one phase decomposition).**

$$\forall (n : \mathbb{N}), \forall (C : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix}.\operatorname{PosSemidef}\left(1 - \operatorname{Matrix}.\operatorname{conjTranspose}\left(C\right) \cdot C\right)) \Rightarrow (\exists (a : \operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right) \to \operatorname{Fin}\left(n\right) \to \mathbb{C}), \exists (c : \operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right) \to \mathbb{C}), (\forall (r : \operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right)), \left\lVert c\left(r\right) \right\rVert = 1) \land ((\sum_{r : \operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right)} \operatorname{Matrix}.\operatorname{vecMulVec}\left(a\left(r\right), \operatorname{star}\left(a\left(r\right)\right)\right) = 1) \land (\sum_{r : \operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right)} c\left(r\right) \cdot \operatorname{Matrix}.\operatorname{vecMulVec}\left(a\left(r\right), \operatorname{star}\left(a\left(r\right)\right)\right) = C)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/ContractionBlocks.contraction_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vectors are indexed by Fin n ⊕ Fin n, including the empty family when n is zero. Their rank-one matrices sum to the identity, and multiplying them by scalars of modulus one reconstructs C. The square root of I − C* C supplies an orthonormal family whose first coordinates are the columns of C. Extending it to an orthonormal basis gives a unitary dilation. A unit scalar outside its finite spectrum permits a Hermitian Cayley transform; its spectral basis and inverse transform provide the phases. Restricting the vectors to the first n coordinates gives the stated decomposition.

**Theorem 1.2 (Separable middle rays).**

$$\forall (m : \mathbb{N}), \forall (n : \mathbb{N}), \forall (H : \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), \mathbb{C}\right)), (\operatorname{Matrix}.\operatorname{IsHermitian}\left(H\right)) \Rightarrow ((\forall (x : \operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right) \to \mathbb{C}), \left\lVert \operatorname{WithLp}.\operatorname{toLp}\left(2, \operatorname{Matrix}.\operatorname{mulVec}\left(H, x\right)\right) \right\rVert \le \left\lVert \operatorname{WithLp}.\operatorname{toLp}\left(2, x\right) \right\rVert) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Resource}.\operatorname{CompositeCones}.\operatorname{separableCone}\left((m : \mathbb{C}) \cdot 1 + H\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/ContractionBlocks.separableCone_scalar_add_of_opNorm_le_one` (`✓ std3`). ∎

*Citation.* Guillaume Aubrun, Kenneth R. Davidson, Alexander Müller-Hermes, Vern I. Paulsen and Mizanur Rahaman (2024). *Completely bounded norms of k-positive maps*. DOI: [10.1112/jlms.12936](https://doi.org/10.1112/jlms.12936). URL: <https://doi.org/10.1112/jlms.12936>.

*Commentary.*

Aubrun--Davidson--Muller-Hermes--Paulsen--Rahaman Theorem 3.7, printed page 9, gives d₁(M_n) = n. The formal scalar-shift statement is its dual form under separable and block-positive cone duality, with the factor labels exchanged. The theorem's proof uses a separable block operator with identity diagonal blocks and a scaled contraction off the diagonal. The bound here quantifies all complex coordinate vectors and takes the norm after WithLp.toLp 2, so both norms are Euclidean. The dimensions m and n may be zero; these cases give the zero matrix. Each diagonal block I + Hii is positive semidefinite. Each off-diagonal block Hij is a contraction; its phase decomposition expresses the two-by-two block with identity diagonal as a sum of Kronecker products of positive semidefinite rank-one matrices, the block-separability statement of Gurvits--Barnum Proposition 1, printed page 2. Embedding these blocks and adding the diagonal terms yields mI + H. The separable cone here means a finite sum of Kronecker products of positive semidefinite factors.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/ContractionBlocks.contraction_decomposition`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/ContractionBlocks.separableCone_scalar_add_of_opNorm_le_one`
