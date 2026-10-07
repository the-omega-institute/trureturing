# A qutrit obstruction to positive/CP factorization of the channel transpose

## Abstract

A unital qutrit measure-and-prepare channel has no factorization of its channel transpose through a positive outer filter and a completely positive inner filter. Nonnegative coefficients impose kernel constraints incompatible with the unital sum and the nonorthogonal state kernels.

**Remark 1.1 (Hermitian preservation).**

$$
\operatorname{IsHermitianPreserving}\left(M\right) \iff \forall X \in \operatorname{Matrix}\left(A, A, R\right),\; \operatorname{IsHermitian}\left(X\right) \Rightarrow \operatorname{IsHermitian}\left(M\left(X\right)\right)
$$

*Citation.* Alex Meiburg and Dennj Osele (2025). *Physlib QuantumInfo: unbundled channels, channel duals and Hermitian-matrix order*. URL: <https://github.com/leanprover-community/physlib/tree/6a09b2d1761a0d4430083045a247eb121d8da260>.

*Commentary.*

Let A and B be finite coordinate types and R an RCLike scalar field. MatrixMap(A,B,R) is the space of R-linear maps from square A matrices to square B matrices. A map preserves Hermitian matrices when every Hermitian input has a Hermitian output.

**Remark 1.2 (Positive maps preserve Hermitian matrices).**

$$
\forall M \in \operatorname{MatrixMap}\left(A, B, R\right),\; \operatorname{IsPositive}\left(M\right) \Rightarrow \operatorname{IsHermitianPreserving}\left(M\right)
$$

*Citation.* Alex Meiburg and Dennj Osele (2025). *Physlib QuantumInfo: unbundled channels, channel duals and Hermitian-matrix order*. URL: <https://github.com/leanprover-community/physlib/tree/6a09b2d1761a0d4430083045a247eb121d8da260>.

*Commentary.*

Let A and B be finite coordinate types and R an RCLike scalar field. Every Hermitian matrix is the difference of its positive and negative parts, both positive semidefinite. A positive linear map sends both parts to positive semidefinite matrices. Their difference is Hermitian.

**Theorem 1.3 (Complete positivity implies positivity).**

$$\forall M \in \operatorname{MatrixMap}\left(A, B, R\right),\; \operatorname{IsCompletelyPositive}\left(M\right) \Rightarrow \operatorname{IsPositive}\left(M\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.IsPositive` (`✓ std3`). ∎

*Citation.* Alex Meiburg and Dennj Osele (2025). *Physlib QuantumInfo: unbundled channels, channel duals and Hermitian-matrix order*. URL: <https://github.com/leanprover-community/physlib/tree/6a09b2d1761a0d4430083045a247eb121d8da260>.

*Commentary.*

Let A and B be finite coordinate types, with decidable equality on A, and let R be an RCLike scalar field. Complete positivity requires positivity after tensoring with the identity map on matrices of every finite size. At size one, the product coordinate types A times Fin 1 and B times Fin 1 identify with A and B. Restricting along those equivalences gives positivity of M itself.

**Remark 1.4 (The trace dual).**

$$
\operatorname{dual}\left(M\right) = tauA \circ \operatorname{inverse}\left(betaA\right) \circ Mvee \circ betaB \circ tauB
$$

*Citation.* Alex Meiburg and Dennj Osele (2025). *Physlib QuantumInfo: unbundled channels, channel duals and Hermitian-matrix order*. URL: <https://github.com/leanprover-community/physlib/tree/6a09b2d1761a0d4430083045a247eb121d8da260>.

*Commentary.*

For finite coordinate types A and B with decidable equality and a commutative ring R, dual M is an R-linear map from B matrices to A matrices. Let betaA and betaB be the standard matrix-basis equivalences with their R-linear dual spaces, and let Mvee be the algebraic dual map. Let tauA and tauB denote matrix transpose. Then dual(M)=tauA composed with betaA inverse, Mvee, betaB, and tauB. No complex conjugation occurs in this definition.

**Theorem 1.5 (Trace duality).**

$$\forall M \in \operatorname{MatrixMap}\left(A, B, R\right),\; \forall X \in \operatorname{Matrix}\left(A, A, R\right),\; \forall Y \in \operatorname{Matrix}\left(B, B, R\right),\; \operatorname{tr}\left(M\left(X\right) \cdot Y\right) = \operatorname{tr}\left(X \cdot \operatorname{dual}\left(M\right)\left(Y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.trace_eq` (`✓ std3`). ∎

*Citation.* Alex Meiburg and Dennj Osele (2025). *Physlib QuantumInfo: unbundled channels, channel duals and Hermitian-matrix order*. URL: <https://github.com/leanprover-community/physlib/tree/6a09b2d1761a0d4430083045a247eb121d8da260>.

*Commentary.*

Let A and B be finite coordinate types with decidable equality, R a commutative ring, and M an R-linear map from A matrices to B matrices. For every input X and output test matrix Y, tr(M(X)Y)=tr(X dual(M)(Y)). In standard coordinates, the pairing with the transposed matrix is exactly the standard-basis dual pairing. The two transposes in the definition convert that coordinate pairing into the trace pairing.

**Remark 1.6 (The dual preserves Hermitian matrices).**

$$
\forall M \in \operatorname{MatrixMap}\left(A, B, complex\right),\; \operatorname{IsHermitianPreserving}\left(M\right) \Rightarrow \operatorname{IsHermitianPreserving}\left(\operatorname{dual}\left(M\right)\right)
$$

*Citation.* Alex Meiburg and Dennj Osele (2025). *Physlib QuantumInfo: unbundled channels, channel duals and Hermitian-matrix order*. URL: <https://github.com/leanprover-community/physlib/tree/6a09b2d1761a0d4430083045a247eb121d8da260>.

*Commentary.*

Let A and B be finite coordinate types with decidable equality. For complex matrices, a Hermitian-preserving linear map commutes with conjugate transpose, by decomposing a matrix into its real and imaginary self-adjoint parts. Trace duality and nondegeneracy of the trace pairing then show that its dual also preserves Hermitian matrices.

**Theorem 1.7 (Nonnegative trace of a product of positive matrices).**

$$\forall X \in \operatorname{Matrix}\left(n, n, R\right),\; \forall Y \in \operatorname{Matrix}\left(n, n, R\right),\; \left(\operatorname{PosSemidef}\left(X\right) \land \operatorname{PosSemidef}\left(Y\right)\right) \Rightarrow 0 \le \operatorname{tr}\left(X \cdot Y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.trace_mul_nonneg` (`✓ std3`). ∎

*Citation.* Alex Meiburg and Dennj Osele (2025). *Physlib QuantumInfo: unbundled channels, channel duals and Hermitian-matrix order*. URL: <https://github.com/leanprover-community/physlib/tree/6a09b2d1761a0d4430083045a247eb121d8da260>.

*Commentary.*

Let n be a finite coordinate type with decidable equality and R an RCLike field. For positive semidefinite n by n matrices X and Y over R, tr(XY) is nonnegative in the scalar star order. Factor Y as S adjoint times S. Cyclicity of trace identifies tr(XY) with tr(S X S adjoint), the trace of a positive semidefinite matrix. In the complex case, nonnegativity includes that this trace is real.

**Theorem 1.8 (The kernel of a sum of positive matrices).**

$$\forall f \in I \to \operatorname{HermitianMatrix}\left(n, R\right),\; \left(\forall i \in I,\; 0 \le f\left(i\right)\right) \Rightarrow \operatorname{ker}\left(\sum_{i \in I} f\left(i\right)\right) = \operatorname{intersection}\left(I, \operatorname{kernels}\left(f\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.ker_sum` (`✓ std3`). ∎

*Citation.* Alex Meiburg and Dennj Osele (2025). *Physlib QuantumInfo: unbundled channels, channel duals and Hermitian-matrix order*. URL: <https://github.com/leanprover-community/physlib/tree/6a09b2d1761a0d4430083045a247eb121d8da260>.

*Commentary.*

Let f be any family of Hermitian matrices over an RCLike field, indexed by a finite type I, on a finite coordinate type n with decidable equality. Assume each f(i) is nonnegative in the matrix order. The kernel of their sum, acting on Euclidean coordinate space, is the intersection of their kernels. For a vector killed by the sum, the sum of the nonnegative quadratic forms is zero. Every individual quadratic form is therefore zero, which is equivalent to membership in that matrix's kernel. The reverse inclusion follows by linearity. This identity also covers empty index and coordinate types. For the qutrit decomposition, apply it to f(j)=C(k,j) sigma(j) and cancel the nonzero coefficient C(k,j).

**Remark 1.9 (The dual of a positive map is positive).**

$$
\forall M \in \operatorname{MatrixMap}\left(A, B, complex\right),\; \operatorname{IsPositive}\left(M\right) \Rightarrow \operatorname{IsPositive}\left(\operatorname{dual}\left(M\right)\right)
$$

*Citation.* Alex Meiburg and Dennj Osele (2025). *Physlib QuantumInfo: unbundled channels, channel duals and Hermitian-matrix order*. URL: <https://github.com/leanprover-community/physlib/tree/6a09b2d1761a0d4430083045a247eb121d8da260>.

*Commentary.*

Let A and B be finite coordinate types with decidable equality and M a positive complex linear map from A matrices to B matrices. For a positive semidefinite Y, and any vector v, the quadratic form of dual(M)(Y) at v equals tr(M(v v adjoint)Y). Both factors on the right are positive semidefinite, so this scalar is nonnegative. Hermitian preservation of the dual supplies the other part of the positive semidefinite criterion.

Applied to a positive diagonal matrix unit, dual positivity and trace duality give positive semidefinite trace representatives of diagonal functionals.

**Definition 1.10 (The weak question at dimension three).**

$$claim \iff (\forall F : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), (\operatorname{UnitalChannel}\left(F\right)) \implies (\forall S : Type, [\operatorname{Fintype}\left(S\right)] \forall K : S \to \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), (F = \operatorname{ofKraus}\left(K, K\right)) \implies (\exists P : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), \exists E : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), (\operatorname{IsPositive}\left(P\right)) \land ((\operatorname{IsCompletelyPositive}\left(E\right)) \land (\operatorname{ofKraus}\left((\lambda i : S, \operatorname{transpose}\left(K\left(i\right)\right)), (\lambda i : S, \operatorname{transpose}\left(K\left(i\right)\right))\right) = P \circ F \circ E)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.claim` (`✓ std3`).

*Citation.* Samuel A. Márquez González (2026). *Feasibility Ordering of Entanglement-Source Placement for Qubit Channels*. DOI: [10.48550/arXiv.2609.18803](https://doi.org/10.48550/arXiv.2609.18803). URL: <https://arxiv.org/abs/2609.18803v1>.

*Commentary.*

Section VI, Eq. (48): “The weaker question, which is sufficient for the source-placement theorem, asks only whether there exist a positive map ℱ and a completely positive map ℰ such that Υᵀ=ℱ∘Υ∘ℰ.” The dimension-three assertion asks for this factorization for every unital qutrit channel. MatrixMap(Fin 3, Fin 3, complex) consists of complex linear maps on three by three complex matrices. UnitalChannel F means that F is completely positive, preserves the trace of every matrix, and sends the identity matrix to itself. Here F denotes the channel Υ, while P and E denote the filters ℱ and ℰ. IsPositive P means that P sends every positive semidefinite matrix to a positive semidefinite matrix. IsCompletelyPositive E requires the same property for every finite matrix amplification of E by an identity map. Neither filter is required to preserve trace, to be unital, or to be invertible. Composition is equality of complex linear maps, hence holds on every complex matrix.

The quantifiers include every finite index type S and every Kraus family K representing F; [Fintype S] supplies the finite sum. ofKraus is MatrixMap.of_kraus, with ofKraus(K,K)(X)=∑ᵢ Kᵢ X Kᵢ†. The transposed family is i↦Kᵢᵀ, where transpose is the ordinary matrix transpose in the fixed standard basis. The second formula expands the transpose channel and identifies (Kᵢᵀ)† with the entrywise conjugate K̅ᵢ, denoted map(Kᵢ,star). It therefore gives the channel transpose of Section II.D, Eqs. (15)–(16), rather than the transpose of an output matrix. This channel transpose is independent of the finite Kraus representation and depends on the chosen basis. A counterexample in dimension three refutes the unrestricted unital-qudit assertion.

$\forall S : Type, [\operatorname{Fintype}\left(S\right)] \forall K : S \to \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), (\forall X : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), \operatorname{ofKraus}\left((\lambda i : S, \operatorname{transpose}\left(K\left(i\right)\right)), (\lambda i : S, \operatorname{transpose}\left(K\left(i\right)\right))\right)\left(X\right) = \sum_{i : S} (\operatorname{transpose}\left(K\left(i\right)\right) \cdot X \cdot \operatorname{conjTranspose}\left(\operatorname{transpose}\left(K\left(i\right)\right)\right))) \land (\forall i : S, \operatorname{conjTranspose}\left(\operatorname{transpose}\left(K\left(i\right)\right)\right) = \operatorname{map}\left(K\left(i\right), star\right))$

**Theorem 1.11 (Refutation of the weak question).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/marquez-gonzalez-2026-positive-filter-transpose-refutation` (refuted) by `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"marquez-gonzalez-2026-positive-filter-transpose-refutation","declaration_gid":"D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Samuel A. Márquez González (2026). *Feasibility Ordering of Entanglement-Source Placement for Qubit Channels*. DOI: [10.48550/arXiv.2609.18803](https://doi.org/10.48550/arXiv.2609.18803). URL: <https://arxiv.org/abs/2609.18803v1>.

*Commentary.*

Let U=(1/7)[[3,−2,6],[6,3,−2],[−2,6,3]], and let uⱼ be its columns and eⱼ the standard basis vectors. Put ρⱼ=(eⱼeⱼ†+uⱼuⱼ†)/2. The matrix U is real orthogonal. These three positive semidefinite matrices each have trace 1 and sum to the identity. The channel F(X)=∑ⱼ Xⱼⱼρⱼ has twelve real Kraus matrices: eⱼeⱼᵀ/2 and uⱼeⱼᵀ/2, each repeated twice for each j. Their finite Kraus sum is F, so F is completely positive; the state traces give trace preservation, and the state sum gives unitality. Its channel transpose is Fᵀ(X)=diag(tr(ρ₀X),tr(ρ₁X),tr(ρ₂X)).

Suppose Fᵀ=P∘F∘E with P positive and E completely positive. Complete positivity at amplification size one implies that E is positive. For each k and j there are positive semidefinite trace representatives Bₖ and σⱼ with tr(BₖX)=P(X)ₖₖ and tr(σⱼX)=E(X)ⱼⱼ for every X. Write Jₖₖ for a diagonal matrix unit. The representatives are Bₖ=dual(P)(Jₖₖ) and σⱼ=dual(E)(Jⱼⱼ). The dual of a positive map is positive, and tr(M(X)Y)=tr(X dual(M)(Y)); applying these facts to the positive diagonal units gives their positivity and the displayed trace identities. Define Cₖⱼ=P(ρⱼ)ₖₖ=tr(Bₖρⱼ)≥0. Taking the kth diagonal entry of the factorization and using nondegeneracy of the trace pairing gives ρₖ=∑ⱼ Cₖⱼσⱼ. Every Bₖ is nonzero: otherwise the kth coefficient row and hence ρₖ would vanish, contradicting tr(ρₖ)=1.

If Cₖⱼ=0, the expression tr(Bₖρⱼ)=(eⱼ†Bₖeⱼ+uⱼ†Bₖuⱼ)/2 is a sum of nonnegative quadratic forms equal to zero. Thus Bₖeⱼ=Bₖuⱼ=0. For distinct j and l, the vectors eⱼ,eₗ,uⱼ form a basis. Two different zeros in the kth row would therefore force Bₖ=0. Each row of C has at most one zero.

The state kernel vectors are v₀=(0,1,3), v₁=(3,0,1), and v₂=(1,3,0). With these columns, V=[[0,3,1],[1,0,3],[3,1,0]] has determinant 28. The diagonal-entry matrix Dₖₐ=(ρₖ)ₐₐ=(1/49)[[29,18,2],[2,29,18],[18,2,29]] has determinant 79/343. Set Tⱼₐ=(σⱼ)ₐₐ. The coefficient relation gives D=CT, so T is nonsingular and no σⱼ is zero. The kernel of a finite sum of positive semidefinite matrices is the intersection of their kernels. Apply this to ρₖ=∑ⱼ Cₖⱼσⱼ and ρₖvₖ=0. It gives Cₖⱼσⱼvₖ=0, hence σⱼvₖ=0 whenever Cₖⱼ≠0. If a column of C had no zero, its σⱼ would annihilate all columns of the invertible V and would vanish. Thus every column has a zero. Choosing one zero per column gives distinct rows by the at-most-one-zero row bound; with three columns and three rows, the zeros form a permutation. Each row and each column consequently has exactly one zero.

Fix j. If C₁ⱼ≠0 then σⱼv₁=0. If C₁ⱼ=0, uniqueness of the column's zero gives C₀ⱼ≠0 and σⱼv₀=0; Hermitian symmetry then gives v₀†σⱼ=0. In either case (V†σⱼV)₀₁=0. The coefficient relation gives (V†ρₖV)₀₁=0 for every k. Summing over k and using ∑ₖρₖ=I yields v₀†v₁=(V†V)₀₁=0. But v₀†v₁=0·3+1·0+3·1=3≠0, a contradiction. This rules out the weak factorization for this unital qutrit channel without imposing normalization or invertibility on the filters.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.IsPositive`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.ker_sum`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.trace_eq`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.trace_mul_nonneg`
- Dependency: [D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation](CPFilterTransposeRefutation.md)
