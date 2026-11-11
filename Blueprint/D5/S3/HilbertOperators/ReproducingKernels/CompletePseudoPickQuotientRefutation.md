# Complete pseudo-Pick does not imply quotient positivity

## Abstract

A three-point complete pseudo-Pick pair has a quotient with a negative quadratic form.

**Definition 1.1 (The source block Pick matrix).**

$$\forall \left(X: \operatorname{Type}\right), \left(\forall \left(k: \operatorname{Matrix}\left(X, X, \mathbb{C}\right)\right), \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(z: \left(\operatorname{Fin}\left(n\right)\right) \to \left(X\right)\right), \left(\forall \left(W: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right), \left(\operatorname{pickMatrix}\left(k, z, W\right) = \operatorname{fun} \left(p: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right)\right) \mapsto \left(\operatorname{fun} \left(q: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right)\right) \mapsto \left(\left(\left(\left(1\right) - \left(\left(W\left(\left(p\right).1\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(W\left(\left(q\right).1\right)\right)\right)\right)\right)\left(\left(p\right).2, \left(q\right).2\right)\right) \cdot \left(k\left(z\left(\left(p\right).1\right), z\left(\left(q\right).1\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation.pickMatrix` (`✓ std3`).

*Citation.* Shuaibing Luo, Scott McCullough and Georgios Tsikalas (2026). *Beurling Criteria for Reproducing Kernels*. URL: <https://arxiv.org/abs/2607.25088v2>.

*Commentary.*

Definition 9.2, page 45, uses the condition “(I − WᵢWⱼ*)k(zᵢ, zⱼ) ⪰ 0”. The displayed matrix contains all n by n blocks, each of size m by m, with indices in Fin n × Fin m. The letter m replaces the source's matrix-size letter k; k remains the scalar kernel. Matrix.conjTranspose is the matrix adjoint.

**Definition 1.2 (Contractivity on the target space).**

$$\forall \left(X: \operatorname{Type}\right), \left(\forall \left(ell: \operatorname{Matrix}\left(X, X, \mathbb{C}\right)\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(Phi: \left(X\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{IsContractiveMultiplier}\left(ell, m, Phi\right)\right) \Leftrightarrow \left(\operatorname{Matrix.PosSemidef}\left(\operatorname{fun} \left(p: X \times \operatorname{Fin}\left(m\right)\right) \mapsto \left(\operatorname{fun} \left(q: X \times \operatorname{Fin}\left(m\right)\right) \mapsto \left(\left(\left(\left(1\right) - \left(\left(Phi\left(\left(p\right).1\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(Phi\left(\left(q\right).1\right)\right)\right)\right)\right)\left(\left(p\right).2, \left(q\right).2\right)\right) \cdot \left(ell\left(\left(p\right).1, \left(q\right).1\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation.IsContractiveMultiplier` (`✓ std3`).

*Citation.* Shuaibing Luo, Scott McCullough and Georgios Tsikalas (2026). *Beurling Criteria for Reproducing Kernels*. URL: <https://arxiv.org/abs/2607.25088v2>.

*Commentary.*

Section 3, page 15, states: “In this case, Φ induces a bounded operator MΦ : Hκ ⊗ F → Hλ ⊗ E whose norm is the smallest C ≥ 0 such that X × X ∋ (a,b) ↦ C²λ(a,b)I_E − Φ(a)Φ(b)* κ(a,b) is positive semi-definite.” Here C = 1, κ = λ = ell, and E = F = ℂᵐ. Matrix.PosSemidef tests Hermitian symmetry and nonnegative quadratic forms on all finitely supported vectors.

**Definition 1.3 (Complete pseudo-Pick pairs).**

$$\forall \left(X: \operatorname{Type}\right), \left(\forall \left(k: \operatorname{Matrix}\left(X, X, \mathbb{C}\right)\right), \left(\forall \left(ell: \operatorname{Matrix}\left(X, X, \mathbb{C}\right)\right), \left(\left(\operatorname{CompletePseudoPick}\left(k, ell\right)\right) \Leftrightarrow \left(\forall \left(n: \mathbb{N}\right), \left(\left(0 < n\right) \Rightarrow \left(\forall \left(m: \mathbb{N}\right), \left(\left(0 < m\right) \Rightarrow \left(\forall \left(z: \left(\operatorname{Fin}\left(n\right)\right) \to \left(X\right)\right), \left(\forall \left(W: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(\operatorname{pickMatrix}\left(k, z, W\right)\right)\right) \Rightarrow \left(\exists \left(Phi: \left(X\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{IsContractiveMultiplier}\left(ell, m, Phi\right)\right) \land \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(Phi\left(z\left(i\right)\right) = W\left(i\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation.CompletePseudoPick` (`✓ std3`).

*Citation.* Shuaibing Luo, Scott McCullough and Georgios Tsikalas (2026). *Beurling Criteria for Reproducing Kernels*. URL: <https://arxiv.org/abs/2607.25088v2>.

*Commentary.*

Definition 9.2, page 45: “A pair (k, ℓ) on a set X is a complete pseudo-Pick pair if, whenever positive integer n and k, points z₁, …, zₙ ∈ X and matrices W₁, …, Wₙ ∈ Mₖ(ℂ) satisfy (I − WᵢWⱼ*)k(zᵢ, zⱼ) ⪰ 0, there exists a contractive multiplier Φ ∈ Mult(Hℓ ⊗ ℂᵏ, Hℓ ⊗ ℂᵏ) such that Φ(zᵢ)=Wᵢ for all i.” Both positive sizes are arbitrary. The list z may repeat points. The interpolating function is defined on all of X and acts on the target space in both domain and codomain.

**Definition 1.4 (Question 9.3).**

$$\left(\operatorname{claim}\right) \Leftrightarrow \left(\forall \left(X: \operatorname{Type}\right), \left(\forall \left(k: \operatorname{Matrix}\left(X, X, \mathbb{C}\right)\right), \left(\forall \left(ell: \operatorname{Matrix}\left(X, X, \mathbb{C}\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(k\right)\right) \Rightarrow \left(\left(\operatorname{Matrix.PosSemidef}\left(ell\right)\right) \Rightarrow \left(\left(\forall \left(x: X\right), \left(\forall \left(y: X\right), \left(k\left(x, y\right) \ne 0\right)\right)\right) \Rightarrow \left(\left(\operatorname{CompletePseudoPick}\left(k, ell\right)\right) \Rightarrow \left(\operatorname{Matrix.PosSemidef}\left(\operatorname{fun} \left(x: X\right) \mapsto \left(\operatorname{fun} \left(y: X\right) \mapsto \left(\frac{ell\left(x, y\right)}{k\left(x, y\right)}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation.claim` (`✓ std3`).

*Citation.* Shuaibing Luo, Scott McCullough and Georgios Tsikalas (2026). *Beurling Criteria for Reproducing Kernels*. URL: <https://arxiv.org/abs/2607.25088v2>.

*Commentary.*

Question 9.3, page 45: “Let (k, ℓ) be a pair of reproducing kernels with k non-vanishing. If (k, ℓ) is complete pseudo-Pick, do we have ℓ/k ⪰ 0?” The affirmative assertion ranges over every X : Type and two complex kernels. Non-vanishing means k x y ≠ 0 for every pair x,y, so the quotient uses no zero denominator. The notation ell denotes ℓ. No assumption of strict positive definiteness, holomorphicity or distinct interpolation nodes is imposed.

**Theorem 1.5 (A three-point counterexample).**

$$\neg \left(\forall \left(X: \operatorname{Type}\right), \left(\forall \left(k: \operatorname{Matrix}\left(X, X, \mathbb{C}\right)\right), \left(\forall \left(ell: \operatorname{Matrix}\left(X, X, \mathbb{C}\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(k\right)\right) \Rightarrow \left(\left(\operatorname{Matrix.PosSemidef}\left(ell\right)\right) \Rightarrow \left(\left(\forall \left(x: X\right), \left(\forall \left(y: X\right), \left(k\left(x, y\right) \ne 0\right)\right)\right) \Rightarrow \left(\left(\operatorname{CompletePseudoPick}\left(k, ell\right)\right) \Rightarrow \left(\operatorname{Matrix.PosSemidef}\left(\operatorname{fun} \left(x: X\right) \mapsto \left(\operatorname{fun} \left(y: X\right) \mapsto \left(\frac{ell\left(x, y\right)}{k\left(x, y\right)}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-lmt2607q93` (refuted) by `D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-lmt2607q93","declaration_gid":"D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shuaibing Luo, Scott McCullough and Georgios Tsikalas (2026). *Beurling Criteria for Reproducing Kernels*. URL: <https://arxiv.org/abs/2607.25088v2>.

*Commentary.*

On Fin 3 take coordinates (1/10,1,2), source kernel k(i,j)=1+xᵢxⱼ, and target kernel ell(i,j)=1+δᵢⱼxᵢ². Both kernels are positive semidefinite, and every source entry is nonzero. The quotient has diagonal entries one and off-diagonal entries 10/11, 5/6 and 1/3. Its quadratic form at (−2,1,1) is −10/33.

Source Pick positivity forces equal matrices at repeated points. When all three points occur, the two relations with coefficients (−1,19/10,−9/10) and their coordinate-weighted values force all three matrices to agree. A constant contractive multiplier then interpolates the data.

For two observed points, copy one value to the omitted point. Three rational diagonal factorizations certify positivity of the corresponding scalar quotient matrices; the Schur product theorem gives a contractive multiplier on the whole three-point set. Single-point data have a constant extension. These cases cover every finite node list and every positive matrix size.

The three source kernel vectors are dependent. Thus complete pseudo-Pick interpolation does not detect this three-point quotient obstruction. The infinite-rank family, a strictly positive-definite source, holomorphic kernels, and the separate implication to BLH are not asserted here.

## References

- Truth anchor: `D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation.CompletePseudoPick`
- Truth anchor: `D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation.IsContractiveMultiplier`
- Truth anchor: `D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation.claim`
- Truth anchor: `D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation.pickMatrix`
- Truth anchor: `D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation.result`
