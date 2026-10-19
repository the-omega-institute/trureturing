# Li–Tan circulant positivity fails at order four

## Abstract

The Li–Tan circulant transform of a positive semidefinite correlation matrix can have a negative quadratic value at order four.

Indices are in Fin n, with addition modulo n. Matrix positivity uses Matrix.PosSemidef. Complex.arg takes values in (−π, π], and the real power of the nonnegative modulus product uses Real.rpow. The matrix with entry 1 when j=i+1 and 0 otherwise is the source's C_n. The displayed real and complex type annotations show the scalar coercions.

**Definition 1.1 (Geometric moduli and mean principal phases).**

$$\forall (n: \mathbb{N}), [\operatorname{NeZero}\left(n\right)], \forall (H: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (k: \mathbb{N}), \operatorname{z}\left(n, H, k\right) = ((\prod_{l: \operatorname{Fin}\left(n\right)} \left\lVert H\left(l, l + \operatorname{Fin.ofNat}\left(n, k\right)\right) \right\rVert)^{\frac{(1: \mathbb{R})}{(n: \mathbb{R})}}: \mathbb{C}) \cdot \operatorname{Complex.exp}\left(\operatorname{Complex.I} \cdot (\frac{\sum_{l: \operatorname{Fin}\left(n\right)} \operatorname{Complex.arg}\left(H\left(l, l + \operatorname{Fin.ofNat}\left(n, k\right)\right)\right)}{(n: \mathbb{R})}: \mathbb{C})\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation.z` (`✓ std3`).

*Citation.* Mao-Sheng Li; Yi-Xi Tan (2024). *On the Bargmann invariants for quantum imaginarity*. DOI: [10.48550/arXiv.2412.08022](https://doi.org/10.48550/arXiv.2412.08022). URL: <https://arxiv.org/abs/2412.08022v1>.

*Commentary.*

Section III, page 5: "For each H = (h_kl) ∈ Mat_{n×n}(ℂ), we can associate it with a circulant matrix C_H = Σ_{k=0}^{n−1} z_k C_nᵏ, where the coefficients are given by z_k = (Π_{l=1}^n r_{l(l⊕k)})^{1/n} e^{iθ_k}, with θ_k := (Σ_{l=1}^n θ_{l(l⊕k)})/n and h_kl = r_kl e^{iθ_kl}, where r_kl ≥ 0 and θ_kl ∈ (−π, π]." Here r_kl is ‖H k l‖ and θ_kl is Complex.arg (H k l). The natural k becomes Fin.ofNat n k before addition to l. Products and sums run over every l : Fin n exactly once.

**Definition 1.2 (The associated circulant matrix).**

$$\forall (n: \mathbb{N}), [\operatorname{NeZero}\left(n\right)], \forall (H: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{CH}\left(n, H\right) = \sum_{k \in \operatorname{Finset.range}\left(n\right)} \operatorname{HSMul.hSMul}\left(\operatorname{z}\left(n, H, k\right), \operatorname{Matrix.of}\left((fun (i j: \operatorname{Fin}\left(n\right)) \mapsto if j = i + 1 then (1: \mathbb{C}) else 0)\right)^{k}\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation.CH` (`✓ std3`).

*Citation.* Mao-Sheng Li; Yi-Xi Tan (2024). *On the Bargmann invariants for quantum imaginarity*. DOI: [10.48550/arXiv.2412.08022](https://doi.org/10.48550/arXiv.2412.08022). URL: <https://arxiv.org/abs/2412.08022v1>.

*Commentary.*

Section II, page 2: "Let C_n = G_{(0,1,0,…,0)}". Section III, page 5: "For each H = (h_kl) ∈ Mat_{n×n}(ℂ), we can associate it with a circulant matrix C_H = Σ_{k=0}^{n−1} z_k C_nᵏ, where the coefficients are given by z_k = (Π_{l=1}^n r_{l(l⊕k)})^{1/n} e^{iθ_k}, with θ_k := (Σ_{l=1}^n θ_{l(l⊕k)})/n and h_kl = r_kl e^{iθ_kl}, where r_kl ≥ 0 and θ_kl ∈ (−π, π]." The shift matrix is written entrywise. HSMul.hSMul is scalar multiplication, the exponent k is natural, and k ∈ Finset.range n means 0 ≤ k < n.

**Definition 1.3 (The positivity conjecture).**

$$claim = (\forall (n: \mathbb{N}), [\operatorname{NeZero}\left(n\right)], \forall (H: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix.PosSemidef}\left(H\right)) \Rightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), H\left(i, i\right) = 1) \Rightarrow (\operatorname{Matrix.PosSemidef}\left(\operatorname{CH}\left(n, H\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation.claim` (`✓ std3`).

*Citation.* Mao-Sheng Li; Yi-Xi Tan (2024). *On the Bargmann invariants for quantum imaginarity*. DOI: [10.48550/arXiv.2412.08022](https://doi.org/10.48550/arXiv.2412.08022). URL: <https://arxiv.org/abs/2412.08022v1>.

*Commentary.*

Section II, page 2: "Let 𝐇_n denote the set of all n × n Hermitian matrices H that are positive semidefinite and have h_ii = 1 for all i = 1, …, n." Section III, page 5: "For the case when n = 3, we deduced that the positive semidefiniteness of C_H follows from the positive semidefiniteness of H. This leads us to the conjecture that the positive semidefiniteness of H implies the positive semidefiniteness of C_H (which may depend on n) for general n." The formula quantifies over every nonzero natural n and every complex matrix H with positive semidefiniteness and unit diagonal. The source's labels 1,…,n are represented by Fin n.

**Theorem 1.4 (A rational counterexample of order four).**

$$\neg (\forall (n: \mathbb{N}), [\operatorname{NeZero}\left(n\right)], \forall (H: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix.PosSemidef}\left(H\right)) \Rightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), H\left(i, i\right) = 1) \Rightarrow (\operatorname{Matrix.PosSemidef}\left(\operatorname{CH}\left(n, H\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mao-Sheng Li; Yi-Xi Tan (2024). *On the Bargmann invariants for quantum imaginarity*. DOI: [10.48550/arXiv.2412.08022](https://doi.org/10.48550/arXiv.2412.08022). URL: <https://arxiv.org/abs/2412.08022v1>.

*Commentary.*

Take H with rows (1,5/8,1/9,5/8), (5/8,1,5/8,4/9), (1/9,5/8,1,5/8), and (5/8,4/9,5/8,1). A diagonal Gram factorization proves H.PosSemidef, and its diagonal entries are 1. Every entry is a positive real number, so every principal phase is zero. The coefficients are (1,5/8,2/9,5/8). Thus CH 4 H has these entries as its first row, and its quadratic value at (1,−1,1,−1) is −1/9. Positivity would force this value to be nonnegative. Unequal opposite correlations 1/9 and 4/9 become their geometric mean 2/9. This refutes the general implication already for real matrices at n=4. The argument makes no assertion about the source's n=3 result or the separate equality of the two Bargmann invariant sets.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation.CH`
- Truth anchor: `D5/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation.result`
- Truth anchor: `D5/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation.z`
