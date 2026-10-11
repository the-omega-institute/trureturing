# Non-concavity of the reduced function of the partial negativity

## Abstract

The function ĥ(ρ) = √(δ₁δ₂) of the two largest eigenvalues δ₁ ≥ δ₂ of a density matrix, the reduced function of the partial negativity, is not concave: the commuting qutrit states diag(1/2, 1/3, 1/6) and diag(1/2, 1/6, 1/3) have ĥ = √(1/6), and their midpoint diag(1/2, 1/4, 1/4) has ĥ = √(1/8).

**Definition 1.1 (The reduced function of the partial negativity).**

$$\forall d: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{hhat}\left(A\right) = \sqrt{\operatorname{getD}\left(\operatorname{sort}\left(\operatorname{map}\left(re, \operatorname{roots}\left(\operatorname{charpoly}\left(A\right)\right)\right), ge\right), 0, 0\right) \operatorname{getD}\left(\operatorname{sort}\left(\operatorname{map}\left(re, \operatorname{roots}\left(\operatorname{charpoly}\left(A\right)\right)\right), ge\right), 1, 0\right)}$$

*Formalization.* `D5/S3/Quantum/Entanglement/PartialNegativityConcavityRefutation.hhat` (`✓ std3`).

*Citation.* Y. Guo (2023). *Partial-Norm of Entanglement: Entanglement Monotones That are not Monogamous*. DOI: [10.1088/1367-2630/acf152](https://doi.org/10.1088/1367-2630/acf152). URL: <https://arxiv.org/abs/2212.06521v6>.

*Commentary.*

For a complex d × d matrix A, let δ₁ ≥ δ₂ ≥ ⋯ be the real parts of the roots of its characteristic polynomial, taken with multiplicity and sorted in decreasing order; ĥ(A) = √(δ₁δ₂). Here roots(p) is the multiset of complex roots of p, map(re, s) the multiset of real parts, sort(s, ge) the list obtained by sorting the multiset s with respect to ≥, and getD(l, n, x) the entry of the list l at position n, counted from 0, or x when the list is too short. For a Hermitian matrix the roots are real and the sorted list is its list of eigenvalues in decreasing order, counted with multiplicity, so δ₁ and δ₂ are its two largest eigenvalues. For a pure bipartite state with decreasing Schmidt coefficients λ₁ ≥ λ₂ ≥ ⋯ the partial negativity is λ₁λ₂, which equals ĥ of either reduced state because the eigenvalues of the reduced state are the λⱼ².

**Definition 1.2 (The conjectured concavity).**

$$claim \Leftrightarrow (\forall d: \mathbb{N}, 2 \leq d \Rightarrow \forall \rho, \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{PosSemidef}\left(\rho\right) \Rightarrow \operatorname{tr}\left(\rho\right) = 1 \Rightarrow \operatorname{PosSemidef}\left(\sigma\right) \Rightarrow \operatorname{tr}\left(\sigma\right) = 1 \Rightarrow \forall t: \mathbb{R}, 0 \leq t \Rightarrow t \leq 1 \Rightarrow t \operatorname{hhat}\left(\rho\right) + (1 - t) \operatorname{hhat}\left(\sigma\right) \leq \operatorname{hhat}\left(t \rho + (1 - t) \sigma\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/PartialNegativityConcavityRefutation.claim` (`✓ std3`).

*Citation.* Y. Guo (2023). *Partial-Norm of Entanglement: Entanglement Monotones That are not Monogamous*. DOI: [10.1088/1367-2630/acf152](https://doi.org/10.1088/1367-2630/acf152). URL: <https://arxiv.org/abs/2212.06521v6>.

*Commentary.*

The conjecture of arXiv:2212.06521v6 that ĥ is concave: for every dimension d ≥ 2, all positive semidefinite ρ and σ of trace one and every real t in [0, 1], t ĥ(ρ) + (1 − t) ĥ(σ) ≤ ĥ(tρ + (1 − t)σ). The products tρ and (1 − t)σ are multiplications of a complex matrix by a real number.

**Theorem 1.3 (The reduced function of the partial negativity is not concave).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialNegativityConcavityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Y. Guo (2023). *Partial-Norm of Entanglement: Entanglement Monotones That are not Monogamous*. DOI: [10.1088/1367-2630/acf152](https://doi.org/10.1088/1367-2630/acf152). URL: <https://arxiv.org/abs/2212.06521v6>.

*Commentary.*

Take d = 3, t = 1/2, ρ = diag(1/2, 1/3, 1/6) and σ = diag(1/2, 1/6, 1/3). Both are positive semidefinite with trace one. The characteristic polynomial of a diagonal matrix is the product of the factors X − dᵢ, so its characteristic roots, sorted decreasingly, are the sorted diagonal entries: (1/2, 1/3, 1/6) for ρ and for σ, and (1/2, 1/4, 1/4) for the midpoint diag(1/2, 1/4, 1/4). Hence ĥ(ρ) = ĥ(σ) = √(1/6), while ĥ of the midpoint is √(1/8) < √(1/6). The second-largest eigenvalue 1/3 belongs to different eigenvectors of ρ and σ, and mixing lowers it to 1/4 while the largest eigenvalue stays 1/2.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PartialNegativityConcavityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialNegativityConcavityRefutation.hhat`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialNegativityConcavityRefutation.result`
