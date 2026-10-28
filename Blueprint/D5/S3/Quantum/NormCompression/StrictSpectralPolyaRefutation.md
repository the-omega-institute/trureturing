# A counterexample to strict spectral convergence

## Abstract

Schatten-p approximants need not converge to the strict spectral approximant. A complex linear subspace of three-by-three matrices has a strict residual with singular values (1,1,0), whereas every minimizing residual for sufficiently large p has real last diagonal entry less than -1/4.

**Theorem 1.1 (Real powers of a square).**

$$\forall (a : \mathbb{R}), \forall (p : \mathbb{R}), \left(a^{2}\right)^{\frac{p}{2}} = \left|a\right|^{p}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.rpow_square_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real a and p, the nonnegative square a² has power p/2 equal to the p-th power of |a|.

**Definition 1.2 (Schatten-p approximation).**

$$\forall (p : \mathbb{R}), \forall (m : \mathbb{N}), \forall (n : \mathbb{N}), \forall (M : \operatorname{Submodule}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right)), \forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (B : \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{IsCpApproximant}\left(p, M, A, B\right) = \left((B \in M) \land (\forall (X : \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (X \in M) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{NormCompression}.\operatorname{UpperBranchReduction}.\operatorname{schattenNorm}\left(p, A - B\right) \le \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{NormCompression}.\operatorname{UpperBranchReduction}.\operatorname{schattenNorm}\left(p, A - X\right)))\right)$$

*Formalization.* `D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.IsCpApproximant` (`✓ std3`).

*Citation.* Krystyna Ziętak (2017). *From the strict Chebyshev approximant of a vector to the strict spectral approximant of a matrix*. DOI: [10.4064/bc112-0-16](https://doi.org/10.4064/bc112-0-16). URL: <https://doi.org/10.4064/bc112-0-16>.

*Commentary.*

Page 308, verbatim: "Thus for 1 < p < ∞ the cₚ-approximant B = Bₚ ∈ ℳ to A satisfying (1.1) is unique." Equation (1.1) minimizes the Schatten p-norm of A - X over X in the linear subspace. Here p is real, matrices have row and column carriers Fin m and Fin n, and schattenNorm is the finite singular-value norm in UpperBranchReduction. The limiting assertion below requires p > 1.

**Definition 1.3 (Lexicographic spectral approximation).**

$$\forall (m : \mathbb{N}), \forall (n : \mathbb{N}), \forall (M : \operatorname{Submodule}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right)), \forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (B : \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{IsStrictSpectralApproximant}\left(M, A, B\right) = \left((B \in M) \land (\forall (X : \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (X \in M) \Rightarrow (\operatorname{toLex}\left((fun (k : \mathbb{N}) \mapsto \operatorname{LinearMap}.\operatorname{singularValues}\left(\operatorname{Matrix}.\operatorname{toEuclideanLin}\left(A - B\right), k\right))\right) \le \operatorname{toLex}\left((fun (k : \mathbb{N}) \mapsto \operatorname{LinearMap}.\operatorname{singularValues}\left(\operatorname{Matrix}.\operatorname{toEuclideanLin}\left(A - X\right), k\right))\right)))\right)$$

*Formalization.* `D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.IsStrictSpectralApproximant` (`✓ std3`).

*Citation.* Krystyna Ziętak (2017). *From the strict Chebyshev approximant of a vector to the strict spectral approximant of a matrix*. DOI: [10.4064/bc112-0-16](https://doi.org/10.4064/bc112-0-16). URL: <https://doi.org/10.4064/bc112-0-16>.

*Commentary.*

Page 309, verbatim: "A matrix B⁽ˢᵗ⁾ ∈ ℳ is a strict spectral approximant to a matrix A if the vector σ(R⁽ˢᵗ⁾) of the ordered singular values of the residual matrix R⁽ˢᵗ⁾ = A − B⁽ˢᵗ⁾ is minimal with respect to the lexicographic ordering in the set of vectors {σ ∈ ℝᵗ : σ = σ(A − X), X ∈ ℳ} (see [106])." Fin m and Fin n index the entries. LinearMap.singularValues supplies decreasing ordered singular values, padded by zeros; toLex uses the natural order of ℕ.

**Definition 1.4 (Ziętak's Conjecture 1.1).**

$$(claim) \Leftrightarrow (\forall (m : \mathbb{N}), \forall (n : \mathbb{N}), \forall (M : \operatorname{Submodule}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right)), \forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (Bst : \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (B : (\mathbb{R} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right))), (\operatorname{IsStrictSpectralApproximant}\left(M, A, Bst\right)) \Rightarrow ((\forall (p : \mathbb{R}), (1 < p) \Rightarrow (\operatorname{IsCpApproximant}\left(p, M, A, B\left(p\right)\right))) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left((fun (p : \mathbb{R}) \mapsto A - B\left(p\right)), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(A - Bst\right)\right))))$$

*Formalization.* `D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.claim` (`✓ std3`).

*Citation.* Krystyna Ziętak (2017). *From the strict Chebyshev approximant of a vector to the strict spectral approximant of a matrix*. DOI: [10.4064/bc112-0-16](https://doi.org/10.4064/bc112-0-16). URL: <https://doi.org/10.4064/bc112-0-16>.

*Commentary.*

Page 309, Conjecture 1.1, verbatim: "Let ℳ be a linear subspace of ℂᵐˣⁿ and let Bₚ ∈ ℳ be the cₚ-approximant to A ∈ ℂᵐˣⁿ. As p tends to ∞, the matrix Rₚ = A − Bₚ converges to A − B⁽ˢᵗ⁾, where B⁽ˢᵗ⁾ is the strict spectral approximant to A." The quantifiers range over all dimensions, complex linear subspaces, targets, strict approximants and functions B of the real exponent p. Minimization is required for every p > 1, and the residual converges in the matrix topology as p tends to infinity.

**Theorem 1.5 (The universal convergence claim is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zietak-2017-strict-spectral-polya-conjecture` (refuted) by `D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zietak-2017-strict-spectral-polya-conjecture","declaration_gid":"D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Krystyna Ziętak (2017). *From the strict Chebyshev approximant of a vector to the strict spectral approximant of a matrix*. DOI: [10.4064/bc112-0-16](https://doi.org/10.4064/bc112-0-16). URL: <https://doi.org/10.4064/bc112-0-16>.

*Commentary.*

Set A = I₃, H = [[1,0,1],[0,-2,0],[1,0,0]], E = Matrix.diagonal (Pi.single 2 1), and M = Submodule.span ℂ {H,E}. The residuals are [[1+s,0,s],[0,1-2s,0],[s,0,t]]. The two leading diagonal constraints force s = 0 on the spectral-optimal face, whose lexicographic minimum is diag(1,1,0), so E is strict. Schatten-p minimizers exist for every p > 1. Their real last residual entry is eventually below -1/4, contradicting convergence to the strict residual. Hermitian projection reduces the complex minimization to a real comparison. No uniqueness or exact residual limit is needed.

Grover–Gupta's Theorem 3.7 for min(m,n) ≤ 2 remains valid. The three-dimensional example uses a repeated leading singular-value cluster and a coupling that does not commute with E. Eventual superiority against each fixed competitor does not give a uniform comparison against moving minimizers.

Priyanka Grover and Krishna Kumar Gupta, Properties of best approximations with respect to the Ky Fan p-k norm, and the strict spectral approximant of a matrix, LAA 743 (2026), DOI 10.1016/j.laa.2026.04.016; arXiv:2603.07498v2.

## References

- Truth anchor: `D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.IsCpApproximant`
- Truth anchor: `D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.IsStrictSpectralApproximant`
- Truth anchor: `D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.claim`
- Truth anchor: `D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.result`
- Truth anchor: `D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.rpow_square_half`
- Dependency: [D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral](../Measurement/OccupationPartialTransposeSpectral.md)
- Dependency: [D5/S3/Quantum/NormCompression/UpperBranchReduction](UpperBranchReduction.md)
- Dependency: [D5/S3/Resource/LogDet/PathSpectralClassical](../../Resource/LogDet/PathSpectralClassical.md)
