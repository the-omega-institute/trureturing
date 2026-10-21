# A counterexample to Lin's Conjecture 4.3

## Abstract

Lin's majorization conjecture fails for positive semidefinite three-by-three matrices at exponent four.

**Definition 1.1 (Descending eigenvalues).**

$$\forall n : \mathbb{N}, \forall M : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{eigDesc}\left(M\right) = (if h : (M).IsHermitian then (\operatorname{List.ofFn}\left((h).eigenvalues\right)).mergeSort\left((fun a : \mathbb{R} \mapsto (fun b : \mathbb{R} \mapsto \operatorname{decide}\left(b \le a\right)))\right) else [])$$

*Formalization.* `D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.eigDesc` (`✓ std3`).

*Citation.* Minghua Lin (2017). *On a determinantal inequality arising from diffusion tensor imaging*. DOI: [10.1142/S0219199716500449](https://doi.org/10.1142/S0219199716500449). URL: <https://arxiv.org/abs/1604.04141v1>.

*Commentary.*

Section 2, arXiv v1 p. 2: “For an n × n matrix A with all eigenvalues real, we denote the vector of eigenvalues by λ(A) = (λ₁(A), …, λ_n(A)), and we assume that the components of λ(A) are in descending order.” Hermitian eigenvalues are counted with multiplicity by List.ofFn and sorted in descending order. The list is empty for a non-Hermitian matrix. Each matrix used in the refutation is Hermitian.

**Definition 1.2 (Majorization of descending lists).**

$$\forall x : \operatorname{List}\left(\mathbb{R}\right), \forall y : \operatorname{List}\left(\mathbb{R}\right), \operatorname{Majorizes}\left(x, y\right) = ((\forall k : \mathbb{N}, (1 \le k) \Rightarrow ((k \le (x).length) \Rightarrow (((y).take\left(k\right)).sum \le ((x).take\left(k\right)).sum))) \land ((x).sum = (y).sum))$$

*Formalization.* `D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.Majorizes` (`✓ std3`).

*Citation.* Minghua Lin (2017). *On a determinantal inequality arising from diffusion tensor imaging*. DOI: [10.1142/S0219199716500449](https://doi.org/10.1142/S0219199716500449). URL: <https://arxiv.org/abs/1604.04141v1>.

*Commentary.*

Section 2, arXiv v1 p. 2: “we say that x weakly majorizes y, written as x ≻_w y, if Σ_{i=1}^k x↓_i ≥ Σ_{i=1}^k y↓_i for k = 1, …, n. We say x majorizes y, denoted by x ≻ y, if x ≻_w y and the sum of all elements of x equal to the sum of all elements of y.” Here x and y are descending eigenvalue lists of equal length; take selects a prefix and sum adds its entries.

**Definition 1.3 (Conjecture 4.3).**

$$claim = (\forall n : \mathbb{N}, \forall A : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall B : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), ((A).PosSemidef) \Rightarrow (((B).PosSemidef) \Rightarrow (\forall p : \mathbb{R}, (0 < p) \Rightarrow (\operatorname{Majorizes}\left(\operatorname{eigDesc}\left(A^{2} + \operatorname{cfc}\left((fun x : \mathbb{R} \mapsto x^{p}), \operatorname{CFC.sqrt}\left(\operatorname{conjTranspose}\left(B \cdot A\right) \cdot B \cdot A\right)\right)\right), \operatorname{eigDesc}\left(A^{2} + \operatorname{cfc}\left((fun x : \mathbb{R} \mapsto x^{p}), \operatorname{CFC.sqrt}\left(\operatorname{conjTranspose}\left(A \cdot B\right) \cdot A \cdot B\right)\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.claim` (`✓ std3`).

*Citation.* Minghua Lin (2017). *On a determinantal inequality arising from diffusion tensor imaging*. DOI: [10.1142/S0219199716500449](https://doi.org/10.1142/S0219199716500449). URL: <https://arxiv.org/abs/1604.04141v1>.

*Commentary.*

Conjecture 4.3, arXiv v1 p. 6: “Let A and B be n × n positive semidefinite matrices. Then λ(A² + |BA|^p) ≻ λ(A² + |AB|^p) for all p > 0.” The matrix carrier is Matrix (Fin n) (Fin n) ℂ, n ranges over all natural numbers, PosSemidef is positive semidefiniteness, and p ranges over all positive real numbers. cfc and CFC.sqrt express the absolute powers by the real function x ↦ x^p on the positive square root of XᴴX; eigDesc and Majorizes express descending eigenvalues and majorization.

**Theorem 1.4 (Refutation in dimension three).**

$$\neg (\forall n : \mathbb{N}, \forall A : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall B : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), ((A).PosSemidef) \Rightarrow (((B).PosSemidef) \Rightarrow (\forall p : \mathbb{R}, (0 < p) \Rightarrow (\operatorname{Majorizes}\left(\operatorname{eigDesc}\left(A^{2} + \operatorname{cfc}\left((fun x : \mathbb{R} \mapsto x^{p}), \operatorname{CFC.sqrt}\left(\operatorname{conjTranspose}\left(B \cdot A\right) \cdot B \cdot A\right)\right)\right), \operatorname{eigDesc}\left(A^{2} + \operatorname{cfc}\left((fun x : \mathbb{R} \mapsto x^{p}), \operatorname{CFC.sqrt}\left(\operatorname{conjTranspose}\left(A \cdot B\right) \cdot A \cdot B\right)\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lin-2017-majorization-conjecture-4-3` (refuted) by `D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lin-2017-majorization-conjecture-4-3","declaration_gid":"D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2017). *On a determinantal inequality arising from diffusion tensor imaging*. DOI: [10.1142/S0219199716500449](https://doi.org/10.1142/S0219199716500449). URL: <https://arxiv.org/abs/1604.04141v1>.

*Commentary.*

Use A = diagonal(3,1,1/2) and B = [[1/2,1/4,3/4],[1/4,3/4,0],[3/4,0,5/2]], and p = 4. Rational triangular factorizations prove that B and L − (7/5)I are positive semidefinite, where L = A² + |BA|⁴. The vector (0,−1,19/64) has negative quadratic form for R − (7/5)I, where R = A² + |AB|⁴. Thus every eigenvalue of L is at least 7/5 and an eigenvalue of R is below 7/5. Majorization of the descending three-entry lists would combine its two-entry prefix inequality and equality of the totals to give the opposite ordering of the smallest entries. This contradicts those bounds. No determinant inequality is asserted or refuted here.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.Majorizes`
- Truth anchor: `D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.eigDesc`
- Truth anchor: `D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.result`
- Dependency: [D5/S3/Quantum/Measurement/OverlapLowRankDistance](../Measurement/OverlapLowRankDistance.md)
