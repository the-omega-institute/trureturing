# Strict spectral domination and near order

## Abstract

Strict comparison of every ordered eigenvalue of the actual means does not imply near order.

**Definition 1.1 (Strict ordered eigenvalue comparison).**

$$\forall m: \mathbb{N}, \forall X: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), \forall Y: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), (\operatorname{StrictSpectralOrder}\left(X, Y\right)) \Leftrightarrow ((\operatorname{IsHermitian}\left(X\right)) \land ((\operatorname{IsHermitian}\left(Y\right)) \land (\forall i: \operatorname{Fin}\left(m\right), \operatorname{lambda}\left(X, i\right) < \operatorname{lambda}\left(Y, i\right))))$$

*Formalization.* `D5/S3/Quantum/Matrix/HwangKimStrictSpectralConverseRefutation.StrictSpectralOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jinmi Hwang; Sejong Kim (2024). *Near-order relation of power means*. DOI: [10.1007/s11117-024-01099-4](https://doi.org/10.1007/s11117-024-01099-4). URL: <https://arxiv.org/abs/2407.07438v1>.

*Commentary.*

lambda(X,i) is the i-th decreasingly ordered Hermitian eigenvalue, Matrix.IsHermitian.eigenvalues₀. The definition requires Hermitian X and Y. Proof witnesses for Hermiticity do not affect the eigenvalue functions.

**Definition 1.2 (The strict-spectral converse for actual means).**

$$(claim) \Leftrightarrow (\forall m: \mathbb{N}, (1 \le m) \Rightarrow (\forall n: \mathbb{N}, (2 \le n) \Rightarrow (\forall w: \operatorname{Fin}\left(n\right) \to \mathbb{R}, (\forall j: \operatorname{Fin}\left(n\right), 0 < \operatorname{w}\left(j\right)) \Rightarrow ((\sum_{j} \operatorname{w}\left(j\right) = 1) \Rightarrow (\forall A: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), (\forall j: \operatorname{Fin}\left(n\right), \operatorname{PosDef}\left(\operatorname{A}\left(j\right)\right)) \Rightarrow ((\operatorname{StrictSpectralOrder}\left(\operatorname{logEuclidean}\left(w, A\right), \operatorname{wassersteinBarycenter}\left(w, A\right)\right)) \Rightarrow (\operatorname{NearOrder}\left(\operatorname{logEuclidean}\left(w, A\right), \operatorname{wassersteinBarycenter}\left(w, A\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/HwangKimStrictSpectralConverseRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jinmi Hwang; Sejong Kim (2024). *Near-order relation of power means*. DOI: [10.1007/s11117-024-01099-4](https://doi.org/10.1007/s11117-024-01099-4). URL: <https://arxiv.org/abs/2407.07438v1>.

*Commentary.*

For every complex matrix size m≥1, input count n≥2, strictly positive normalized weight vector and positive definite input family, ask whether strict comparison of every sorted eigenvalue of LE and the actual epsilon-selected Wasserstein barycenter would imply NearOrder. This is the reverse implication separated by the first Ma–Zhang witness; it is not the original forward near-order question.

**Theorem 1.3 (The original witness refutes the converse).**

$$\neg (\forall m: \mathbb{N}, (1 \le m) \Rightarrow (\forall n: \mathbb{N}, (2 \le n) \Rightarrow (\forall w: \operatorname{Fin}\left(n\right) \to \mathbb{R}, (\forall j: \operatorname{Fin}\left(n\right), 0 < \operatorname{w}\left(j\right)) \Rightarrow ((\sum_{j} \operatorname{w}\left(j\right) = 1) \Rightarrow (\forall A: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), (\forall j: \operatorname{Fin}\left(n\right), \operatorname{PosDef}\left(\operatorname{A}\left(j\right)\right)) \Rightarrow ((\operatorname{StrictSpectralOrder}\left(\operatorname{logEuclidean}\left(w, A\right), \operatorname{wassersteinBarycenter}\left(w, A\right)\right)) \Rightarrow (\operatorname{NearOrder}\left(\operatorname{logEuclidean}\left(w, A\right), \operatorname{wassersteinBarycenter}\left(w, A\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HwangKimStrictSpectralConverseRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinmi Hwang; Sejong Kim (2024). *Near-order relation of power means*. DOI: [10.1007/s11117-024-01099-4](https://doi.org/10.1007/s11117-024-01099-4). URL: <https://arxiv.org/abs/2407.07438v1>.

*Commentary.*

Use the original A=diag(4,1), B=[[19,−3√15],[−3√15,61]]/64 at weights (1/2,1/2). The original positive-input, actual CFC log-Euclidean and global-argmin Wasserstein proofs are reused. With u=√√2 and z=√265, LE has sorted eigenvalues u and 1/u. For W, tr W=25/16+265/(16z) and det W=(5/8+10/z)². Rational interval bounds prove tr W>2u, tr W>2/u and (1/u)²−tr(W)/u+det W>0. Sortedness and the quadratic root identity therefore give lambda(W,0)>u and lambda(W,1)>1/u. The original trace obstruction supplies failure of near order. Thus the new strict-spectrum premise is proved for actual means; neither an assumed premise nor a surrogate mean is used. The original universal near-order refutation is reused, not a new discovery. Source: Ma–Zhang revision2 Theorem 1 and Corollary (reverse), issue #29594, CC BY 4.0. Haobo Ma: ChronoAI, Singapore. Wenlin Zhang: NUS and ChronoAI, Singapore. This does not prove the second weighted witness, the arbitrary-size families, or the full classification of reverse implications. BJL's actual norm/weak-majorization Conjecture 1 and weak log-majorization remain intact.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HwangKimStrictSpectralConverseRefutation.StrictSpectralOrder`
- Truth anchor: `D5/S3/Quantum/Matrix/HwangKimStrictSpectralConverseRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/HwangKimStrictSpectralConverseRefutation.result`
- Dependency: [D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation](HwangKimNearOrderRefutation.md)
