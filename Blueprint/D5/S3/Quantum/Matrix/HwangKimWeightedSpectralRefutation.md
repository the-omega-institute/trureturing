# The unequal-weight entrywise counterexample

## Abstract

The actual matrix means need not have entrywise ordered eigenvalues.

**Definition 1.1 (Ordered eigenvalue comparison).**

$$\forall m: \mathbb{N}, \forall X: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), \forall Y: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), (\operatorname{SpectralOrder}\left(X, Y\right)) \Leftrightarrow ((\operatorname{IsHermitian}\left(X\right)) \land ((\operatorname{IsHermitian}\left(Y\right)) \land (\forall i: \operatorname{Fin}\left(m\right), \operatorname{lambda}\left(X, i\right) \le \operatorname{lambda}\left(Y, i\right))))$$

*Formalization.* `D5/S3/Quantum/Matrix/HwangKimWeightedSpectralRefutation.SpectralOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jinmi Hwang; Sejong Kim (2024). *Near-order relation of power means*. DOI: [10.1007/s11117-024-01099-4](https://doi.org/10.1007/s11117-024-01099-4). URL: <https://arxiv.org/abs/2407.07438v1>.

*Commentary.*

lambda(X,i) is the i-th decreasingly ordered Hermitian eigenvalue, Matrix.IsHermitian.eigenvalues₀. This is non-strict entrywise spectral comparison, with Hermitian X,Y; it is neither weak majorization nor weak log-majorization.

**Definition 1.2 (The entrywise strengthening for actual means).**

$$(claim) \Leftrightarrow (\forall m: \mathbb{N}, (1 \le m) \Rightarrow (\forall n: \mathbb{N}, (2 \le n) \Rightarrow (\forall w: \operatorname{Fin}\left(n\right) \to \mathbb{R}, (\forall j: \operatorname{Fin}\left(n\right), 0 < \operatorname{w}\left(j\right)) \Rightarrow ((\sum_{j} \operatorname{w}\left(j\right) = 1) \Rightarrow (\forall A: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), (\forall j: \operatorname{Fin}\left(n\right), \operatorname{PosDef}\left(\operatorname{A}\left(j\right)\right)) \Rightarrow (\operatorname{SpectralOrder}\left(\operatorname{logEuclidean}\left(w, A\right), \operatorname{wassersteinBarycenter}\left(w, A\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/HwangKimWeightedSpectralRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jinmi Hwang; Sejong Kim (2024). *Near-order relation of power means*. DOI: [10.1007/s11117-024-01099-4](https://doi.org/10.1007/s11117-024-01099-4). URL: <https://arxiv.org/abs/2407.07438v1>.

*Commentary.*

For every complex dimension m≥1, input count n≥2, strictly positive normalized weights and positive definite inputs, ask whether LE≤λΩ holds for the actual CFC logarithmic mean and epsilon-selected positive definite global argmin. The complete quantifiers are retained; the proof supplies the specified 2×2 weighted counterexample.

**Theorem 1.3 (The specified unequal-weight witness refutes the comparison).**

$$\neg (\forall m: \mathbb{N}, (1 \le m) \Rightarrow (\forall n: \mathbb{N}, (2 \le n) \Rightarrow (\forall w: \operatorname{Fin}\left(n\right) \to \mathbb{R}, (\forall j: \operatorname{Fin}\left(n\right), 0 < \operatorname{w}\left(j\right)) \Rightarrow ((\sum_{j} \operatorname{w}\left(j\right) = 1) \Rightarrow (\forall A: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), (\forall j: \operatorname{Fin}\left(n\right), \operatorname{PosDef}\left(\operatorname{A}\left(j\right)\right)) \Rightarrow (\operatorname{SpectralOrder}\left(\operatorname{logEuclidean}\left(w, A\right), \operatorname{wassersteinBarycenter}\left(w, A\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HwangKimWeightedSpectralRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinmi Hwang; Sejong Kim (2024). *Near-order relation of power means*. DOI: [10.1007/s11117-024-01099-4](https://doi.org/10.1007/s11117-024-01099-4). URL: <https://arxiv.org/abs/2407.07438v1>.

*Commentary.*

Use weights (3/4,1/4), A=diag(256,1), B=[[13,3√3],[3√3,7]]/4. Both inputs are positive definite. Put h=√399, K=[[9,2√3],[2√3,90]]/(4h), M=(3I+K)/4 and W=MAM. Exact multiplication proves KAK=B. The positive transports T=M⁻¹ and V=KM⁻¹ obey (3/4)T+(1/4)V=I and transport W to A,B. BuresWassersteinTransport.finite_barycenter_of_dual identifies this W with the actual unique global argmin. Thus the finite theorem has a concrete live mathematical consumer. The logarithmic sum is log(2)H, H=[[51,√3],[√3,1]]/8. Orthogonal diagonalization of B identifies its actual logarithm. Positive definiteness of H−I/10 and (107/100)^10<2 imply that L−(107/100)I is positive definite by continuous functional calculus. This proves λmin(L)>107/100 without assuming the desired spectral bound. The source's exact expression λmin(L)=2^((13−√157)/4) is preserved as written scientific context; that expression is not a separately asserted Lean endpoint. Exact trace and determinant calculations give tr W=1159/8+3591/(16h), det W=(73/8+297/(4h))². The rational brackets 1997/100<h<999/50 prove q²−tr(W)q+det W<0 at q=107/100, hence λmin(W)<q. Combining these strict bounds refutes the universal entrywise comparison for the actual means. The same actual pair fails near order: if C=L⁻¹#W≥I, then C²≥I and W−qI=C(L−qI)C+q(C²−I) is positive semidefinite. Its negative determinant at q=107/100 contradicts this. This exact application was kernel-checked; it is an application of the retained bounds and Riccati suppliers. Source: Ma–Zhang revision2 Theorem (entrywise), CC BY 4.0. Haobo Ma: ChronoAI Pte Ltd, Singapore only. Wenlin Zhang: NUS and ChronoAI Pte Ltd, Singapore. This is a formal return of their written witness, not a new discovery. The established transport criterion is credited to Bhatia–Jain–Lim. Their Theorem 1 weak log-majorization and (54) LE≤λQ₁/₂ remain valid; the witness therefore separates weak log-majorization from entrywise order and obstructs the unposed stronger entrywise Q₁/₂≤λΩ reading, as attributed mathematical consequences. Q₁/₂≠Ω, and their actual Conjecture 1 on unitarily invariant norms / weak majorization is not refuted. The theorem itself refutes the entrywise claim; the full all-dimension/input-count families, commuting equality case, near-to-entrywise bridge and literature comparison consumers remain separate proof obligations and are not assumed as axioms.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HwangKimWeightedSpectralRefutation.SpectralOrder`
- Truth anchor: `D5/S3/Quantum/Matrix/HwangKimWeightedSpectralRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/HwangKimWeightedSpectralRefutation.result`
- Dependency: [D5/S3/Quantum/Matrix/BuresWassersteinTransport](BuresWassersteinTransport.md)
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/ScalarPerturbation](LinGProperty/ScalarPerturbation.md)
