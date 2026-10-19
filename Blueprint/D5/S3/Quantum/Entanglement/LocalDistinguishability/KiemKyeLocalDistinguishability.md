# Local distinguishability at boundary projection states

## Abstract

Adjacent trace-one blockpositive sets are locally distinguishable at every boundary projection state.

Complex vectors have coordinates Fin m × Fin n. Operators are Matrix (Fin m × Fin n) (Fin m × Fin n) Complex. EuclideanSpace supplies the Hilbert norm. The imported schmidtRank is the rank of the coefficient matrix with entry x(i,j). Matrix.mulVec is matrix-vector multiplication, dotProduct is the coordinate sum, star is coordinatewise conjugation, and Complex.re is the real part. The topology is the finite-dimensional matrix topology.

**Definition 1.1 (The trace-one Hermitian affine space).**

$$\forall (m: Nat), (\forall (n: Nat), (\operatorname{ambient}\left(m, n\right) = \{W: \operatorname{Matrix}\left((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), Complex\right) \mid (\operatorname{Matrix}.\operatorname{IsHermitian}\left(W\right)) \land (\operatorname{Matrix}.\operatorname{trace}\left(W\right) = 1)\}))$$

*Formalization.* `D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.ambient` (`✓ std3`).

*Citation.* Young-Hoon Kiem; Seung-Hyeok Kye (2026). *Local geometry for Schmidt number witnesses*. DOI: [10.48550/arXiv.2608.14199](https://doi.org/10.48550/arXiv.2608.14199). URL: <https://arxiv.org/abs/2608.14199v1>.

*Commentary.*

Section 3, page 7, uses the affine subspace H of Hermitian matrices with trace one. Both conditions are included.

**Definition 1.2 (The blockpositive sets).**

$$\forall (m: Nat), (\forall (n: Nat), (\forall (k: Nat), (\operatorname{BP}\left(m, n, k\right) = \{W: \operatorname{Matrix}\left((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), Complex\right) \mid (W \in \operatorname{ambient}\left(m, n\right)) \land (\forall (x: (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \to Complex), ((\operatorname{schmidtRank}\left(x\right) \le k) \Rightarrow (0 \le \operatorname{Complex}.\operatorname{re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(x\right), \operatorname{Matrix}.\operatorname{mulVec}\left(W, x\right)\right)\right))))\})))$$

*Formalization.* `D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.BP` (`✓ std3`).

*Citation.* Young-Hoon Kiem; Seung-Hyeok Kye (2026). *Local geometry for Schmidt number witnesses*. DOI: [10.48550/arXiv.2608.14199](https://doi.org/10.48550/arXiv.2608.14199). URL: <https://arxiv.org/abs/2608.14199v1>.

*Commentary.*

Section 3, page 7: “A Hermitian matrix W ∈ M_m ⊗ M_n is called k-blockpositive if ⟨ξ|W|ξ⟩ ≥ 0 for every |ξ⟩ with SR |ξ⟩ ≤ k.” BP restricts this condition to the trace-one affine space. For Hermitian W the quadratic form is real, so the displayed real-part inequality is the same condition.

**Definition 1.3 (A normalized orthogonal projection).**

$$\forall (m: Nat), (\forall (n: Nat), (\forall (E: \operatorname{Submodule}\left(Complex, \operatorname{EuclideanSpace}\left(Complex, (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right))\right)\right)), (\operatorname{rhoPerp}\left(E\right) = \operatorname{SMul}.\operatorname{smul}\left((\operatorname{Module}.\operatorname{finrank}\left(Complex, E^{\perp}\right): Complex)^{-1}, \operatorname{Matrix}.\operatorname{toEuclideanLin}.\operatorname{symm}\left(E^{\perp}.\operatorname{starProjection}.\operatorname{toLinearMap}\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.rhoPerp` (`✓ std3`).

*Citation.* Young-Hoon Kiem; Seung-Hyeok Kye (2026). *Local geometry for Schmidt number witnesses*. DOI: [10.48550/arXiv.2608.14199](https://doi.org/10.48550/arXiv.2608.14199). URL: <https://arxiv.org/abs/2608.14199v1>.

*Commentary.*

Sections 3 and 5 write ϱ_{E⊥} for the projection state onto E⊥. Submodule.starProjection is orthogonal projection, Matrix.toEuclideanLin.symm gives its coordinate matrix, and the inverse of the complex dimension normalizes its trace when E is proper. The definition also has a value for E equal to the whole space, where the dimension is zero; that case is excluded from the conclusion.

**Definition 1.4 (Boundary relative to the affine space).**

$$\forall (m: Nat), (\forall (n: Nat), (\forall (k: Nat), (\forall (rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), Complex\right)), (\operatorname{OnBoundary}\left(m, n, k, rho\right) \Leftrightarrow ((rho \in \operatorname{BP}\left(m, n, k\right)) \land (rho \in \operatorname{closure}\left((\operatorname{ambient}\left(m, n\right) \setminus \operatorname{BP}\left(m, n, k\right))\right)))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.OnBoundary` (`✓ std3`).

*Citation.* Young-Hoon Kiem; Seung-Hyeok Kye (2026). *Local geometry for Schmidt number witnesses*. DOI: [10.48550/arXiv.2608.14199](https://doi.org/10.48550/arXiv.2608.14199). URL: <https://arxiv.org/abs/2608.14199v1>.

*Commentary.*

The boundary is relative to the trace-one Hermitian space. The set BP is closed there: it is the intersection of the closed nonnegative quadratic-form tests. Thus the two membership conditions express the relative boundary.

**Definition 1.5 (Every neighbourhood meets the difference).**

$$\forall (m: Nat), (\forall (n: Nat), (\forall (C: \operatorname{Set}\left(\operatorname{Matrix}\left((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), Complex\right)\right)), (\forall (D: \operatorname{Set}\left(\operatorname{Matrix}\left((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), Complex\right)\right)), (\forall (x: \operatorname{Matrix}\left((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), Complex\right)), (\operatorname{LocallyDistinguishable}\left(C, D, x\right) \Leftrightarrow (\forall (N: \operatorname{Set}\left(\operatorname{Matrix}\left((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), Complex\right)\right)), ((N \in \operatorname{nhds}\left(x\right)) \Rightarrow (\operatorname{Set}.\operatorname{Nonempty}\left(\operatorname{Set}.\operatorname{inter}\left(N, (C \setminus D)\right)\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.LocallyDistinguishable` (`✓ std3`).

*Citation.* Young-Hoon Kiem; Seung-Hyeok Kye (2026). *Local geometry for Schmidt number witnesses*. DOI: [10.48550/arXiv.2608.14199](https://doi.org/10.48550/arXiv.2608.14199). URL: <https://arxiv.org/abs/2608.14199v1>.

*Commentary.*

Section 2, page 6: “Suppose that closed convex sets C and D with the inclusion C ⊃ D share a boundary point x₀. We say that C ⊃ D is locally distinguishable around x₀ if the set N ∩ (C∖D) is nonempty for every neighborhood N of x₀.” The predicate displays the neighbourhood condition; the source's standing geometric conditions hold for the sets and states in the conclusion. Ambient matrix neighbourhoods give the same condition as relative neighbourhoods because the difference lies in H.

**Definition 1.6 (The Kiem–Kye conjecture).**

$$claim \Leftrightarrow (\forall (m: Nat), (\forall (n: Nat), (\forall (E: \operatorname{Submodule}\left(Complex, \operatorname{EuclideanSpace}\left(Complex, (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right))\right)\right)), ((E \ne \operatorname{Bot}.\operatorname{bot}) \Rightarrow ((E \ne \operatorname{Top}.\operatorname{top}) \Rightarrow (\forall (k: Nat), (\forall (l: Nat), ((1 \le k) \Rightarrow ((k \le l) \Rightarrow ((l < \operatorname{min}\left(m, n\right)) \Rightarrow ((\operatorname{OnBoundary}\left(m, n, k, \operatorname{rhoPerp}\left(E\right)\right)) \Rightarrow (\operatorname{LocallyDistinguishable}\left(\operatorname{BP}\left(m, n, l\right), \operatorname{BP}\left(m, n, l + 1\right), \operatorname{rhoPerp}\left(E\right)\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.claim` (`✓ std3`).

*Citation.* Young-Hoon Kiem; Seung-Hyeok Kye (2026). *Local geometry for Schmidt number witnesses*. DOI: [10.48550/arXiv.2608.14199](https://doi.org/10.48550/arXiv.2608.14199). URL: <https://arxiv.org/abs/2608.14199v1>.

*Commentary.*

Section 5, page 12: “For non-generic cases, we cannot show the existence of Schmidt number witnesses around ϱ_{E⊥} by the method in this paper. Nevertheless, we conjecture that the inclusion BP_ℓ ⊋ BP_{ℓ+1} is locally distinguishable around ϱ_{E⊥} for ℓ ≥ k, whenever ϱ_{E⊥} is on the boundary of the convex set BP_k.” Here m and n are the local dimensions, E is nonzero and proper, k and l are natural numbers with 1 ≤ k ≤ l < min(m,n), and rhoPerp(E) is ϱ_{E⊥}. These bounds are the range of adjacent sets in the source's finite chain. No genericity assumption is imposed.

**Theorem 1.7 (Local distinguishability for every subspace).**

$$\forall (m: Nat), (\forall (n: Nat), (\forall (E: \operatorname{Submodule}\left(Complex, \operatorname{EuclideanSpace}\left(Complex, (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right))\right)\right)), ((E \ne \operatorname{Bot}.\operatorname{bot}) \Rightarrow ((E \ne \operatorname{Top}.\operatorname{top}) \Rightarrow (\forall (k: Nat), (\forall (l: Nat), ((1 \le k) \Rightarrow ((k \le l) \Rightarrow ((l < \operatorname{min}\left(m, n\right)) \Rightarrow ((\operatorname{OnBoundary}\left(m, n, k, \operatorname{rhoPerp}\left(E\right)\right)) \Rightarrow (\operatorname{LocallyDistinguishable}\left(\operatorname{BP}\left(m, n, l\right), \operatorname{BP}\left(m, n, l + 1\right), \operatorname{rhoPerp}\left(E\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Young-Hoon Kiem; Seung-Hyeok Kye (2026). *Local geometry for Schmidt number witnesses*. DOI: [10.48550/arXiv.2608.14199](https://doi.org/10.48550/arXiv.2608.14199). URL: <https://arxiv.org/abs/2608.14199v1>.

*Commentary.*

A positive semidefinite matrix on the boundary has a unit kernel vector of Schmidt rank at most k. Compactness of the unit low-rank vectors makes the projection of the nonpositive quadratic-form tests closed, which supplies this kernel vector at a boundary limit.

A rank-one perturbation raises a rectangular coefficient matrix's rank by one: a dual vector nonzero on its kernel is paired with a vector outside its range. Rank–nullity identifies the new kernel as the intersection of two kernels. Repetition and normalization place the old unit vector in the closure of the unit vectors of rank l+1.

Compression by I−uu† moves the kernel to u while preserving positivity. Its trace tends to one near the original kernel vector, so normalized compression is continuous there. For each unit u of rank l+1, compactness gives an overlap bound α<1 on unit vectors of rank at most l. The matrix Q=αI−uu† is nonnegative on all those vectors and negative at u. Adding a small positive multiple of Q to the compressed state and normalizing the trace produces a matrix in BP_l outside BP_(l+1). Two closure arguments return to the original state. The same sufficient condition applies to any positive semidefinite trace-one matrix with a unit kernel vector of Schmidt rank at most l+1. No convergence rate or converse characterization is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.BP`
- Truth anchor: `D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.LocallyDistinguishable`
- Truth anchor: `D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.OnBoundary`
- Truth anchor: `D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.ambient`
- Truth anchor: `D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.rhoPerp`
- Dependency: [D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation](../WitnessKernelTraceCriteriaRefutation.md)
- Dependency: [D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction](../../Information/SeparableStateLocalUnitaryStabilizerObstruction.md)
- Dependency: [D5/S3/Quantum/Reduction/IsometricCompression](../../Reduction/IsometricCompression.md)
