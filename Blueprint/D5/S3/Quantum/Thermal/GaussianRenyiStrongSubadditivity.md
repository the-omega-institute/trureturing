# Strong subadditivity of bosonic Gaussian Renyi entropy

## Abstract

Bosonic Gaussian Renyi entropy satisfies strong subadditivity for every order from zero to two, with zero and one excluded.

**Definition 1.1 (The canonical symplectic form).**

$$\forall (n: \mathbb{N}), ((\operatorname{symplecticForm}\left(n\right): \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)), \mathbb{R}\right)) = \operatorname{let} e:= \operatorname{Equiv.trans}\left(\operatorname{Equiv.trans}\left(\operatorname{Equiv.prodComm}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Equiv.prodCongr}\left(\operatorname{finTwoEquiv}, \operatorname{Equiv.refl}\left(\operatorname{Fin}\left(n\right)\right)\right)\right), \operatorname{Equiv.boolProdEquivSum}\left(\operatorname{Fin}\left(n\right)\right)\right); \operatorname{Matrix.submatrix}\left(-(\operatorname{Matrix.J}\left(\operatorname{Fin}\left(n\right), \mathbb{R}\right)), \operatorname{Equiv.toFun}\left(e\right), \operatorname{Equiv.toFun}\left(e\right)\right))$$

*Formalization.* `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.symplecticForm` (`✓ std3`).

*Citation.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

The quadrature indices are pairs in Fin n × Fin 2. Reindexing the negative standard symplectic matrix by e gives the direct sum of n copies of the matrix with rows (0,1) and (−1,0). This is the form in the bosonic commutation relations of RenyiGaussian_v2.tex, lines 179–186.

**Definition 1.2 (The uncertainty condition on a finite index type).**

$$\forall (\iota: \operatorname{Type}), ([\operatorname{Fintype}\left(\iota\right)] [\operatorname{DecidableEq}\left(\iota\right)] \forall (V: \operatorname{Matrix}\left(\iota, \iota, \mathbb{R}\right)), (\forall (\omega: \operatorname{Matrix}\left(\iota, \iota, \mathbb{R}\right)), (\operatorname{physicalOn}\left(V, \omega\right) = \left((\operatorname{Matrix.IsSymm}\left(V\right)) \land (\operatorname{Matrix.PosSemidef}\left((\operatorname{Matrix.map}\left(V, \operatorname{Complex.ofReal}\right)) + ((\operatorname{Complex.I}) \cdot (\operatorname{Matrix.map}\left(\omega, \operatorname{Complex.ofReal}\right)))\right))\right))))$$

*Formalization.* `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.physicalOn` (`✓ std3`).

*Citation.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

For arbitrary finite indices, V must be real symmetric and V+iω must be positive semidefinite. With the canonical symplectic form this is the bosonic uncertainty condition. The source writes V−iΩ in RenyiGaussian_v2.tex, lines 194–198, with Ω for the matrix ω here; for real V and ω, complex conjugation makes the two sign conventions equivalent.

**Definition 1.3 (Physical bosonic covariances).**

$$\forall (n: \mathbb{N}), (\forall (V: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)), \mathbb{R}\right)), (\operatorname{physicalCovariance}\left(V\right) = \operatorname{D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation.IsGaussianMeasurementCov}\left(\operatorname{Matrix.submatrix}\left(V, \operatorname{Equiv.toFun}\left(\operatorname{Equiv.trans}\left(\operatorname{finCongr}\left(\operatorname{Nat.mul_{comm}}\left(2, n\right)\right), \operatorname{Equiv.symm}\left(\operatorname{finProdFinEquiv}\left(n, 2\right)\right)\right)\right), \operatorname{Equiv.toFun}\left(\operatorname{Equiv.trans}\left(\operatorname{finCongr}\left(\operatorname{Nat.mul_{comm}}\left(2, n\right)\right), \operatorname{Equiv.symm}\left(\operatorname{finProdFinEquiv}\left(n, 2\right)\right)\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.physicalCovariance` (`✓ std3`).

*Citation.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

The covariance is reindexed from mode–quadrature pairs to Fin (2*n) and tested by IsGaussianMeasurementCov. The index permutation identifies its uncertainty matrix with V+i symplecticForm(n), so this is the same bona fide covariance condition in RenyiGaussian_v2.tex, lines 188–198.

**Definition 1.4 (Reduction to a set of modes).**

$$\forall (n: \mathbb{N}), (\forall (V: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)), \mathbb{R}\right)), (\forall (X: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((\operatorname{reducedCovariance}\left(V, X\right): \operatorname{Matrix}\left(\operatorname{Subtype}\left(\lambda (p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right))) \mapsto (\operatorname{Prod.fst}\left(p\right) \in X)\right), \operatorname{Subtype}\left(\lambda (p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right))) \mapsto (\operatorname{Prod.fst}\left(p\right) \in X)\right), \mathbb{R}\right)) = \operatorname{Matrix.submatrix}\left(V, \lambda (p: \operatorname{Subtype}\left(\lambda (q: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right))) \mapsto (\operatorname{Prod.fst}\left(q\right) \in X)\right)) \mapsto (\operatorname{Subtype.val}\left(p\right)), \lambda (p: \operatorname{Subtype}\left(\lambda (q: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right))) \mapsto (\operatorname{Prod.fst}\left(q\right) \in X)\right)) \mapsto (\operatorname{Subtype.val}\left(p\right))\right))))$$

*Formalization.* `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.reducedCovariance` (`✓ std3`).

*Citation.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

For a finite set X of modes, retain both quadratures of each member of X. The reduced covariance is the principal submatrix on these indices. The same restriction applies to the symplectic form. These are the covariance reductions used for the subsystem entropies in Eq. RCMI (RenyiGaussian_v2.tex, lines 122–125).

**Definition 1.5 (The Hermitian representative of the symplectic spectrum).**

$$\forall (\iota: \operatorname{Type}), ([\operatorname{Fintype}\left(\iota\right)] [\operatorname{DecidableEq}\left(\iota\right)] \forall (V: \operatorname{Matrix}\left(\iota, \iota, \mathbb{R}\right)), (\forall (\omega: \operatorname{Matrix}\left(\iota, \iota, \mathbb{R}\right)), ((\operatorname{symplecticOperator}\left(V, \omega\right): \operatorname{Matrix}\left(\iota, \iota, \mathbb{C}\right)) = ((\operatorname{CFC.sqrt}\left(\operatorname{Matrix.map}\left(V, \operatorname{Complex.ofReal}\right)\right)) \cdot ((\operatorname{Complex.I}) \cdot (\operatorname{Matrix.map}\left(\omega, \operatorname{Complex.ofReal}\right)))) \cdot (\operatorname{CFC.sqrt}\left(\operatorname{Matrix.map}\left(V, \operatorname{Complex.ofReal}\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.symplecticOperator` (`✓ std3`).

*Citation.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

Embed the real matrices into complex matrices and place iω between two copies of the positive square root of V. For a physical covariance the resulting matrix is Hermitian and has the spectrum of iωV. Its eigenvalues have absolute value at least one. This represents the symplectic eigenvalues described in RenyiGaussian_v2.tex, lines 201–205.

**Definition 1.6 (Entropy from the symplectic eigenvalues).**

$$\forall (\iota: \operatorname{Type}), ([\operatorname{Fintype}\left(\iota\right)] [\operatorname{DecidableEq}\left(\iota\right)] \forall (\alpha: \mathbb{R}), (\forall (V: \operatorname{Matrix}\left(\iota, \iota, \mathbb{R}\right)), (\forall (\omega: \operatorname{Matrix}\left(\iota, \iota, \mathbb{R}\right)), ((\operatorname{gaussianRenyiEntropy}\left(\alpha, V, \omega\right): \mathbb{R}) = \operatorname{dite}\left(\operatorname{Matrix.IsHermitian}\left(\operatorname{symplecticOperator}\left(V, \omega\right)\right), \lambda (h: \operatorname{Matrix.IsHermitian}\left(\operatorname{symplecticOperator}\left(V, \omega\right)\right)) \mapsto (((\frac{1}{2}: \mathbb{R})) \cdot (\sum_{i: \iota} (\operatorname{D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.renyiFunction}\left(\alpha, \left|\operatorname{Matrix.IsHermitian.eigenvalues}\left(h, i\right)\right|\right)))), \operatorname{Function.const}\left(\neg (\operatorname{Matrix.IsHermitian}\left(\operatorname{symplecticOperator}\left(V, \omega\right)\right)), (0: \mathbb{R})\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.gaussianRenyiEntropy` (`✓ std3`).

*Citation.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

When the symplectic operator is Hermitian, sum renyiFunction over the absolute values of all its eigenvalues and divide by two, accounting for the two signs of each symplectic eigenvalue. This gives Eq. renyi_bosonic_1 (RenyiGaussian_v2.tex, lines 216–220). The definition assigns zero in the non-Hermitian case. Empty mode sets also give zero.

**Definition 1.7 (Strong subadditivity for the stated orders).**

$$\operatorname{claim} = (\forall (n: \mathbb{N}), (\forall (V: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)), \mathbb{R}\right)), ((\operatorname{physicalCovariance}\left(V\right)) \Rightarrow (\forall (A: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), (\forall (B: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), (\forall (C: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((\operatorname{Disjoint}\left(A, B\right)) \Rightarrow ((\operatorname{Disjoint}\left(A, C\right)) \Rightarrow ((\operatorname{Disjoint}\left(B, C\right)) \Rightarrow (\forall (\alpha: \mathbb{R}), ((0 < \alpha) \Rightarrow ((\alpha \le 2) \Rightarrow ((\alpha \ne 1) \Rightarrow ((\operatorname{gaussianRenyiEntropy}\left(\alpha, \operatorname{reducedCovariance}\left(V, (A) \cup (B)\right), \operatorname{reducedCovariance}\left(\operatorname{symplecticForm}\left(n\right), (A) \cup (B)\right)\right)) + (\operatorname{gaussianRenyiEntropy}\left(\alpha, \operatorname{reducedCovariance}\left(V, (B) \cup (C)\right), \operatorname{reducedCovariance}\left(\operatorname{symplecticForm}\left(n\right), (B) \cup (C)\right)\right)) \ge (\operatorname{gaussianRenyiEntropy}\left(\alpha, \operatorname{reducedCovariance}\left(V, ((A) \cup (B)) \cup (C)\right), \operatorname{reducedCovariance}\left(\operatorname{symplecticForm}\left(n\right), ((A) \cup (B)) \cup (C)\right)\right)) + (\operatorname{gaussianRenyiEntropy}\left(\alpha, \operatorname{reducedCovariance}\left(V, B\right), \operatorname{reducedCovariance}\left(\operatorname{symplecticForm}\left(n\right), B\right)\right))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

For every physical bosonic covariance and all pairwise disjoint mode sets A, B and C, the sum of the AB and BC entropies dominates the sum of the ABC and B entropies whenever 0<α≤2 and α differs from one. This is the positive-order validity part of the conjecture in RenyiGaussian_v2.tex, line 463, whose proof is requested again at line 532. The statement concerns the covariance entropy formula; order zero, order one, orders above two, fermions and non-Gaussian states are outside its scope.

**Theorem 1.8 (Strong subadditivity of the covariance entropy).**

$$\forall (n: \mathbb{N}), (\forall (V: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)), \mathbb{R}\right)), ((\operatorname{physicalCovariance}\left(V\right)) \Rightarrow (\forall (A: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), (\forall (B: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), (\forall (C: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((\operatorname{Disjoint}\left(A, B\right)) \Rightarrow ((\operatorname{Disjoint}\left(A, C\right)) \Rightarrow ((\operatorname{Disjoint}\left(B, C\right)) \Rightarrow (\forall (\alpha: \mathbb{R}), ((0 < \alpha) \Rightarrow ((\alpha \le 2) \Rightarrow ((\alpha \ne 1) \Rightarrow ((\operatorname{gaussianRenyiEntropy}\left(\alpha, \operatorname{reducedCovariance}\left(V, (A) \cup (B)\right), \operatorname{reducedCovariance}\left(\operatorname{symplecticForm}\left(n\right), (A) \cup (B)\right)\right)) + (\operatorname{gaussianRenyiEntropy}\left(\alpha, \operatorname{reducedCovariance}\left(V, (B) \cup (C)\right), \operatorname{reducedCovariance}\left(\operatorname{symplecticForm}\left(n\right), (B) \cup (C)\right)\right)) \ge (\operatorname{gaussianRenyiEntropy}\left(\alpha, \operatorname{reducedCovariance}\left(V, ((A) \cup (B)) \cup (C)\right), \operatorname{reducedCovariance}\left(\operatorname{symplecticForm}\left(n\right), ((A) \cup (B)) \cup (C)\right)\right)) + (\operatorname{gaussianRenyiEntropy}\left(\alpha, \operatorname{reducedCovariance}\left(V, B\right), \operatorname{reducedCovariance}\left(\operatorname{symplecticForm}\left(n\right), B\right)\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.result` (`✓ std3`). ∎

*Resolves.* `Problems/camilo-landi-eliens-2019-bosonic-gaussian-renyi-strong-subadditivity` (proved) by `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"camilo-landi-eliens-2019-bosonic-gaussian-renyi-strong-subadditivity","declaration_gid":"D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

First identify the canonical uncertainty condition under the quadrature permutation. The symplectic form squares to minus the identity, as does its restriction to any full set of mode quadratures. The two positive semidefinite matrices V+iω and V−iω have average V. If V has a kernel vector, positivity forces it into the kernel of each uncertainty matrix and hence into the kernel of ω; invertibility of ω rules this out. Thus V is positive definite. These facts pass to each reduced covariance, whose index cardinality is twice the number of retained modes.

Put J=iω, S=V^(1/2) and M=SJS. The matrix M is Hermitian and invertible. Congruencing the two uncertainty matrices by JS gives M²+M and M²−M positive semidefinite. Evaluating their quadratic forms on normalized eigenvectors gives λ²+λ≥0 and λ²−λ≥0. Since λ is nonzero, |λ|≥1. For 0≤x<1, the interpolation H_x=V+ixω=x(V+iω)+(1−x)V is Hermitian positive definite, and its principal blocks are the corresponding interpolations of the reduced covariances.

To compute its determinant, use equality of the characteristic polynomials of SJS and JV, together with −J H_(−t)=tI−JV. Since J²=I and H_x transposed equals H_(−x), multiplication of the characteristic products at x and −x gives det(H_x)² equal to the product of λ²−x² over all eigenvalues λ of M. Every factor and det(H_x) are positive. Taking logarithms gives log(det(H_x)) equal to one half the sum of log(λ²−x²). Apply stieltjes_representation to each |λ| and interchange the finite sum and integrals. The resulting positive Stieltjes mixture is S_α(V)=n c_α+∫₀¹ w_α(x) log(det(V+ixω)) dx for 0<α<2, α different from one; its logarithmic integrand is integrable, including when a symplectic eigenvalue equals one.

At order two, renyiFunction(2,ν)=log(ν). The determinant identity at x=0 therefore gives S_2(V)=one half of log(det(V)). This also applies to every reduced covariance.

For a positive definite Hermitian block matrix with leading block P, off-diagonal block X and trailing block Q, the Schur complement Q−XᴴP⁻¹X is positive definite and det(H)=det(P) det(Q−XᴴP⁻¹X). The complement is at most Q in the positive semidefinite order; log_det_mono gives determinant monotonicity, and hence the Fischer product bound. Eliminate the common block B of the matrix on B together with A and C, then apply that product bound to the A and C blocks of the remaining Schur complement. Restriction commutes with this complement. The determinant factors give Koteljanskii’s inequality det(H_ABC) det(H_B)≤det(H_AB) det(H_BC). Positivity of all determinants converts it into the corresponding sum of logarithms. Empty blocks have determinant one and are included.

Apply this logarithmic inequality to H_x on the four blocks AB, BC, ABC and B, using the disjoint quadrature sets associated with A, B and C. For 0<α<2 with α different from one, multiply the pointwise inequality by the positive weight w_α(x), integrate on (0,1), and use the integrability supplied by the Stieltjes mixture. The identity |A∪B|+|B∪C|=|A∪B∪C|+|B| also holds after casting the cardinalities to the real numbers and cancels the additive multiples of c_α. This gives the asserted entropy inequality. At α=2, apply the same logarithmic inequality at x=0 and multiply by one half.

## References

- Truth anchor: `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.claim`
- Truth anchor: `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.gaussianRenyiEntropy`
- Truth anchor: `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.physicalCovariance`
- Truth anchor: `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.physicalOn`
- Truth anchor: `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.reducedCovariance`
- Truth anchor: `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.result`
- Truth anchor: `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.symplecticForm`
- Truth anchor: `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.symplecticOperator`
- Dependency: [D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation](../../Estimation/GaussianThermometryJointMeasurementRefutation.md)
- Dependency: [D5/S3/Quantum/Analysis/BosonicRenyiStieltjes](../Analysis/BosonicRenyiStieltjes.md)
- Dependency: [D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction](../Entanglement/ChoiKiemKye/ConstructionReduction.md)
- Dependency: [D5/S3/Resource/LogDet/LogDetInformationSubmodularity](../../Resource/LogDet/LogDetInformationSubmodularity.md)
