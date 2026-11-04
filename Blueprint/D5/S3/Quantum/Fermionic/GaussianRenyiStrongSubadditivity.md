# Strong subadditivity of fermionic Gaussian Renyi entropy

## Abstract

Fermionic Gaussian Renyi covariance entropy satisfies strong subadditivity for every real order strictly between zero and one.

**Definition 1.1 (Physical fermionic covariances).**

$$\forall (n: \mathbb{N}), (\forall (G: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)), \mathbb{R}\right)), (\operatorname{physicalCovariance}\left(G\right) = \left((\operatorname{Matrix.transpose}\left(G\right) = -(G)) \land (\exists (h: \operatorname{Matrix.IsHermitian}\left((\operatorname{Complex.I}) \cdot (\operatorname{Matrix.map}\left(G, \operatorname{Complex.ofReal}\right))\right)), (\forall (i: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right))), (\left|\operatorname{Matrix.IsHermitian.eigenvalues}\left(h, i\right)\right| \le 1)))\right)))$$

*Formalization.* `D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity.physicalCovariance` (`✓ std3`).

*Citation.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

A covariance is a real antisymmetric matrix on the two Majorana indices of each mode. Multiplication by i after embedding its entries into the complex numbers gives a Hermitian matrix whose real eigenvalues have absolute value at most one. This encodes the fermionic covariance condition and the paired spectrum described by Camilo, Landi and Eliëns (RenyiGaussian_v2.tex, lines 265–285).

**Definition 1.2 (Entropy from the full Majorana spectrum).**

$$\forall (n: \mathbb{N}), (\forall (X: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), (\forall (\alpha: \mathbb{R}), (\forall (G: \operatorname{Matrix}\left(\operatorname{Subtype}\left(\lambda (p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right))) \mapsto (\operatorname{Prod.fst}\left(p\right) \in X)\right), \operatorname{Subtype}\left(\lambda (p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right))) \mapsto (\operatorname{Prod.fst}\left(p\right) \in X)\right), \mathbb{R}\right)), ((\operatorname{fermionicGaussianRenyiEntropy}\left(\alpha, G\right): \mathbb{R}) = \operatorname{dite}\left(\operatorname{Matrix.IsHermitian}\left((\operatorname{Complex.I}) \cdot (\operatorname{Matrix.map}\left(G, \operatorname{Complex.ofReal}\right))\right), \lambda (h: \operatorname{Matrix.IsHermitian}\left((\operatorname{Complex.I}) \cdot (\operatorname{Matrix.map}\left(G, \operatorname{Complex.ofReal}\right))\right)) \mapsto (((\frac{1}{2}: \mathbb{R})) \cdot (\sum_{i: \operatorname{Subtype}\left(\lambda (p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right))) \mapsto (\operatorname{Prod.fst}\left(p\right) \in X)\right)} (\operatorname{D5.S3.Quantum.Analysis.FermionicRenyiStieltjes.fermionicRenyiFunction}\left(\alpha, \operatorname{Matrix.IsHermitian.eigenvalues}\left(h, i\right)\right)))), \operatorname{Function.const}\left(\neg (\operatorname{Matrix.IsHermitian}\left((\operatorname{Complex.I}) \cdot (\operatorname{Matrix.map}\left(G, \operatorname{Complex.ofReal}\right))\right)), (0: \mathbb{R})\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity.fermionicGaussianRenyiEntropy` (`✓ std3`).

*Citation.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

For a matrix on the Majorana indices of a mode set X, take one half of the sum of fermionicRenyiFunction over every eigenvalue of iG. The two signs of each mode contribute the same scalar entropy, so this is Eq. renyi_fermionic_1, equivalently Eq. renyi_fermionic_3 (RenyiGaussian_v2.tex, lines 297–320). The definition assigns zero if iG is not Hermitian and also gives zero on an empty index type.

**Definition 1.3 (The fermionic strong subadditivity proposition).**

$$\operatorname{claim} = (\forall (n: \mathbb{N}), (\forall (G: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)), \mathbb{R}\right)), ((\operatorname{physicalCovariance}\left(G\right)) \Rightarrow (\forall (A: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), (\forall (B: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), (\forall (C: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((\operatorname{Disjoint}\left(A, B\right)) \Rightarrow ((\operatorname{Disjoint}\left(A, C\right)) \Rightarrow ((\operatorname{Disjoint}\left(B, C\right)) \Rightarrow (\forall (\alpha: \mathbb{R}), ((0 < \alpha) \Rightarrow ((\alpha < 1) \Rightarrow ((\operatorname{fermionicGaussianRenyiEntropy}\left(\alpha, \operatorname{D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.reducedCovariance}\left(G, (A) \cup (B)\right)\right)) + (\operatorname{fermionicGaussianRenyiEntropy}\left(\alpha, \operatorname{D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.reducedCovariance}\left(G, (B) \cup (C)\right)\right)) \ge (\operatorname{fermionicGaussianRenyiEntropy}\left(\alpha, \operatorname{D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.reducedCovariance}\left(G, ((A) \cup (B)) \cup (C)\right)\right)) + (\operatorname{fermionicGaussianRenyiEntropy}\left(\alpha, \operatorname{D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.reducedCovariance}\left(G, B\right)\right)))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

For every physical covariance and every three pairwise disjoint mode sets A, B and C, the AB and BC entropies sum to at least the ABC and B entropies for 0<α<1. The principal blocks are given by D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.reducedCovariance, which retains both Majorana indices of every selected mode. The source conjectures validity on [0,1] rather than asserting a proof (RenyiGaussian_v2.tex, line 498); its conditional mutual information is Eq. RCMI, lines 122–125. This proposition covers the open interval using the covariance entropy formula. The endpoint orders, a density-operator construction and non-Gaussian states are outside the statement.

**Theorem 1.4 (Strong subadditivity of the covariance entropy).**

$$\forall (n: \mathbb{N}), (\forall (G: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)), \mathbb{R}\right)), ((\operatorname{physicalCovariance}\left(G\right)) \Rightarrow (\forall (A: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), (\forall (B: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), (\forall (C: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((\operatorname{Disjoint}\left(A, B\right)) \Rightarrow ((\operatorname{Disjoint}\left(A, C\right)) \Rightarrow ((\operatorname{Disjoint}\left(B, C\right)) \Rightarrow (\forall (\alpha: \mathbb{R}), ((0 < \alpha) \Rightarrow ((\alpha < 1) \Rightarrow ((\operatorname{fermionicGaussianRenyiEntropy}\left(\alpha, \operatorname{D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.reducedCovariance}\left(G, (A) \cup (B)\right)\right)) + (\operatorname{fermionicGaussianRenyiEntropy}\left(\alpha, \operatorname{D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.reducedCovariance}\left(G, (B) \cup (C)\right)\right)) \ge (\operatorname{fermionicGaussianRenyiEntropy}\left(\alpha, \operatorname{D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.reducedCovariance}\left(G, ((A) \cup (B)) \cup (C)\right)\right)) + (\operatorname{fermionicGaussianRenyiEntropy}\left(\alpha, \operatorname{D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.reducedCovariance}\left(G, B\right)\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity.result` (`✓ std3`). ∎

*Resolves.* `Problems/camilo-landi-eliens-2019-fermionic-gaussian-renyi-strong-subadditivity` (proved) by `D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"camilo-landi-eliens-2019-fermionic-gaussian-renyi-strong-subadditivity","declaration_gid":"D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

Antisymmetry of the real covariance makes iG Hermitian. Unitary diagonalization identifies the eigenvalues of I+iuG as 1+uλ, where λ ranges over the eigenvalues of iG. The spectral bound gives positive semidefiniteness at u=1. The identity I+iuG=u(I+iG)+(1−u)I and shifted_posDef then give positive definiteness for 0≤u<1. Principal restriction commutes with the interpolation. Positivity at u=1 and u=−1 passes to each principal block and bounds its Hermitian eigenvalues between minus one and one; antisymmetry also passes to these blocks. Here each reduction is the principal block supplied by D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.reducedCovariance.

The spectral determinant identity det_spectral gives det(I+iuG) as the product of the factors 1+uλ over the eigenvalues λ of iG. Transposition changes u to −u without changing the determinant. Multiplying the spectral products at u and −u expresses det(I+iuG) squared as the product of the factors 1−u²λ². Each such factor and the determinant are positive for 0≤u<1. Taking logarithms gives log(det(I+iuG)) as one half of the sum of these scalar logarithms.

Apply stieltjes_representation to each eigenvalue of the reduced covariance. Its integrable logarithmic integrand permits interchange of the finite sum and integral. There are twice as many Majorana indices as selected modes, by reduced_card. Consequently the entropy of a block X is |X| log 2 plus the integral on (0,1) of fermionicWeight(α,u) times log(det(I+iuG_X)). This is the positive Stieltjes mixture S_α(G_X)=|X| ln 2+∫₀¹ v_α(u) ln det(I+iuG_X) du, with v_α given by fermionicWeight. It includes pure modes because the scalar representation includes both spectral endpoints.

For each u in (0,1), apply log_koteljanskii to the Hermitian positive definite matrix I+iuG and the three disjoint Majorana index sets A×Fin 2, B×Fin 2 and C×Fin 2. The four principal determinants on ABC, B, AB and BC agree with the determinants of the corresponding reduced interpolations, since their index subtypes are equivalent. Thus the ABC and B logarithms sum to at most the AB and BC logarithms. Multiply by the strictly positive fermionicWeight and integrate. Integrability of all four weighted logarithms justifies splitting the integrals. Finally, |A∪B|+|B∪C|=|A∪B∪C|+|B|, also after casting these natural cardinalities to the real numbers, cancels the multiples of log 2 in the four mixture identities. The remaining inequality is the asserted strong subadditivity.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity.claim`
- Truth anchor: `D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity.fermionicGaussianRenyiEntropy`
- Truth anchor: `D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity.physicalCovariance`
- Truth anchor: `D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity.result`
- Dependency: [D5/S3/Quantum/Analysis/FermionicRenyiStieltjes](../Analysis/FermionicRenyiStieltjes.md)
- Dependency: [D5/S3/Quantum/Subentropy/DensityKernel](../Subentropy/DensityKernel.md)
- Dependency: [D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity](../Thermal/GaussianRenyiStrongSubadditivity.md)
