# Singlet exclusion for the equal-spin diamond

## Abstract

For every positive integer spin, the coefficient-one diamond has no singlet ground vector in its entire zero-weight sector.

Let S be a natural number. Each of the four factors is the complete complex spin-S space with orthonormal basis indexed by W(S) = Fin(2S+1). Index r has weight S−r; the native normalized raising matrix Jplus(2S) has coefficient √((r+1)(2S−r)) from r+1 to r, with zero endpoint, and lowering is its adjoint. Put C(S) = Fin(4) → W(S), V(S) = C(S) → ℂ and O(S) = Matrix(C(S),C(S),ℂ). Norms are the Euclidean norms and inner products conjugate the first argument. Matrices act on every complex superposition in V(S). Sites 0,1,2,3 correspond to vertices 1,2,3,4. A submodule infimum denotes intersection; bottom is the zero submodule.

**Definition 1.1 (The ground energy).**

$$\forall (S: \mathbb{N}), (\operatorname{groundEnergy}\left(S\right) = \operatorname{sInf}\left(\operatorname{spectrumReal}\left(\operatorname{restrictedHamiltonian}\left(S\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.groundEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The restricted Hermitian matrix has finite nonempty real spectrum. Its infimum belongs to that spectrum and is its least element, so groundEnergy is the actual attained minimum.

**Definition 1.2 (The entire zero-weight ground eigenspace).**

$$\forall (S: \mathbb{N}), (\operatorname{groundSpace}\left(S\right) = \operatorname{inf}\left(\operatorname{ker}\left(\operatorname{hamiltonian}\left(S\right) - \operatorname{ofReal}\left(\operatorname{groundEnergy}\left(S\right)\right) \cdot 1\right), \operatorname{zeroWeightSpace}\left(S\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.groundSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The identity matrix in this expression acts on V(S). Intersecting its kernel with zero weight includes every vector of the minimum eigenspace and all degeneracies.

**Definition 1.3 (The singlet threshold).**

$$\forall (S: \mathbb{N}), (\operatorname{singletLowerBound}\left(S\right) = -\left(4 \cdot S^{2}\right) - \frac{8}{3} \cdot S)$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.singletLowerBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The threshold L(S)=−4S²−8S/3 is strictly negative for every S≥1.

**Definition 1.4 (All three conclusions).**

$$\operatorname{claim} \Leftrightarrow \forall (S: \mathbb{N}), ((1 \le S) \Rightarrow ((\forall (v: \operatorname{V}\left(S\right)), (((v \in \operatorname{singletSpace}\left(S\right)) \land (\operatorname{norm}\left(v\right) = 1)) \Rightarrow (\operatorname{singletLowerBound}\left(S\right) \le \operatorname{re}\left(\operatorname{inner}\left(v, \operatorname{hamiltonian}\left(S\right) \cdot v\right)\right)))) \land ((\operatorname{groundEnergy}\left(S\right) < \operatorname{singletLowerBound}\left(S\right)) \land (\operatorname{inf}\left(\operatorname{groundSpace}\left(S\right), \operatorname{singletSpace}\left(S\right)\right) = \operatorname{bottom}))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All clauses hold for every integer spin S≥1. The first clause covers every unit complex singlet; the second compares the entire zero-weight minimum with the threshold; the third excludes all nonzero singlet ground vectors.

**Theorem 1.5 (Uniform bound, strict comparison and singlet exclusion).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Dᵢⱼ = (Jᵢ⁺Jⱼ⁻+Jᵢ⁻Jⱼ⁺)/2 + ZᵢZⱼ and I = Σedges Dᵢⱼ. A strictly positive product of binomial vectors is a Dᵢⱼ eigenvector with eigenvalue S². Adding S² times the identity to Dᵢⱼ gives an entrywise nonnegative matrix. The Perron comparison bound and the Hermitian spectral theorem yield Dᵢⱼ≤S²I on the whole complex carrier. This includes every coupling sector.

For any singlet v, total-ladder commutators give the expectation identity ⟨v,Kv⟩=(4/3)⟨v,Iv⟩. This is an expectation identity, not the vector equation Kv=(4/3)Iv. The central-pair Casimir expansion gives Iv=−2S(S+1)v−D₀₁v. Applying the full-carrier pair bound proves the singlet threshold for every unit v.

For strict comparison, define an unnormalized vector t supported on Σᵢrᵢ=4S by t(r)=(-1)^p Πᵢ√C(2S,rᵢ)/C(4S,p), where p=r₀+r₁. Adjacent binomial recurrences prove that both total ladders annihilate t, including all endpoint cases. Its middle coefficient is nonzero and D₀₁t=S²t. Hence ⟨t,Kt⟩=L(S)⟨t,t⟩.

Put Tz=Σedges ZᵢZⱼ. The exact double commutator [Jtotal⁺,[Jtotal⁻,K]]=2K−8Tz forces Tz v=(e/4)v for every singlet K-eigenvector of eigenvalue e. At the middle configuration Tz has diagonal entry zero. Since t has a nonzero coefficient there and L(S)<0, t cannot be a K-eigenvector of eigenvalue L(S).

If the restricted minimum were at least L(S), the Hermitian matrix Krestricted−L(S)I would be positive semidefinite. The zero quadratic form of the restricted t would place it in that matrix's kernel, contradicting the preceding non-eigenvector result. Thus the actual minimum is strictly below L(S). Finally any nonzero ground singlet could be normalized and would contradict the unit-singlet lower bound. The full ground-singlet intersection is therefore zero.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.groundEnergy`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.groundSpace`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.result`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.singletLowerBound`
- Dependency: [D5/S3/Quantum/SpinChains/DiamondSpinBounds](DiamondSpinBounds.md)
