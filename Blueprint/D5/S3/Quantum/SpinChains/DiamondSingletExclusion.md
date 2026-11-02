# Singlet exclusion for the equal-spin diamond

## Abstract

For every positive integer spin, the coefficient-one diamond has no singlet ground vector in its entire zero-weight sector.

Let S be a natural number. Each of the four factors is the complete complex spin-S space with orthonormal basis indexed by W(S) = Fin(2S+1). Index r has weight S−r; the native normalized raising matrix Jplus(2S) has coefficient √((r+1)(2S−r)) from r+1 to r, with zero endpoint, and lowering is its adjoint. Put C(S) = Fin(4) → W(S), V(S) = C(S) → ℂ and O(S) = Matrix(C(S),C(S),ℂ). Norms are the Euclidean norms and inner products conjugate the first argument. Matrices act on every complex superposition in V(S). Sites 0,1,2,3 correspond to vertices 1,2,3,4. A submodule infimum denotes intersection; bottom is the zero submodule.

**Definition 1.1 (An operator at one site).**

$$\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (A: \operatorname{Matrix}\left(\operatorname{W}\left(S\right), \operatorname{W}\left(S\right), \mathbb{C}\right)), (\forall (x: \operatorname{C}\left(S\right)), (\forall (y: \operatorname{C}\left(S\right)), (\operatorname{site}\left(S, i, A, x, y\right) = \operatorname{A}\left(x\left(i\right), y\left(i\right)\right) \cdot \operatorname{prodExcept}\left(i, x, y\right))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.site` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

prodExcept(i,x,y) is the product of Kronecker deltas δ(xⱼ,yⱼ) over the three sites j≠i. Thus site is exactly the tensor placement of A with identities on all other factors.

**Definition 1.2 (The raising operator at a site).**

$$\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\operatorname{raising}\left(S, i\right) = \operatorname{site}\left(S, i, \operatorname{Jplus}\left(2 \cdot S\right)\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.raising` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the normalized native raising matrix on the full factor.

**Definition 1.3 (The lowering operator at a site).**

$$\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\operatorname{lowering}\left(S, i\right) = \operatorname{site}\left(S, i, (\operatorname{Jplus}\left(2 \cdot S\right))^{*}\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.lowering` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The adjoint convention includes both ladder endpoints.

**Definition 1.4 (The five edges).**

$$\operatorname{edges} = \operatorname{finset}\left((0,1), (0,2), (0,3), (1,2), (1,3)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.edges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each listed unordered edge is included once. The absent edge is (2,3); there are no loops or additional coefficients.

**Definition 1.5 (The diamond Hamiltonian).**

$$\forall (S: \mathbb{N}), (\operatorname{hamiltonian}\left(S\right) = \sum_{(i,j)\in\operatorname{edges}} 2 \cdot (\operatorname{X}\left(i\right) \cdot \operatorname{X}\left(j\right) + \operatorname{Y}\left(i\right) \cdot \operatorname{Y}\left(j\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.hamiltonian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Writing Xᵢ=site(S,i,Jx(2S)) and Yᵢ=site(S,i,Jy(2S)), this is 2Σedges(XᵢXⱼ+YᵢYⱼ). The native Cartesian identity proves it equals Σedges(Jᵢ⁺Jⱼ⁻+Jᵢ⁻Jⱼ⁺), with coefficient +1 on each of the five edges. Operators at distinct sites commute, so the Hamiltonian is Hermitian.

**Definition 1.6 (Total raising).**

$$\forall (S: \mathbb{N}), (\operatorname{totalRaising}\left(S\right) = \sum_{i\in\operatorname{Fin}\left(4\right)} \operatorname{raising}\left(S, i\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.totalRaising` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum runs over all four sites.

**Definition 1.7 (Total lowering).**

$$\forall (S: \mathbb{N}), (\operatorname{totalLowering}\left(S\right) = \sum_{i\in\operatorname{Fin}\left(4\right)} \operatorname{lowering}\left(S, i\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.totalLowering` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the adjoint of total raising.

**Definition 1.8 (Total weight).**

$$\forall (S: \mathbb{N}), (\operatorname{totalWeight}\left(S\right) = \sum_{i\in\operatorname{Fin}\left(4\right)} \operatorname{site}\left(S, i, \operatorname{Jz}\left(2 \cdot S\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.totalWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At configuration x its diagonal entry is 4S−Σᵢxᵢ. The Hamiltonian commutes with total weight.

**Definition 1.9 (The entire singlet space).**

$$\forall (S: \mathbb{N}), (\operatorname{singletSpace}\left(S\right) = \operatorname{inf}\left(\operatorname{ker}\left(\operatorname{totalRaising}\left(S\right)\right), \operatorname{ker}\left(\operatorname{totalLowering}\left(S\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.singletSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both kernels are taken on V(S). No pair-coupling sector or multiplicity is selected. The total ladder commutator implies that every vector here has total weight zero.

**Definition 1.10 (The entire zero-weight space).**

$$\forall (S: \mathbb{N}), (\operatorname{zeroWeightSpace}\left(S\right) = \operatorname{ker}\left(\operatorname{totalWeight}\left(S\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.zeroWeightSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

It consists exactly of vectors supported on configurations Z(S) with Σᵢxᵢ=4S. These coordinate vectors form an orthonormal basis of the entire kernel. The middle configuration xᵢ=S belongs to Z(S), including at S=0.

**Definition 1.11 (The actual Hermitian restriction).**

$$\forall (S: \mathbb{N}), (\forall (x: \operatorname{Z}\left(S\right)), (\forall (y: \operatorname{Z}\left(S\right)), (\operatorname{restrictedHamiltonian}\left(S, x, y\right) = \operatorname{hamiltonian}\left(S, \operatorname{val}\left(x\right), \operatorname{val}\left(y\right)\right))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.restrictedHamiltonian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Z(S) is the subtype of C(S) just described. Invariance of zero weight identifies this submatrix with the genuine restricted operator, including its action, inner product and eigenvectors.

**Definition 1.12 (The ground energy).**

$$\forall (S: \mathbb{N}), (\operatorname{groundEnergy}\left(S\right) = \operatorname{sInf}\left(\operatorname{spectrumReal}\left(\operatorname{restrictedHamiltonian}\left(S\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.groundEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The restricted Hermitian matrix has finite nonempty real spectrum. Its infimum belongs to that spectrum and is its least element, so groundEnergy is the actual attained minimum.

**Definition 1.13 (The entire zero-weight ground eigenspace).**

$$\forall (S: \mathbb{N}), (\operatorname{groundSpace}\left(S\right) = \operatorname{inf}\left(\operatorname{ker}\left(\operatorname{hamiltonian}\left(S\right) - \operatorname{ofReal}\left(\operatorname{groundEnergy}\left(S\right)\right) \cdot 1\right), \operatorname{zeroWeightSpace}\left(S\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.groundSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The identity matrix in this expression acts on V(S). Intersecting its kernel with zero weight includes every vector of the minimum eigenspace and all degeneracies.

**Definition 1.14 (The singlet threshold).**

$$\forall (S: \mathbb{N}), (\operatorname{singletLowerBound}\left(S\right) = -\left(4 \cdot S^{2}\right) - \frac{8}{3} \cdot S)$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.singletLowerBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The threshold L(S)=−4S²−8S/3 is strictly negative for every S≥1.

**Definition 1.15 (All three conclusions).**

$$\operatorname{claim} \Leftrightarrow \forall (S: \mathbb{N}), ((1 \le S) \Rightarrow ((\forall (v: \operatorname{V}\left(S\right)), (((v \in \operatorname{singletSpace}\left(S\right)) \land (\operatorname{norm}\left(v\right) = 1)) \Rightarrow (\operatorname{singletLowerBound}\left(S\right) \le \operatorname{re}\left(\operatorname{inner}\left(v, \operatorname{hamiltonian}\left(S\right) \cdot v\right)\right)))) \land ((\operatorname{groundEnergy}\left(S\right) < \operatorname{singletLowerBound}\left(S\right)) \land (\operatorname{inf}\left(\operatorname{groundSpace}\left(S\right), \operatorname{singletSpace}\left(S\right)\right) = \operatorname{bottom}))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All clauses hold for every integer spin S≥1. The first clause covers every unit complex singlet; the second compares the entire zero-weight minimum with the threshold; the third excludes all nonzero singlet ground vectors.

**Theorem 1.16 (Uniform bound, strict comparison and singlet exclusion).**

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
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.edges`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.groundEnergy`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.groundSpace`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.hamiltonian`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.lowering`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.raising`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.restrictedHamiltonian`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.result`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.singletLowerBound`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.singletSpace`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.site`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.totalLowering`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.totalRaising`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.totalWeight`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSingletExclusion.zeroWeightSpace`
- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Dominance](../../Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Dominance.md)
- Dependency: [D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment](../Contextuality/TemporalHardySpinAttainment.md)
- Dependency: [D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation](../Entanglement/PrecessionUniversalThresholdRefutation.md)
