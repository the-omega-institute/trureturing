# Unitary and doubly extreme decomposition of a qutrit channel

## Abstract

Every equal-modulus Haagerup–Musat–Ruskai qutrit channel is a mixture of a unitary conjugation and a rank-three channel extreme in both the unital and trace-preserving completely positive maps.

**Definition 1.1 (The four HMR operators).**

$$\forall (\alpha: \mathbb{C}), (\forall (\beta: \mathbb{C}), ((\operatorname{D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition.hmrKraus}\left(\alpha, \beta\right): (\operatorname{Fin}\left(4\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))) = ![\begin{pmatrix}\alpha&(0: \mathbb{C})&(0: \mathbb{C})\\(0: \mathbb{C})&(0: \mathbb{C})&(1: \mathbb{C})\\(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})\end{pmatrix}, \begin{pmatrix}(0: \mathbb{C})&(0: \mathbb{C})&\beta\\(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})\\(0: \mathbb{C})&(1: \mathbb{C})&(0: \mathbb{C})\end{pmatrix}, \begin{pmatrix}(0: \mathbb{C})&-(1: \mathbb{C})&(0: \mathbb{C})\\(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})\\-\operatorname{star}\left(\beta\right)&(0: \mathbb{C})&(0: \mathbb{C})\end{pmatrix}, \begin{pmatrix}(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})\\(1: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})\\(0: \mathbb{C})&(0: \mathbb{C})&\operatorname{star}\left(\alpha\right)\end{pmatrix}]))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition.hmrKraus` (`✓ std3`).

*Citation.* Uffe Haagerup; Magdalena Musat; Mary Beth Ruskai (2021). *Extreme Points and Factorizability for New Classes of Unital Quantum Channels*. DOI: [10.1007/s00023-021-01071-y](https://doi.org/10.1007/s00023-021-01071-y). URL: <https://arxiv.org/abs/2006.03414v4>.

*Commentary.*

The four matrices are the operators A₁, A₂, A₃, A₄ of Theorem UCPT, HMR2021J.tex lines 280–285, in that order. The vector notation ![A₁,A₂,A₃,A₄] is a function on Fin 4, with indices zero through three. The star on a complex entry is complex conjugation. This definition allows arbitrary complex α and β; the source's channel theorem assumes |α|² + |β|² = 1.

**Definition 1.2 (The HMR matrix map).**

$$\forall (\alpha: \mathbb{C}), (\forall (\beta: \mathbb{C}), ((\operatorname{D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition.hmrChannel}\left(\alpha, \beta\right): \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)) = ((\frac{1}{2}: \mathbb{C})) \cdot (\operatorname{MatrixMap.of_{kraus}}\left(\lambda (k: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{star}\left(\operatorname{D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition.hmrKraus}\left(\alpha, \beta, k\right)\right)), \lambda (k: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{star}\left(\operatorname{D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition.hmrKraus}\left(\alpha, \beta, k\right)\right))\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition.hmrChannel` (`✓ std3`).

*Citation.* Uffe Haagerup; Magdalena Musat; Mary Beth Ruskai (2021). *Extreme Points and Factorizability for New Classes of Unital Quantum Channels*. DOI: [10.1007/s00023-021-01071-y](https://doi.org/10.1007/s00023-021-01071-y). URL: <https://arxiv.org/abs/2006.03414v4>.

*Commentary.*

This is the complex linear map Φ in HMR2021J.tex line 286. MatrixMap.of_kraus K L sends ρ to the sum of K(k)ρL(k)*. Both families here are k ↦ A(k)*, so the action is one half of the sum of A(k)*ρA(k). In particular, the adjoints occur on the left. The scalar one half is complex. The definition imposes no modulus condition.

**Definition 1.3 (Preserving the identity).**

$$\forall (\varphi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition.IsUnital}\left(\varphi\right)) \Leftrightarrow (\varphi\left((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))\right) = (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition.IsUnital` (`✓ std3`).

*Citation.* Uffe Haagerup; Magdalena Musat; Mary Beth Ruskai (2021). *Extreme Points and Factorizability for New Classes of Unital Quantum Channels*. DOI: [10.1007/s00023-021-01071-y](https://doi.org/10.1007/s00023-021-01071-y). URL: <https://arxiv.org/abs/2006.03414v4>.

*Commentary.*

A complex linear map on three-by-three matrices is unital precisely when it maps the identity matrix to the identity matrix. Together with complete positivity this is the UCP condition used in HMR2021J.tex lines 377–383.

**Theorem 1.4 (The decomposition for all equal-modulus parameters).**

$$\forall (\alpha: \mathbb{C}), (\forall (\beta: \mathbb{C}), ((\left\lVert \alpha \right\rVert = \frac{(1: \mathbb{R})}{\operatorname{Real.sqrt}\left((2: \mathbb{R})\right)}) \to ((\left\lVert \beta \right\rVert = \frac{(1: \mathbb{R})}{\operatorname{Real.sqrt}\left((2: \mathbb{R})\right)}) \to (\exists (u: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)), (\exists (lam: \mathbb{R}), (\exists (\psi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)), ((u \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(3\right), \mathbb{C}\right)) \land (((0: \mathbb{R}) \le lam) \land ((lam \le (1: \mathbb{R})) \land ((\operatorname{MatrixMap.IsCompletelyPositive}\left(\psi\right)) \land ((\operatorname{D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition.IsUnital}\left(\psi\right)) \land ((\operatorname{MatrixMap.IsTracePreserving}\left(\psi\right)) \land ((\operatorname{Matrix.rank}\left(\operatorname{MatrixMap.choi_{matrix}}\left(\psi\right)\right) = (3: \mathbb{N})) \land ((\psi \in \operatorname{Set.extremePoints}\left(\mathbb{R}, \{(\theta: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)) \mid (\operatorname{MatrixMap.IsCompletelyPositive}\left(\theta\right)) \land (\operatorname{D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition.IsUnital}\left(\theta\right))\}\right)) \land ((\psi \in \operatorname{Set.extremePoints}\left(\mathbb{R}, \{(\theta: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)) \mid (\operatorname{MatrixMap.IsCompletelyPositive}\left(\theta\right)) \land (\operatorname{MatrixMap.IsTracePreserving}\left(\theta\right))\}\right)) \land (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition.hmrChannel}\left(\alpha, \beta, \rho\right) = (\operatorname{Complex.ofReal}\left(lam\right)) \cdot (((\operatorname{star}\left(u\right)) \cdot (\rho)) \cdot (u)) + (\operatorname{Complex.ofReal}\left((1: \mathbb{R}) - lam\right)) \cdot (\psi\left(\rho\right)))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition.result` (`✓ std3`). ∎

*Resolves.* `Problems/haagerup-musat-ruskai-2021-qutrit-channel-unitary-extreme-decomposition` (proved) by `D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"haagerup-musat-ruskai-2021-qutrit-channel-unitary-extreme-decomposition","declaration_gid":"D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Uffe Haagerup; Magdalena Musat; Mary Beth Ruskai (2021). *Extreme Points and Factorizability for New Classes of Unital Quantum Channels*. DOI: [10.1007/s00023-021-01071-y](https://doi.org/10.1007/s00023-021-01071-y). URL: <https://arxiv.org/abs/2006.03414v4>.

*Commentary.*

For every pair of complex parameters of norm 1/√2, the channel is a convex combination of a unitary conjugation and a completely positive, unital, trace-preserving map ψ. Its Choi matrix has natural-valued rank three, and ψ is separately extreme in the UCP maps and in the CPT maps, where convexity is over the real scalars. The equality holds for every complex matrix ρ. MatrixMap.choi_matrix is the Choi matrix operation; MatrixMap.IsCompletelyPositive quantifies over every finite amplification, and MatrixMap.IsTracePreserving requires preservation of the trace of every matrix. Complex.ofReal displays both real-to-complex coefficient casts. The source's question is HMR2021J.tex lines 387–390; its positive real parameter example is at lines 366–383. The construction below always takes lam = 1/4.

First consider any three matrices y(i) and their map Ψ(ρ) = Σᵢ y(i)*ρy(i). If Ψ = tθ + sη with t > 0, s ≥ 0 and θ, η completely positive, then C(Ψ) − tC(θ) = sC(η) is positive semidefinite. Positivity implies ker C(Ψ) ⊆ ker C(θ). Let V have columns given by the entries of y(i)*, so C(Ψ) = VV*. Factor C(θ) = BB*. The kernel inclusion gives B* = QC(Ψ) for a matrix Q, hence C(θ) = VHV* with H = V*Q*QV. Inverting the Choi correspondence gives θ(ρ) = Σᵢⱼ Hᵢⱼ y(i)*ρy(j).

Suppose Σᵢ y(i)*y(i) = I and the nine products y(i)*y(j) are complex linearly independent. Unitality of θ then makes H equal to I by uniqueness of coefficients, so θ = Ψ. This proves extremality among UCP maps. For CPT maps, assume Σᵢ y(i)y(i)* = I and independence of the nine products y(i)y(j)*. Trace preservation, cyclicity of trace and the nondegenerate trace pairing give Σᵢⱼ Hᵢⱼ y(j)y(i)* = I. Coefficient uniqueness applied to the transpose of H again gives H = I. Independence of y(i)*y(j) also implies independence of the three y(i), then of their adjoints and of the columns of V. Thus rank C(Ψ) = rank(VV*) = rank V = 3.

Put q = √2, viewing the real entries below as complex numbers. Choose the three y(i), in order, to be 1/(2√3) times the matrices [[−1,−q,1],[q,0,−q],[−1,q,1]], [[1,q,1],[q,0,q],[1,q,1]], and [[1,−q,1],[−q,0,q],[−1,q,−1]]. Entrywise multiplication verifies both sums of products equal I. For each of the two nine-product families, explicit dual coordinate matrices recover each coefficient from any linear combination of the products: the sum of the entrywise products with the chosen dual matrix is that coefficient. Applying these identities to a zero linear combination proves both independence assertions. These calculations use (√2)² = 2, (√3)² = 3 and √3 ≠ 0. Consequently the map Ψ₀ associated with these three matrices has both extremality properties and Choi rank three.

Write Φ₀ for the channel at α = β = 1/√2, and set U₀ = 1/2 [[1,−q,−1],[q,0,q],[−1,−q,1]]. Direct calculation of its nine entries proves U₀*U₀ = I. Expanding the two Kraus sums entry by entry proves, for every ρ, Φ₀(ρ) = (1/4)U₀*ρU₀ + (3/4)Ψ₀(ρ). These matrices are the source's operators 2X₂ and (2/√3)(X₁,X₃,X₄), respectively, from HMR2021J.tex lines 370–381.

For general α and β of the required norms, set u = √2 α and v = √2 β. Both have norm one. Choose a fifth root r with r⁵ = uv² and set s = r²/v. Norm multiplicativity gives |r| = |s| = 1, and algebra gives rs² = u and r²/s = v. The diagonal matrices D = diag(r,1,r⁻¹) and E = diag(s,1,s⁻¹) are unitary. Substituting these identities in the nine entries of the Kraus sums gives Φα,β(ρ) = E*Φ₀(D*ρD)E.

The transformation T(φ)(ρ) = E*φ(D*ρD)E preserves complete positivity by composition of Kraus maps. Unitarity gives unitality, and cyclicity of trace gives trace preservation. Its inverse uses D* and E*. Together these transformations form a real linear equivalence mapping each of the UCP and CPT sets onto itself; the image theorem for extreme points therefore preserves each extremality property. In Choi coordinates C(T(φ)) = QC(φ)Q*, where Q has entries Q((a,i),(b,j)) = conjugate(E(b,a)) conjugate(D(i,j)). The rank of a product cannot exceed that of its middle factor. Applying this inequality to T and its inverse proves equality of Choi ranks.

Transport the positive real parameter decomposition by T. The unitary term becomes conjugation by U = DU₀E, and the other term becomes ψ = T(Ψ₀), which retains complete positivity, unitality, trace preservation, rank three and both extremality properties. With lam = 1/4 the two nonnegative weights are 1/4 and 3/4, and their sum is one. The phase identity identifies the transported channel with Φα,β, giving the stated equality on every ρ.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition.IsUnital`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition.hmrChannel`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition.hmrKraus`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition.result`
- Dependency: [D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility](ElementaryChannelDivisibility.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence](IptPptSquaredEquivalence.md)
