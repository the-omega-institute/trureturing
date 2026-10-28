# Mixed-unitary channels and marginal pinching

## Abstract

Every non-isotropic mixed-unitary qubit channel fails to commute with marginal pinching on a two-qubit density matrix with nondegenerate input and output marginals.

QubitMatrix is the algebra of complex matrices with both indices in Fin 2. A starred matrix denotes its conjugate transpose, and I denotes the identity of the indicated size.

**Definition 1.1 (Finite mixtures of unitary conjugations).**

$$\forall (\varphi: (\operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix}) \to (\operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix})), (\operatorname{D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation.IsMixedUnitary}\left(\varphi\right) = (\exists (k: \mathbb{N}), (\exists (p: (\operatorname{Fin}\left(k\right)) \to (\mathbb{R})), (\exists (u: (\operatorname{Fin}\left(k\right)) \to (\operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix})), ((\forall (j: \operatorname{Fin}\left(k\right)), ((0: \mathbb{R}) \le p\left(j\right))) \land ((\sum_{j: \operatorname{Fin}\left(k\right)} (p\left(j\right)) = (1: \mathbb{R})) \land ((\forall (j: \operatorname{Fin}\left(k\right)), (u\left(j\right) \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))) \land (\forall (a: \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix}), (\varphi\left(a\right) = \sum_{j: \operatorname{Fin}\left(k\right)} (((\operatorname{Complex.ofReal}\left(p\left(j\right)\right): \mathbb{C})) \cdot (((u\left(j\right)) \cdot (a)) \cdot (\operatorname{star}\left(u\left(j\right)\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.IsMixedUnitary` (`✓ std3`).

*Citation.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

A mixed-unitary map is a finite convex combination of unitary conjugations. The real weights are nonnegative and sum to one; their inclusions into the complex numbers act by scalar multiplication. The equality holds for every complex qubit matrix, rather than only for density matrices. This is the linear extension of the mixed-unitary class in Section 3.2, revised_jphysa_clean.tex, line 325.

**Definition 1.2 (Unitary and antiunitary isotropic forms).**

$$\forall (\varphi: (\operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix}) \to (\operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix})), (\operatorname{D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation.IsIsotropic}\left(\varphi\right) = (\exists (\gamma: \mathbb{R}), ((\gamma \in \operatorname{Set.Icc}\left((0: \mathbb{R}), (1: \mathbb{R})\right)) \land (\exists (u: \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix}), ((u \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)) \land ((\forall (a: \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix}), (\varphi\left(a\right) = (((\operatorname{Complex.ofReal}\left(((1: \mathbb{R})) - (\gamma)\right): \mathbb{C})) \cdot (((u) \cdot (a)) \cdot (\operatorname{star}\left(u\right)))) + (((\operatorname{Complex.ofReal}\left(\gamma\right): \mathbb{C})) \cdot ((\frac{\operatorname{Matrix.trace}\left(a\right)}{(2: \mathbb{C})}) \cdot ((1: \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix})))))) \lor (\forall (a: \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix}), (\varphi\left(a\right) = (((\operatorname{Complex.ofReal}\left(((1: \mathbb{R})) - (\gamma)\right): \mathbb{C})) \cdot (((u) \cdot (\operatorname{Matrix.transpose}\left(a\right))) \cdot (\operatorname{star}\left(u\right)))) + (((\operatorname{Complex.ofReal}\left(\gamma\right): \mathbb{C})) \cdot ((\frac{\operatorname{Matrix.trace}\left(a\right)}{(2: \mathbb{C})}) \cdot ((1: \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix}))))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.IsIsotropic` (`✓ std3`).

*Citation.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

An isotropic map combines a unitary or antiunitary action with complete depolarization, using one real parameter between zero and one and one unitary matrix. On arbitrary complex matrices the depolarizing term is trace(a) times I/2. The antiunitary action on states extends complex linearly as u a-transpose u-star. These are the two alternatives in Section 3.2, revised_jphysa_clean.tex, lines 326-327; no positivity condition is imposed on the matrix argument a.

**Definition 1.3 (Extension to the first qubit).**

$$\forall (\varphi: (\operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix}) \to (\operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix})), (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation.localMap}\left(\varphi, \rho\right): \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)) = \lambda (a: \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \mapsto (\lambda (c: \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \mapsto (\varphi\left(\lambda (i: \operatorname{Fin}\left(2\right)) \mapsto (\lambda (j: \operatorname{Fin}\left(2\right)) \mapsto (\rho\left((i, (a).2), (j, (c).2)\right))), (a).1, (c).1\right)))))$$

*Formalization.* `D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.localMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

The two matrix indices are pairs, with the first coordinate belonging to A. Fixing the second coordinates selects a qubit block, to which the map is applied. For a linear map this is its tensor product with the identity on the second qubit. The block formula also defines a function for arbitrary maps, without requiring linearity.

**Definition 1.4 (A Hermitian qubit matrix with simple spectrum).**

$$\forall (a: \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix}), (\operatorname{D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation.IsNondegenerate}\left(a\right) = (\exists (h: \operatorname{Matrix.IsHermitian}\left(a\right)), (\operatorname{Function.Injective}\left(\operatorname{Matrix.IsHermitian.eigenvalues}\left(h\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.IsNondegenerate` (`✓ std3`).

*Citation.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

The matrix must be Hermitian and its two real eigenvalues must be distinct. Injectivity of the eigenvalue function on Fin 2 expresses this distinction. This is the nondegeneracy assumption on the marginal in revised_jphysa_clean.tex, line 339.

**Definition 1.5 (Pinching in the first marginal's spectral basis).**

$$\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation.pinchA}\left(\rho\right): \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)) = \operatorname{dite}\left(\operatorname{Matrix.IsHermitian}\left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\rho\right)\right), \lambda (h: \operatorname{Matrix.IsHermitian}\left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\rho\right)\right)) \mapsto (\operatorname{D5.S3.Observer.Conditioning.unreadState}\left(\lambda (i: \operatorname{Fin}\left(2\right)) \mapsto (\operatorname{let} (p: \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix}) = \lambda (a: \operatorname{Fin}\left(2\right)) \mapsto (\lambda (c: \operatorname{Fin}\left(2\right)) \mapsto ((\operatorname{WithLp.ofLp}\left(\operatorname{Matrix.IsHermitian.eigenvectorBasis}\left(h\right)\left(i\right)\right)\left(a\right)) \cdot (\operatorname{star}\left(\operatorname{WithLp.ofLp}\left(\operatorname{Matrix.IsHermitian.eigenvectorBasis}\left(h\right)\left(i\right)\right)\left(c\right)\right)))); \operatorname{Matrix.kroneckerMap}\left(\lambda (x1: \mathbb{C}) \mapsto (\lambda (x2: \mathbb{C}) \mapsto ((x1) \cdot (x2))), p, (1: \operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix})\right)), \rho\right)), \operatorname{Function.const}\left(\neg (\operatorname{Matrix.IsHermitian}\left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\rho\right)\right)), \rho\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.pinchA` (`✓ std3`).

*Citation.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

For a Hermitian first marginal, choose its orthonormal eigenvector basis. Each outer product p projects onto one eigenvector; tensoring with the second identity and summing the corresponding unread measurements gives marginal pinching. This is the map defined in revised_jphysa_clean.tex, line 261. The choice is unambiguous on a nondegenerate marginal. The formula extends to degenerate Hermitian marginals using the chosen basis, and returns the original matrix when the marginal is not Hermitian.

**Theorem 1.6 (Non-isotropic mixed-unitary channels do not commute with pinching).**

$$\forall (\varphi: (\operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix}) \to (\operatorname{D5.S3.Quantum.FiniteDimensional.QubitMatrix})), ((\operatorname{D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation.IsMixedUnitary}\left(\varphi\right)) \Rightarrow ((\neg (\operatorname{D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation.IsIsotropic}\left(\varphi\right))) \Rightarrow (\exists (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{Matrix.PosSemidef}\left(\rho\right)) \land ((\operatorname{Matrix.trace}\left(\rho\right) = (1: \mathbb{C})) \land ((\operatorname{D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation.IsNondegenerate}\left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\rho\right)\right)) \land ((\operatorname{D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation.IsNondegenerate}\left(\varphi\left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\rho\right)\right)\right)) \land (\operatorname{D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation.pinchA}\left(\operatorname{D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation.localMap}\left(\varphi, \rho\right)\right) \ne \operatorname{D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation.localMap}\left(\varphi, \operatorname{D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation.pinchA}\left(\rho\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/liu-takagi-lloyd-2019-mixed-unitary-pinching-commutation` (proved) by `D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"liu-takagi-lloyd-2019-mixed-unitary-pinching-commutation","declaration_gid":"D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

The conclusion concerns the second sentence of the conjecture in revised_jphysa_clean.tex, line 463. For each non-isotropic mixed-unitary qubit map, it supplies a positive semidefinite two-qubit matrix of trace one, with both the input marginal and its image nondegenerate, on which the two orders of pinching and local evolution differ. It asserts neither the converse nor a classification of maps outside the mixed-unitary class.

First, the convex combination gives a complex linear map preserving the identity, trace and Hermiticity. Write S(v) for the real Pauli combination v-dot-sigma. Define the real matrix T by T(i,j) = Re tr(sigma(i+1) phi(sigma(j+1)))/2. The Hermitian traceless Pauli expansion gives phi(S(v)) = S(Tv). The trace of S(v) is zero, S(v) squared is (v-dot-v)I, and the anticommutator of S(v) and S(w) is 2(v-dot-w)I. These identities also give S(v)S(w)S(v) = 2(v-dot-w)S(v) - (v-dot-v)S(w). Agreement on I and every S(v) determines a complex linear map on all qubit matrices.

The convex combination also preserves positivity. Suppose T-transpose T = cI. The squared length of each column gives c at least zero. Apply positivity to the rank-one diagonal matrix with entries 1 and 0: its image has trace one and Bloch-vector length squared c, hence c is at most one. To lift an orthogonal transformation of real three-space, begin with a hyperplane reflection. For a nonzero normal v, the Hermitian unitary S(v)/length(v), together with the second Pauli matrix and matrix transpose, implements the reflection on Pauli combinations by the triple-product identity. A zero normal gives the identity. The Cartan-Dieudonne decomposition expresses every orthogonal transformation as a product of such reflections; composing their actions yields either unitary conjugation or unitary conjugation after transpose. When c = 0, T = 0 and agreement on the Pauli expansion identifies phi with complete depolarization. When c is positive, put s = sqrt(c) and O = T/s. Then O-transpose O = I and 0 < s <= 1. The lift and agreement on I and S(v) identify phi with the isotropic form of parameter gamma = 1 - s. Thus non-isotropy forces Q = T-transpose T to be nonscalar.

A nonscalar Q supplies orthogonal real vectors whose images under T have nonzero inner product. If Q has a nonzero off-diagonal entry Q(i,j), use the coordinate vectors e_i and e_j. Otherwise some diagonal entry Q(i,i) differs from Q(0,0); use e_0 + e_i and e_0 - e_i. Their image inner product is Q(0,0) - Q(i,i). Normalize both vectors to obtain n and x with n-dot-n = x-dot-x = 1, n-dot-x = 0 and (Tn)-dot-(Tx) nonzero. In particular both n and Tn are nonzero.

Next derive a pinching formula for any two-qubit matrix tau with marginal (I + S(v))/2 and v nonzero. Let p_0 and p_1 be the marginal's spectral projectors and lambda_0, lambda_1 its eigenvalues. The spectral expansion gives p_0 + p_1 = I. The trace and determinant give lambda_0 + lambda_1 = 1 and lambda_0 lambda_1 = (1 - v-dot-v)/4, so (lambda_0 - lambda_1) squared is v-dot-v. Consequently S(v) = (lambda_0 - lambda_1)(p_0 - p_1). Expanding the two lifted projectors in the unread measurement yields pinchA(tau) = [tau + (S(v) tensor I) tau (S(v) tensor I)/(v-dot-v)]/2.

Now take rho = [I tensor I + (S(n) tensor I)/2 + (S(x) tensor Z)/4]/4. Here Z is the diagonal Pauli matrix with entries 1 and -1. Its first marginal is (I + S(n)/2)/2. To prove positivity directly, put K = S(n) tensor I, L = S(x) tensor Z and H = K/2 + L/4. The Pauli identities give K squared = L squared = I and KL = -LK. Thus H is Hermitian and H squared = 5I/16. The identity rho = (I + H)(I + H)-dagger/8 + 11I/128 expresses rho as a sum of positive semidefinite matrices. The Pauli traces give trace(rho) = 1.

For arbitrary real a and b, let R(a,b) be the same displayed state expression with n and x replaced by a and b. Linearity and the Pauli representation show that local evolution takes R(a,b) to R(Ta,Tb). For a nonzero, the pinching formula takes R(a,b) to R(a,[(a-dot-b)/(a-dot-a)]a). Taking the partial trace commutes with local evolution, and the output marginal is (I + S(Tn)/2)/2. A qubit matrix (I + S(v))/2 with v nonzero has distinct eigenvalues: equal eigenvalues would make its spectral expansion scalar, whose Bloch vector vanishes, contradicting v nonzero. Apply this to v = n/2 and v = Tn/2 to obtain both required nondegeneracy conclusions.

Finally substitute these state and pinching identities in the difference of the two orders. Since n-dot-x = 0, the difference is [(Tn)-dot-(Tx)]/[16((Tn)-dot-(Tn))] times S(Tn) tensor Z. The real quotient is included into the complex scalars. Its numerator is nonzero and its denominator is positive. The tensor factor is also nonzero: its second-qubit (0,0) block is S(Tn), and a vanishing S(Tn) would contradict S(Tn) squared = ((Tn)-dot-(Tn))I. Thus the difference cannot vanish, proving the inequality.

## References

- Truth anchor: `D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.IsIsotropic`
- Truth anchor: `D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.IsMixedUnitary`
- Truth anchor: `D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.IsNondegenerate`
- Truth anchor: `D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.localMap`
- Truth anchor: `D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.pinchA`
- Truth anchor: `D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.result`
- Dependency: [D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound](TraceNormDiscordMutualCorrelationBound.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction](../QuantumChannels/HiaiRuskaiRiemannianContraction.md)
- Dependency: [D5/S3/QuantumChannels/ChannelTimeReversalNoGo](../../QuantumChannels/ChannelTimeReversalNoGo.md)
