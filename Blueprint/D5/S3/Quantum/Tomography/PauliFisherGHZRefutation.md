# Pauli Fisher information along a GHZ phase family

## Abstract

GHZ phase tangents refute a uniform lower bound for mean Pauli Fisher information.

**Definition 1.1 (Single-qubit Pauli eigenvectors).**

$$\forall (s: \operatorname{Fin}\left(3\right)), (\forall (o: \operatorname{Fin}\left(2\right)), (\forall (b: \operatorname{Fin}\left(2\right)), ((\operatorname{D5.S3.Quantum.Tomography.PauliFisherGHZRefutation.pauliEigen}\left(s, o, b\right): \mathbb{C}) = \operatorname{D5.S3.Quantum.Magic.WignerDistanceMinimum.eigenVector}\left(\operatorname{ite}\left(s = (2: \operatorname{Fin}\left(3\right)), \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{ite}\left(s = (0: \operatorname{Fin}\left(3\right)), \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.X}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Y}\right)\right), o, b\right))))$$

*Formalization.* `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.pauliEigen` (`✓ std3`).

*Citation.* Anirudh Acharya, Theodore Kypraios and Mădălin Guţă (2016). *Statistically efficient tomography of low rank states with incomplete measurements*. DOI: [10.1088/1367-2630/18/4/043018](https://doi.org/10.1088/1367-2630/18/4/043018). URL: <https://arxiv.org/abs/1510.03229v2>.

*Commentary.*

A setting s in Fin 3 encodes X, Y, Z by 0, 1, 2, respectively. The outcome o in Fin 2 encodes the eigenvalue (−1)^o, and b is a computational-basis coordinate. The chosen eigenvectors fix the phases of the Pauli eigenvectors used in Efficient-Ion-Tomography.tex, lines 114–121.

**Definition 1.2 (Product measurement vectors).**

$$\forall (n: \mathbb{N}), (\forall (s: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(3\right))), (\forall (o: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), (\forall (b: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), ((\operatorname{D5.S3.Quantum.Tomography.PauliFisherGHZRefutation.productVector}\left(s, o, b\right): \mathbb{C}) = \operatorname{D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(2\right)\right), (\lambda (j: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Function.const}\left(\operatorname{Unit}, \operatorname{D5.S3.Quantum.Tomography.PauliFisherGHZRefutation.pauliEigen}\left(s\left(j\right), o\left(j\right)\right)\right))), \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Unit.unit}\right), b\right)))))$$

*Formalization.* `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.productVector` (`✓ std3`).

*Citation.* Anirudh Acharya, Theodore Kypraios and Mădălin Guţă (2016). *Statistically efficient tomography of low rank states with incomplete measurements*. DOI: [10.1088/1367-2630/18/4/043018](https://doi.org/10.1088/1367-2630/18/4/043018). URL: <https://arxiv.org/abs/1510.03229v2>.

*Commentary.*

For n qubits, s chooses one Pauli basis at each site and o chooses one eigenvector in each basis. The value at the bit string b is the product of the corresponding single-qubit coordinates. The product map takes a constant family of two-element coordinate types and a unit input at each site. This is the tensor-product measurement vector of Efficient-Ion-Tomography.tex, lines 118–121.

**Definition 1.3 (Outcome probabilities).**

$$\forall (n: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\forall (s: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(3\right))), (\forall (o: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), ((\operatorname{D5.S3.Quantum.Tomography.PauliFisherGHZRefutation.outcomeProb}\left(\rho, s, o\right): \mathbb{R}) = \operatorname{D5.S3.Quantum.Recovery.ProductPrefixRigidity.readout}\left(\rho, \operatorname{D5.S3.Quantum.Tomography.PauliFisherGHZRefutation.productVector}\left(s, o\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.outcomeProb` (`✓ std3`).

*Citation.* Anirudh Acharya, Theodore Kypraios and Mădălin Guţă (2016). *Statistically efficient tomography of low rank states with incomplete measurements*. DOI: [10.1088/1367-2630/18/4/043018](https://doi.org/10.1088/1367-2630/18/4/043018). URL: <https://arxiv.org/abs/1510.03229v2>.

*Commentary.*

The real readout of ρ in the product measurement vector is the Born probability when ρ is a density matrix. The readout is the real part of the conjugate-vector quadratic form. The definition is also meaningful for arbitrary complex matrices. It expresses equation (1) of Efficient-Ion-Tomography.tex, lines 114–121.

**Definition 1.4 (Fisher information of a setting).**

$$\forall (n: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\forall (v: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\forall (s: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(3\right))), ((\operatorname{D5.S3.Quantum.Tomography.PauliFisherGHZRefutation.settingFisher}\left(\rho, v, s\right): \mathbb{R}) = \sum_{o: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))} (\frac{\operatorname{D5.S3.Quantum.Recovery.ProductPrefixRigidity.readout}\left(v, \operatorname{D5.S3.Quantum.Tomography.PauliFisherGHZRefutation.productVector}\left(s, o\right)\right)^{(2: \mathbb{N})}}{\operatorname{D5.S3.Quantum.Tomography.PauliFisherGHZRefutation.outcomeProb}\left(\rho, s, o\right)})))))$$

*Formalization.* `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.settingFisher` (`✓ std3`).

*Citation.* Anirudh Acharya, Theodore Kypraios and Mădălin Guţă (2016). *Statistically efficient tomography of low rank states with incomplete measurements*. DOI: [10.1088/1367-2630/18/4/043018](https://doi.org/10.1088/1367-2630/18/4/043018). URL: <https://arxiv.org/abs/1510.03229v2>.

*Commentary.*

For a state ρ and a matrix direction v, sum the squared real directional readouts divided by the outcome probabilities over all bit-string outcomes. This is the directional quadratic form of the Fisher matrix in Efficient-Ion-Tomography.tex, lines 173–176. Real division assigns zero to a term whose denominator is zero; the definition itself does not require density or tangency assumptions.

**Definition 1.5 (Mean Fisher information over Pauli settings).**

$$\forall (n: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\forall (v: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Tomography.PauliFisherGHZRefutation.averageFisher}\left(\rho, v\right): \mathbb{R}) = \operatorname{Finset.expect}\left((\operatorname{Finset.univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(3\right))\right)), \operatorname{D5.S3.Quantum.Tomography.PauliFisherGHZRefutation.settingFisher}\left(\rho, v\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.averageFisher` (`✓ std3`).

*Citation.* Anirudh Acharya, Theodore Kypraios and Mădălin Guţă (2016). *Statistically efficient tomography of low rank states with incomplete measurements*. DOI: [10.1088/1367-2630/18/4/043018](https://doi.org/10.1088/1367-2630/18/4/043018). URL: <https://arxiv.org/abs/1510.03229v2>.

*Commentary.*

Take the uniform finite average over every setting s : Fin n → Fin 3. There are 3^n settings, including one empty setting when n is zero. Finite expectation divides the sum by the real cast of the cardinality of the setting set. The average over all Pauli settings is given in Efficient-Ion-Tomography.tex, line 335.

**Definition 1.6 (Tangents represented by curves of fixed rank).**

$$\forall (n: \mathbb{N}), (\forall (r: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\forall (v: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Tomography.PauliFisherGHZRefutation.IsRankTangent}\left(r, \rho, v\right)) \Leftrightarrow (\exists (\gamma: (\mathbb{R}) \to (\operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right))), ((\gamma\left((0: \mathbb{R})\right) = \rho) \land ((\operatorname{HasDerivAt}\left(\gamma, v, (0: \mathbb{R})\right)) \land (\forall (t: \mathbb{R}), ((\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\gamma\left(t\right)\right)) \land (\operatorname{Matrix.rank}\left(\gamma\left(t\right)\right) = r))))))))))$$

*Formalization.* `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.IsRankTangent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anirudh Acharya, Theodore Kypraios and Mădălin Guţă (2016). *Statistically efficient tomography of low rank states with incomplete measurements*. DOI: [10.1088/1367-2630/18/4/043018](https://doi.org/10.1088/1367-2630/18/4/043018). URL: <https://arxiv.org/abs/1510.03229v2>.

*Commentary.*

A matrix v is a rank-r tangent at ρ if a curve γ of complex matrices passes through ρ at zero, has real derivative v there, and is a density matrix of rank r at every real parameter t. Only differentiability at zero is required. This curve formulation expresses the directions used with the local Frobenius metric of Efficient-Ion-Tomography.tex, lines 157–173.

**Definition 1.7 (A uniform lower bound at each positive rank).**

$$(\operatorname{D5.S3.Quantum.Tomography.PauliFisherGHZRefutation.claim}) \Leftrightarrow (\forall (r: \mathbb{N}), (((1: \mathbb{N}) \le r) \to (\exists (c: \mathbb{R}), (((0: \mathbb{R}) < c) \land (\forall (n: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\forall (v: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)) \to ((\operatorname{Matrix.rank}\left(\rho\right) = r) \to ((\operatorname{D5.S3.Quantum.Tomography.PauliFisherGHZRefutation.IsRankTangent}\left(r, \rho, v\right)) \to ((c) \cdot (\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((v) \cdot (v)\right)\right)) \le \operatorname{D5.S3.Quantum.Tomography.PauliFisherGHZRefutation.averageFisher}\left(\rho, v\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anirudh Acharya, Theodore Kypraios and Mădălin Guţă (2016). *Statistically efficient tomography of low rank states with incomplete measurements*. DOI: [10.1088/1367-2630/18/4/043018](https://doi.org/10.1088/1367-2630/18/4/043018). URL: <https://arxiv.org/abs/1510.03229v2>.

*Commentary.*

For each natural rank r at least one, the assertion asks for a positive real c independent of n, ρ and v. Every rank-r density matrix on n qubits and every rank-r tangent must then have mean Pauli Fisher information at least c times the real part of trace(vv). The quantifier over n includes zero. This is a tangent formulation of the conjecture in Efficient-Ion-Tomography.tex, line 360. For a tangent v = Σₐ wₐ ∂ₐρ in local coordinates, trace(v²) = wᵀGw and the directional Fisher form is wᵀĪw, relating the inequality to the normalized minimum eigenvalue in that conjecture.

**Theorem 1.8 (Rank-one GHZ states violate the uniform lower bound).**

$$\neg (\operatorname{D5.S3.Quantum.Tomography.PauliFisherGHZRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/acharya-kypraios-guta-2016-pauli-fisher-ghz-refutation` (refuted) by `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"acharya-kypraios-guta-2016-pauli-fisher-ghz-refutation","declaration_gid":"D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Anirudh Acharya, Theodore Kypraios and Mădălin Guţă (2016). *Statistically efficient tomography of low rank states with incomplete measurements*. DOI: [10.1088/1367-2630/18/4/043018](https://doi.org/10.1088/1367-2630/18/4/043018). URL: <https://arxiv.org/abs/1510.03229v2>.

*Commentary.*

For n > 0, let a = 0ⁿ and b = 1ⁿ be the two distinct constant bit strings, with computational-basis vectors |a⟩ and |b⟩. Let E = exp(iθ), ψ = (|a⟩ + E|b⟩)/√2, ρ = |ψ⟩⟨ψ| and V = (i/2)(E|b⟩⟨a| − conjugate(E)|a⟩⟨b|). The identity E conjugate(E) = 1 gives the four nonzero corner entries of ρ. Its diagonal entries at a and b are 1/2, so its trace is one; the outer-product form is positive semidefinite and has rank one. Entrywise differentiation of exp(i(θ+t)) and its conjugate shows that the curve t ↦ ρ(θ+t) has derivative V at zero.

Expanding a quadratic form supported on the four corners indexed by a and b expresses its expectation using only the two coordinates u(a) and u(b). For V the expectation is (i/2)(E conjugate(u(b))u(a) − conjugate(E) conjugate(u(a))u(b)). For ρ it is one half of |u(a)|² + |u(b)|² + E conjugate(u(b))u(a) + conjugate(E) conjugate(u(a))u(b). Squaring V gives diagonal entries 1/4 at a and b and zero elsewhere. Thus the real part of trace(V²) is 1/2.

If a setting contains Z at some site, each product measurement vector u has u(a) = 0 or u(b) = 0, according to its outcome at that site. The expectation of V is therefore zero for every outcome, and this setting contributes zero Fisher information, including at zero-probability outcomes.

For a setting using only X and Y, the single-qubit spectral projectors give |uⱼ(0)|² = |uⱼ(1)|² = 1/2 and conjugate(uⱼ(1))uⱼ(0) = (−1)^(oⱼ)(1 if sⱼ = 0, otherwise −i)/2. Multiplying these identities over the sites gives |u(a)|² = |u(b)|² = 2^(−n) and conjugate(u(b))u(a) = q/2^n, where q = ∏ⱼ (−1)^(oⱼ)(1 if sⱼ = 0, otherwise −i). Consequently the probability is (1 + Re(Eq))/2^n and the directional readout is −Im(Eq)/2^n.

Every factor in q has fourth power one, hence q⁴ = 1 and q is one of 1, −1, i, −i. At θ = π/4, both Re(Eq)² and Im(Eq)² equal 1/2. It follows that every X/Y outcome probability is positive. The sum of q over all outcomes factors into the product of the single-site sums; each such sum is zero, and n > 0 supplies a site. Thus Σₒ q = 0. The Fisher summand simplifies to (1 − Re(Eq))/2^n, so summing over the 2^n outcomes gives Fisher information one for every X/Y setting.

The indicator that every site uses X or Y factors over sites. Summing it over all settings gives 2^n, since each site allows exactly two choices. Averaging the setting contributions over the 3^n Pauli settings therefore gives (2/3)^n. For every c > 0, geometric decay supplies n > 0 with 2(2/3)^n < c. If the asserted bound held, specialize it to r = 1, this n, the state at θ = π/4, and its phase derivative V. The curve above consists entirely of rank-one density matrices, so V satisfies the tangent condition. The bound would imply c/2 ≤ (2/3)^n, contradicting the chosen n. This disproves the universal assertion already at rank one; it makes no assertion about a lower bound restricted to higher ranks or to random measurement bases.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.IsRankTangent`
- Truth anchor: `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.averageFisher`
- Truth anchor: `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.outcomeProb`
- Truth anchor: `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.pauliEigen`
- Truth anchor: `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.productVector`
- Truth anchor: `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.result`
- Truth anchor: `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.settingFisher`
- Dependency: [D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation](../Information/LiTheilHarrowChuangPurifyCloneRefutation.md)
- Dependency: [D5/S3/Quantum/Magic/WignerDistanceMinimum](../Magic/WignerDistanceMinimum.md)
- Dependency: [D5/S3/QuantumBounds/NonlocalityDepthQuantumBound](../../QuantumBounds/NonlocalityDepthQuantumBound.md)
