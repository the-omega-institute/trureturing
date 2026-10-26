# The spatiotemporal Born rule dichotomy

## Abstract

A universal sequential Born representation exists exactly for a maximally mixed state or a discard-and-prepare channel.

**Definition 1.1 (One operator for all sequential projective outcomes).**

$$\forall (d: \mathbb{N}), (\forall (e: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (\varepsilon: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(e\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy.BornRuleExists}\left(\rho, \varepsilon\right)) \Leftrightarrow (\exists (w: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(e\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(e\right)), \mathbb{C}\right)), (\forall (p: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (q: \operatorname{Matrix}\left(\operatorname{Fin}\left(e\right), \operatorname{Fin}\left(e\right), \mathbb{C}\right)), ((\operatorname{IsStarProjection}\left(p\right)) \Rightarrow ((\operatorname{IsStarProjection}\left(q\right)) \Rightarrow (\operatorname{Matrix.trace}\left((w) \cdot (\operatorname{Matrix.kronecker}\left(p, q\right))\right) = \operatorname{Matrix.trace}\left((\varepsilon\left(((p) \cdot (\rho)) \cdot (p)\right)) \cdot (q)\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy.BornRuleExists` (`✓ std3`).

*Citation.* James Fullwood; Zhihao Ma; Zhen Wu (2026). *Quasiprobabilistic nature of the spatiotemporal Born rule*. DOI: [10.1103/cw25-pqx1](https://doi.org/10.1103/cw25-pqx1). URL: <https://arxiv.org/abs/2507.16919v2>.

*Commentary.*

BornRuleExists asks for a single complex bipartite operator w whose trace against every tensor product p ⊗ q equals the Lüders–von Neumann sequential probability tr(ε(pρp)q). Here p and q are self-adjoint idempotents on the input and output spaces. Every such p occurs in the projective measurement {p, 1 − p}, and the same holds for q. Thus quantification over individual projections expresses the condition for all projective measurements. No positivity, self-adjointness or trace normalization is imposed on w. The predicate is defined for all natural dimensions, all complex matrices ρ and all complex linear maps ε; the state and channel assumptions enter the dichotomy below. The source gives the sequential distribution in PRA_rev.tex, lines 247–250, and this representation condition in lines 534–537 of arXiv:2507.16919v2.

**Definition 1.2 (A fixed output density matrix).**

$$\forall (d: \mathbb{N}), (\forall (e: \mathbb{N}), (\forall (\varepsilon: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(e\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy.DiscardPrepare}\left(\varepsilon\right)) \Leftrightarrow (\exists (\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(e\right), \operatorname{Fin}\left(e\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\sigma\right)) \land (\forall (x: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\varepsilon\left(x\right) = (\operatorname{Matrix.trace}\left(x\right)) \cdot (\sigma))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy.DiscardPrepare` (`✓ std3`).

*Citation.* James Fullwood; Zhihao Ma; Zhen Wu (2026). *Quasiprobabilistic nature of the spatiotemporal Born rule*. DOI: [10.1103/cw25-pqx1](https://doi.org/10.1103/cw25-pqx1). URL: <https://arxiv.org/abs/2507.16919v2>.

*Commentary.*

DiscardPrepare means that there is one output density matrix σ such that ε(x) = tr(x)σ for every complex input matrix x. IsDensity requires positive semidefiniteness and trace one. The formula describes the map on all matrices, including matrices that are not states. This is the discard-and-prepare condition in Proposition 1, PRA_rev.tex, line 271 of arXiv:2507.16919v2.

**Definition 1.3 (The dichotomy in every positive finite dimension).**

$$(\operatorname{D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy.claim}) \Leftrightarrow (\forall (d: \mathbb{N}), (\forall (e: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (\varepsilon: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(e\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)) \Rightarrow ((\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.IsCPTP}\left(\varepsilon\right)) \Rightarrow (((1: \mathbb{N}) \le d) \Rightarrow (((1: \mathbb{N}) \le e) \Rightarrow ((\operatorname{D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy.BornRuleExists}\left(\rho, \varepsilon\right)) \Leftrightarrow ((\rho = (\frac{(1: \mathbb{C})}{(\operatorname{Nat.cast}\left(d\right): \mathbb{C})}) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)))) \lor (\operatorname{D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy.DiscardPrepare}\left(\varepsilon\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* James Fullwood; Zhihao Ma; Zhen Wu (2026). *Quasiprobabilistic nature of the spatiotemporal Born rule*. DOI: [10.1103/cw25-pqx1](https://doi.org/10.1103/cw25-pqx1). URL: <https://arxiv.org/abs/2507.16919v2>.

*Commentary.*

For every pair of positive natural dimensions d and e, every input density matrix ρ and every completely positive trace-preserving complex linear map ε, a universal sequential Born representation exists if and only if ρ is the identity divided by d or ε discards and prepares a fixed density matrix. The natural number d is cast to ℂ before division and scalar multiplication. The two alternatives may both hold. The necessity question appears in PRA_rev.tex, line 577 of arXiv:2507.16919v2; the displayed equivalence also includes both sufficient conditions.

**Theorem 1.4 (The spectral argument and the two representations).**

$$\operatorname{D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy.result` (`✓ std3`). ∎

*Resolves.* `Problems/fullwood-ma-wu-2026-spatiotemporal-born-dichotomy` (proved) by `D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fullwood-ma-wu-2026-spatiotemporal-born-dichotomy","declaration_gid":"D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* James Fullwood; Zhihao Ma; Zhen Wu (2026). *Quasiprobabilistic nature of the spatiotemporal Born rule*. DOI: [10.1103/cw25-pqx1](https://doi.org/10.1103/cw25-pqx1). URL: <https://arxiv.org/abs/2507.16919v2>.

*Commentary.*

Assume a representing operator w exists. Complex linear combinations of self-adjoint projections span the full square matrix space: the spectral theorem writes each self-adjoint matrix as a real linear combination of unitary conjugates of coordinate projections, and self-adjoint matrices span the complex algebra. Consequently a matrix whose trace pairing with every projection is zero is itself zero.

Fix an input projection p and an output projection q. The decomposition 1 = p + (1 − p) makes the trace pairing with w additive in the first projection. Substituting the sequential probabilities for p, 1 − p and 1 shows that tr(ε(ρ − pρp − (1 − p)ρ(1 − p))q) = 0. Trace separation and expansion of the two products give ε(pρ + ρp) = 2ε(pρp) for every projection p.

Write |u⟩⟨v| for the rank-one matrix u v*. Products satisfy (|u⟩⟨v|)x(|w⟩⟨t|) = (v*xw)|u⟩⟨t|. If w*w = c with c a nonzero real number, then c⁻¹|w⟩⟨w| is a self-adjoint projection. Applying the preceding identity to this projection and clearing its scalar denominator yields c ε(|w⟩⟨w|ρ + ρ|w⟩⟨w|) = 2ε(|w⟩⟨w|ρ|w⟩⟨w|).

Take orthonormal eigenvectors u and v of ρ with distinct real eigenvalues r and s. Set A = ε(|u⟩⟨u|), B = ε(|v⟩⟨v|), T = ε(|u⟩⟨v|) and S = ε(|v⟩⟨u|). For real a and b with a² + b² ≠ 0 and a complex phase z with conjugate(z)z = 1, use w = au + bzv and c = a² + b². Expanding its outer product and using the eigenvector equations gives an equality involving A, B, T and S. The choices (a,b,z) = (1,1,1), (3,4,1) and (3,4,i) first give (r − s)(A − B) = 0, then (r − s)(T + S) = 0 and (r − s)(−iT + iS) = 0. Since r ≠ s, these imply A = B and T = S = 0.

Choose an orthonormal eigenbasis v indexed by Fin d, with real eigenvalues r. If every r i equals every r j, the spectral decomposition gives ρ = (r i₀)1 for any index i₀, which exists because d is positive. Taking traces and using tr(ρ) = 1 gives (r i₀)d = 1, hence ρ = (1/(d : ℂ))1.

Otherwise choose i₀ and j₀ with r i₀ ≠ r j₀, and put σ = ε(|v i₀⟩⟨v i₀|). Comparing any basis vector with either v i₀ or v j₀ by the distinct-eigenvalue calculation shows ε(|v i⟩⟨v i|) = σ for every i. It also annihilates |v i⟩⟨v j| whenever their eigenvalues differ.

For distinct i and j with the same eigenvalue, choose k with r i ≠ r k. For z equal to 1 and i, the vector (v i + z v j)/√2 is a unit eigenvector orthogonal to v k. Their eigenvalues differ, so the image of its rank-one projector equals σ. Expanding this projector and cancelling the already equal diagonal images gives conjugate(z) ε(|v i⟩⟨v j|) + z ε(|v j⟩⟨v i|) = 0. The two phase choices force both off-diagonal images to vanish, including within every degenerate eigenspace.

Completeness of the eigenbasis gives the identity as the sum of |v i⟩⟨v i|. Multiplying an arbitrary matrix x on both sides by this sum expands x as the sum over i and j of ((v i)*x(v j))|v i⟩⟨v j|. Applying ε leaves only the diagonal coefficients, whose sum is tr(x). Thus ε(x) = tr(x)σ for every x. Complete positivity makes σ positive semidefinite, and trace preservation gives tr(σ) = 1. This proves the discard-and-prepare alternative when the state is not scalar.

Conversely, if ρ = (1/(d : ℂ))1, take w = (1/(d : ℂ)) times the sum over i,j in Fin d of Eᵢⱼ ⊗ ε(Eⱼᵢ), where Eᵢⱼ is the coordinate matrix with entry one at (i,j). The identity pρp = (1/(d : ℂ))p for a projection p, the coordinate-matrix expansion of ε(p), and the product rule for traces of tensor products give the required pairing with every p ⊗ q. If ε(x) = tr(x)σ, instead take w = ρ ⊗ σ. Cyclicity of trace and p² = p give tr(pρp) = tr(ρp), so this tensor product also has the required pairing. Both sufficient constructions use only complex linearity and the stated alternative.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy.BornRuleExists`
- Truth anchor: `D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy.DiscardPrepare`
- Truth anchor: `D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy.result`
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](../Information/SLDSpectralEnergy.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation](../QuantumChannels/ChannelAssemblageLOSRRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility](../QuantumChannels/ElementaryChannelDivisibility.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation](../QuantumChannels/PositiveFilterTransposeRefutation.md)
- Dependency: [D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality](../../QuantumBounds/SicMubCorrelationTraceNormEquality.md)
