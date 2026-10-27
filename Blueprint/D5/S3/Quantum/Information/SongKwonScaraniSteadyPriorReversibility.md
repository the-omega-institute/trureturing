# Stationarity does not imply tabletop time reversibility

## Abstract

A full-rank steady qutrit prior need not admit fixed-dilation tabletop reversal.

**Definition 1.1 (Forward dilation channel).**

$$\forall S \in \operatorname{Type},\; \forall E \in \operatorname{Type},\; [\operatorname{Fintype}\left(S\right)] [\operatorname{DecidableEq}\left(S\right)] [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(E\right)] \forall U \in \operatorname{Matrix}\left((S\times E), (S\times E), \mathbb{C}\right),\; \forall xi \in \operatorname{Matrix}\left(E, E, \mathbb{C}\right),\; \forall X \in \operatorname{Matrix}\left(S, S, \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility.channel}\left(U, xi, X\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(U \cdot \operatorname{Matrix.kronecker}\left(X, xi\right) \cdot \operatorname{Matrix.conjTranspose}\left(U\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.channel` (`✓ std3`).

*Citation.* M. Song, H. Kwon and V. Scarani (2025). *Exact and approximate conditions of tabletop reversibility: when is Petz recovery cost-free?*. DOI: [10.1088/2058-9565/aea92d](https://doi.org/10.1088/2058-9565/aea92d). URL: <https://arxiv.org/abs/2510.26895v1>.

*Commentary.*

Equation (1), page 2: "N(•) = Tr_E[U_SE (• ⊗ ξ_E) U_SE†]". S and E are finite index types with decidable equality; xi denotes ξ. The product index S × E places the system before the environment. PartialTraceMutualInformation.partialTraceRight traces out the environment.

**Definition 1.2 (Hilbert–Schmidt adjoint of the dilation channel).**

$$\forall S \in \operatorname{Type},\; \forall E \in \operatorname{Type},\; [\operatorname{Fintype}\left(S\right)] [\operatorname{DecidableEq}\left(S\right)] [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(E\right)] \forall U \in \operatorname{Matrix}\left((S\times E), (S\times E), \mathbb{C}\right),\; \forall xi \in \operatorname{Matrix}\left(E, E, \mathbb{C}\right),\; \forall Y \in \operatorname{Matrix}\left(S, S, \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility.channelAdjoint}\left(U, xi, Y\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\operatorname{Matrix.conjTranspose}\left(U\right) \cdot \operatorname{Matrix.kronecker}\left(Y, (1:\operatorname{Matrix}\left(E, E, \mathbb{C}\right))\right) \cdot U \cdot \operatorname{Matrix.kronecker}\left((1:\operatorname{Matrix}\left(S, S, \mathbb{C}\right)), xi\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.channelAdjoint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Song, H. Kwon and V. Scarani (2025). *Exact and approximate conditions of tabletop reversibility: when is Petz recovery cost-free?*. DOI: [10.1088/2058-9565/aea92d](https://doi.org/10.1088/2058-9565/aea92d). URL: <https://arxiv.org/abs/2510.26895v1>.

*Commentary.*

For the channel in equation (1), page 2, the Hilbert–Schmidt adjoint has action Tr_E[U†(Y ⊗ 1)U(1 ⊗ ξ)]. Matrix multiplication has the displayed order; the two identity matrices act on E and S respectively. This expression is derived from the forward dilation by cyclicity of the trace.

**Definition 1.3 (Petz recovery map).**

$$\forall S \in \operatorname{Type},\; \forall E \in \operatorname{Type},\; [\operatorname{Fintype}\left(S\right)] [\operatorname{DecidableEq}\left(S\right)] [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(E\right)] \forall U \in \operatorname{Matrix}\left((S\times E), (S\times E), \mathbb{C}\right),\; \forall xi \in \operatorname{Matrix}\left(E, E, \mathbb{C}\right),\; \forall gamma \in \operatorname{Matrix}\left(S, S, \mathbb{C}\right),\; \forall X \in \operatorname{Matrix}\left(S, S, \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility.petz}\left(U, xi, gamma, X\right) = \operatorname{CFC.sqrt}\left(gamma\right) \cdot \operatorname{D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility.channelAdjoint}\left(U, xi, (\operatorname{CFC.sqrt}\left(\operatorname{D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility.channel}\left(U, xi, gamma\right)\right))^{-1} \cdot X \cdot (\operatorname{CFC.sqrt}\left(\operatorname{D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility.channel}\left(U, xi, gamma\right)\right))^{-1}\right) \cdot \operatorname{CFC.sqrt}\left(gamma\right)$$

*Formalization.* `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.petz` (`✓ std3`).

*Citation.* M. Song, H. Kwon and V. Scarani (2025). *Exact and approximate conditions of tabletop reversibility: when is Petz recovery cost-free?*. DOI: [10.1088/2058-9565/aea92d](https://doi.org/10.1088/2058-9565/aea92d). URL: <https://arxiv.org/abs/2510.26895v1>.

*Commentary.*

Definition 1, equation (2), page 2: "N̂_γ^(P)(•) ≡ √γ N†( (1/√N(γ)) • (1/√N(γ)) ) √γ." gamma denotes γ. CFC.sqrt is the positive square root; inverse means the matrix inverse. The question below restricts gamma to positive definite matrices and assumes channel U xi gamma = gamma, so these square roots are invertible in the instance used here.

**Definition 1.4 (Reverse map with the same interaction).**

$$\forall S \in \operatorname{Type},\; \forall E \in \operatorname{Type},\; [\operatorname{Fintype}\left(S\right)] [\operatorname{DecidableEq}\left(S\right)] [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(E\right)] \forall U \in \operatorname{Matrix}\left((S\times E), (S\times E), \mathbb{C}\right),\; \forall eta \in \operatorname{Matrix}\left(E, E, \mathbb{C}\right),\; \forall X \in \operatorname{Matrix}\left(S, S, \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility.tabletopReverse}\left(U, eta, X\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\operatorname{Matrix.conjTranspose}\left(U\right) \cdot \operatorname{Matrix.kronecker}\left(X, eta\right) \cdot U\right)$$

*Formalization.* `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.tabletopReverse` (`✓ std3`).

*Citation.* M. Song, H. Kwon and V. Scarani (2025). *Exact and approximate conditions of tabletop reversibility: when is Petz recovery cost-free?*. DOI: [10.1088/2058-9565/aea92d](https://doi.org/10.1088/2058-9565/aea92d). URL: <https://arxiv.org/abs/2510.26895v1>.

*Commentary.*

Definition 2, equation (3), page 2: "N̂_ξ′^(T)(•) ≡ Tr_E[U_SE† (• ⊗ ξ′_E) U_SE]." eta denotes ξ′. U is the very same interaction used in the forward map; only the environmental state may change.

**Definition 1.5 (Tabletop time reversibility for a prior).**

$$\forall S \in \operatorname{Type},\; \forall E \in \operatorname{Type},\; [\operatorname{Fintype}\left(S\right)] [\operatorname{DecidableEq}\left(S\right)] [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(E\right)] \forall U \in \operatorname{Matrix}\left((S\times E), (S\times E), \mathbb{C}\right),\; \forall xi \in \operatorname{Matrix}\left(E, E, \mathbb{C}\right),\; \forall gamma \in \operatorname{Matrix}\left(S, S, \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility.IsTTR}\left(U, xi, gamma\right) \Leftrightarrow \left(\exists eta \in \operatorname{Matrix}\left(E, E, \mathbb{C}\right),\; (\operatorname{Matrix.PosSemidef}\left(eta\right)) \land ((\operatorname{Matrix.trace}\left(eta\right) = 1) \land (\forall X \in \operatorname{Matrix}\left(S, S, \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility.petz}\left(U, xi, gamma, X\right) = \operatorname{D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility.tabletopReverse}\left(U, eta, X\right)))\right)$$

*Formalization.* `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.IsTTR` (`✓ std3`).

*Citation.* M. Song, H. Kwon and V. Scarani (2025). *Exact and approximate conditions of tabletop reversibility: when is Petz recovery cost-free?*. DOI: [10.1088/2058-9565/aea92d](https://doi.org/10.1088/2058-9565/aea92d). URL: <https://arxiv.org/abs/2510.26895v1>.

*Commentary.*

Definition 2, equation (4), page 2: the channel is tabletop time-reversible for a prior γ "if there exists ξ′ = ξ′_γ such that its Petz recovery map N̂_γ^(P) is given by N̂_γ^(P) = N̂_ξ′^(T)". The existential eta is positive semidefinite and has trace one. Equality of the maps means equality on every system matrix X.

**Definition 1.6 (The stationary-prior assertion).**

$$\operatorname{D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility.claim} \Leftrightarrow (\forall S \in \operatorname{Type},\; \forall E \in \operatorname{Type},\; [\operatorname{Fintype}\left(S\right)] [\operatorname{DecidableEq}\left(S\right)] [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(E\right)] \forall U \in \operatorname{Matrix}\left((S\times E), (S\times E), \mathbb{C}\right),\; \forall xi \in \operatorname{Matrix}\left(E, E, \mathbb{C}\right),\; \forall gamma \in \operatorname{Matrix}\left(S, S, \mathbb{C}\right),\; (U \in \operatorname{Matrix.unitaryGroup}\left((S\times E), \mathbb{C}\right)) \Rightarrow ((\operatorname{Matrix.PosSemidef}\left(xi\right)) \Rightarrow ((\operatorname{Matrix.trace}\left(xi\right) = 1) \Rightarrow ((\operatorname{Matrix.PosDef}\left(gamma\right)) \Rightarrow ((\operatorname{Matrix.trace}\left(gamma\right) = 1) \Rightarrow ((\operatorname{D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility.channel}\left(U, xi, gamma\right) = gamma) \Rightarrow (\operatorname{D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility.IsTTR}\left(U, xi, gamma\right))))))))$$

*Formalization.* `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.claim` (`✓ std3`).

*Citation.* M. Song, H. Kwon and V. Scarani (2025). *Exact and approximate conditions of tabletop reversibility: when is Petz recovery cost-free?*. DOI: [10.1088/2058-9565/aea92d](https://doi.org/10.1088/2058-9565/aea92d). URL: <https://arxiv.org/abs/2510.26895v1>.

*Commentary.*

Section V, question 2, page 9: "In all of the examples we considered, a dynamics appears to be tabletop time-reversible whenever a prior state is a steady state. We do not have a proof that this is true in general, and leave it for a future investigation." The assertion ranges over finite system and environment types, a unitary U, a positive semidefinite trace-one xi, and a positive definite trace-one gamma fixed by channel U xi. It asks for IsTTR for this fixed U and xi.

**Theorem 1.7 (A qutrit stationary prior without tabletop reversal).**

$$\neg (\forall S \in \operatorname{Type},\; \forall E \in \operatorname{Type},\; [\operatorname{Fintype}\left(S\right)] [\operatorname{DecidableEq}\left(S\right)] [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(E\right)] \forall U \in \operatorname{Matrix}\left((S\times E), (S\times E), \mathbb{C}\right),\; \forall xi \in \operatorname{Matrix}\left(E, E, \mathbb{C}\right),\; \forall gamma \in \operatorname{Matrix}\left(S, S, \mathbb{C}\right),\; (U \in \operatorname{Matrix.unitaryGroup}\left((S\times E), \mathbb{C}\right)) \Rightarrow ((\operatorname{Matrix.PosSemidef}\left(xi\right)) \Rightarrow ((\operatorname{Matrix.trace}\left(xi\right) = 1) \Rightarrow ((\operatorname{Matrix.PosDef}\left(gamma\right)) \Rightarrow ((\operatorname{Matrix.trace}\left(gamma\right) = 1) \Rightarrow ((\operatorname{D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility.channel}\left(U, xi, gamma\right) = gamma) \Rightarrow (\operatorname{D5.S3.Quantum.Information.SongKwonScaraniSteadyPriorReversibility.IsTTR}\left(U, xi, gamma\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.result` (`✓ std3`). ∎

*Resolves.* `Problems/song-kwon-scarani-2025-steady-prior-reversibility` (refuted) by `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"song-kwon-scarani-2025-steady-prior-reversibility","declaration_gid":"D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. Song, H. Kwon and V. Scarani (2025). *Exact and approximate conditions of tabletop reversibility: when is Petz recovery cost-free?*. DOI: [10.1088/2058-9565/aea92d](https://doi.org/10.1088/2058-9565/aea92d). URL: <https://arxiv.org/abs/2510.26895v1>.

*Commentary.*

Take S = E = Fin 3, xi = Matrix.diagonal ![1/2, 1/3, 1/6], and gamma = Matrix.diagonal ![17/44, 13/44, 14/44]. The unitary exchanges (0,0) with (1,1), (1,0) with (2,2), and (2,0) with (0,2), with coefficient −Complex.I, and fixes (0,1), (1,2), and (2,1). The prior is positive definite, has trace one, and is stationary. For every environmental matrix eta, the tabletop output at (1,1) on Matrix.single 0 0 1 and at (2,2) on Matrix.single 1 1 1 both equal eta 0 0. The corresponding Petz entries are 13/51 and 7/39. Their inequality excludes every eta, including all density matrices. Only this fixed interaction is asserted; no statement about the whole continuous Hamiltonian family is proved here.

## References

- Truth anchor: `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.IsTTR`
- Truth anchor: `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.channel`
- Truth anchor: `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.channelAdjoint`
- Truth anchor: `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.claim`
- Truth anchor: `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.petz`
- Truth anchor: `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.result`
- Truth anchor: `D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility.tabletopReverse`
- Dependency: [D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation](../Foundation/FuchsLogarithmBasisRefutation.md)
- Dependency: [D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation](NMLWMeasuredFidelitySeparation.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](PartialTraceMutualInformation.md)
