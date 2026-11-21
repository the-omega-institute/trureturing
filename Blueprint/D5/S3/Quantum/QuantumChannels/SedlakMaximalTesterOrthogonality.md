# Maximal incompatibility of one-step testers

## Abstract

One-step testers are maximally incompatible exactly when their normalization states are orthogonal.

Let d₀ and d₁ be the input and output dimensions, and p and q the respective outcome counts of A and B. Write HasNormalization(A, ρ) when A has positive semidefinite effects with sum I ⊗ ρ, and likewise for B and σ. The density condition additionally requires the input matrix to be positive semidefinite with trace one. Tester robustness is the infimum of the mixing weights in the unit interval at which separate arbitrary noise testers make the mixtures marginals of a joint tester.

**Definition 1.1 (Entry of the explicit joint cover).**

$$\operatorname{coverEntry}\left(p, q, \varepsilon, M, X, Y\right)=\frac{X}{q}+\frac{Y}{p}-\varepsilon(XY+YX)+\frac{M\varepsilon^{2}}{pq}I$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.coverEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This matrix-valued definition takes real p, q, ε and M and complex square matrices X and Y on a common finite index type with decidable equality. The identity acts on that same matrix space. The positive-count and size conditions used for the cover are hypotheses of the construction theorem.

**Definition 1.2 (Positive cover with dominating marginals).**

$$\begin{aligned}\operatorname{IsJointCover}\left(A, B, C, H\right)&\Leftrightarrow(\forall j,k,C(j,k)\geq0)\land(\sum_{j,k}C(j,k)=\operatorname{liftInput}\left(H\right))\\&\land(\forall j,A_{j}\leq\sum_{k}C(j,k))\land(\forall k,B_{k}\leq\sum_{j}C(j,k))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.IsJointCover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A, B and C act on output times input, and H acts on input. The lift is I ⊗ H. The inequalities use positive semidefinite order. The sum over j,k is over all product outcomes. This is the feasible cover in the one-step specialization of Ragini–Sazim's published covering SDP, Appendix A, (A18)–(A28).

**Theorem 1.3 (Construct a joint cover).**

$$0\leq\varepsilon\leq\min(p^{-1},q^{-1})\quad\max(p^{2},q^{2})\leq M\quad\longrightarrow\quad\operatorname{IsJointCover}\left(A, B, C, H\right)\quad C(j,k)=\operatorname{coverEntry}\left(p, q, \varepsilon, M, A_{j}, B_{k}\right)\quad H=\rho+\sigma-\varepsilon(\rho\sigma+\sigma\rho)+M\varepsilon^{2}I_{d_{0}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.explicitJointCover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive p and q, input density matrices ρ and σ, and families with the corresponding normalization identities and positive effects, take real ε and M satisfying the displayed bounds. The effects and lifted states are positive contractions. Expanding the square of the difference of the two effects gives entry positivity. Completing a positive sandwich with the opposite lifted state gives row and column domination because M bounds the squares of both outcome counts. Summing the entries gives the lift of H.

**Theorem 1.4 (Convert a cover into actual mixing witnesses).**

$$t=\Re\operatorname{tr}\left(H\right)\quad1\leq t\land\operatorname{TesterCompatibleAt}\left(1-t^{-1}, A, B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.compatibleAt_of_jointCover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume positive output dimension, density matrices ρ and σ, the corresponding normalization hypotheses on A and B, and a joint cover C with input matrix H. Taking traces of the input normalization inequalities gives t ≥ 1. Divide the cover by t. If t > 1, divide its two marginal slacks by t − 1 for the two noise testers. If t = 1, the positive slacks vanish, so the cover already has the required marginals at zero weight.

**Theorem 1.5 (Strict upper bound from normalization overlap).**

$$\delta=\Re\operatorname{tr}\left(\rho\sigma\right)\quad t=2-\frac{\delta^{2}}{\max(p,q)^{2}d_{0}}\quad1\leq t\land \left(R_{t}\right)\left(A, B\right)\leq1-t^{-1}\land1-t^{-1}<\frac{1}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.nonorthogonal_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume positive d₀, d₁, p and q, input densities ρ and σ, the corresponding normalization hypotheses on A and B, and ρσ ≠ 0. The real trace δ of ρσ lies in (0, 1]. With M = max(p,q)², the choice ε = δ/(M d₀) satisfies the cover bounds. Substituting it in the real trace of H gives the displayed t. The cover-to-compatibility theorem supplies the feasible weight 1 − 1/t, so the same weight bounds the infimum.

**Theorem 1.6 (Normalization and effectwise orthogonality).**

$$\rho\sigma=0\Leftrightarrow\forall j,k,A_{j}B_{k}=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.normalization_orthogonal_iff_effectwise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michal Sedlák; Daniel Reitzner; Giulio Chiribella; Mário Ziman (2016). *Incompatible measurements on quantum causal networks*. DOI: [10.1103/PhysRevA.93.052323](https://doi.org/10.1103/PhysRevA.93.052323). URL: <https://arxiv.org/abs/1511.00976v2>.

*Commentary.*

Assume positive output dimension, that ρ is an input density matrix, and the positivity and sum hypotheses for A with ρ and B with σ. This is the operator equivalence used in Proposition 12 of Sedlák et al. If the normalization product vanishes, trace monotonicity bounds each positive effect pairing by zero. Zero trace pairing of positive matrices forces their product to vanish. Conversely, summing the zero products gives I ⊗ (ρσ) = 0, and the lift is injective.

**Definition 1.7 (Maximal robustness and orthogonality).**

$$\begin{aligned}claim&\Leftrightarrow\forall d_{0},d_{1},p,q>0,\quad\forall A,B,\rho,\sigma,\\&(\operatorname{IsDensity}\left(\rho\right)\land\operatorname{IsDensity}\left(\sigma\right)\land\operatorname{IsTester}\left(A\right)\land\operatorname{IsTester}\left(B\right)\land\operatorname{HasNormalization}\left(A, \rho\right)\land\operatorname{HasNormalization}\left(B, \sigma\right))\\&\longrightarrow(\left(R_{t}\right)\left(A, B\right)=\frac{1}{2}\Leftrightarrow\rho\sigma=0)\land(\rho\sigma=0\Leftrightarrow\forall j,k,A_{j}B_{k}=0)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michal Sedlák; Daniel Reitzner; Giulio Chiribella; Mário Ziman (2016). *Incompatible measurements on quantum causal networks*. DOI: [10.1103/PhysRevA.93.052323](https://doi.org/10.1103/PhysRevA.93.052323). URL: <https://arxiv.org/abs/1511.00976v2>.

*Commentary.*

For every positive d₀, d₁, p and q, the families A and B are indexed by Fin p and Fin q and act on Fin d₁ × Fin d₀. The input matrices ρ and σ act on Fin d₀. The hypotheses explicitly require both densities, both tester predicates, and the two positivity and normalization conditions HasNormalization(A, ρ) and HasNormalization(B, σ). The displayed conjunction is the conclusion under all these hypotheses.

**Theorem 1.8 (Resolve the §V.C converse).**

$$\begin{aligned}&\forall d_{0},d_{1},p,q>0,\quad\forall A,B,\rho,\sigma,\\&(\operatorname{IsDensity}\left(\rho\right)\land\operatorname{IsDensity}\left(\sigma\right)\land\operatorname{IsTester}\left(A\right)\land\operatorname{IsTester}\left(B\right)\land\operatorname{HasNormalization}\left(A, \rho\right)\land\operatorname{HasNormalization}\left(B, \sigma\right))\\&\longrightarrow(\left(R_{t}\right)\left(A, B\right)=\frac{1}{2}\Leftrightarrow\rho\sigma=0)\land(\rho\sigma=0\Leftrightarrow\forall j,k,A_{j}B_{k}=0)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.result` (`✓ std3`). ∎

*Resolves.* `Problems/sedlak-reitzner-chiribella-ziman-2016-maximal-tester-orthogonality` (proved) by `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sedlak-reitzner-chiribella-ziman-2016-maximal-tester-orthogonality","declaration_gid":"D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Michal Sedlák; Daniel Reitzner; Giulio Chiribella; Mário Ziman (2016). *Incompatible measurements on quantum causal networks*. DOI: [10.1103/PhysRevA.93.052323](https://doi.org/10.1103/PhysRevA.93.052323). URL: <https://arxiv.org/abs/1511.00976v2>.

*Commentary.*

The result proves claim with the same quantifiers and hypotheses. For nonorthogonal input states, the strict upper bound supplies a feasible noise weight below one half. The zero-perturbation cover gives compatibility at one half for all such tester pairs.

For orthogonal input states, any compatible pair has a joint normalization dominating each original state scaled by 1 − λ. Taking traces against the support and kernel projections of ρ gives 1 ≥ 2(1 − λ), so the infimum is at least one half. Proposition 12's effectwise equivalence gives the second conjunct.

Ragini and Sazim formulate one-step compatibility using a joint cover in New Journal of Physics (2024), DOI 10.1088/1367-2630/ad93f6. The positive joint family above gives the quantitative estimate and the strict inequality for nonorthogonal inputs.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.IsJointCover`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.compatibleAt_of_jointCover`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.coverEntry`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.explicitJointCover`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.nonorthogonal_upper_bound`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.normalization_orthogonal_iff_effectwise`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.result`
- Dependency: [D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity](../Measurements/FiniteMemoryHistoryCapacity.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality](AncillaFreeTesterRobustnessEquality.md)
