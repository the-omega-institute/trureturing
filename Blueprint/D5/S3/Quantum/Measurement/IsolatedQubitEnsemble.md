# An isolated qubit ensemble

## Abstract

A four-state qubit ensemble with unequal positive priors has a unique minimum-error POVM. Every completely positive trace-preserving channel sharing an optimal POVM with this ensemble is the identity.

**Definition 1.1 (Minimum-error optimality).**

$$\forall n \in \mathbb{N},\; \forall q \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \forall rho \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall M \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{IsOptimalPOVM}\left(q, rho, M\right) \Leftrightarrow ((\operatorname{IsPOVM}\left(M\right)) \land (\forall F \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{IsPOVM}\left(F\right)) \Rightarrow (\sum_{i : \operatorname{Fin}\left(n\right)} (q\left(i\right) \cdot \operatorname{Matrix.trace}\left(rho\left(i\right) \cdot F\left(i\right)\right).re) \le \sum_{i : \operatorname{Fin}\left(n\right)} (q\left(i\right) \cdot \operatorname{Matrix.trace}\left(rho\left(i\right) \cdot M\left(i\right)\right).re))))$$

*Formalization.* `D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.IsOptimalPOVM` (`✓ std3`).

*Citation.* Spiros Kechrimparis; Joonwoo Bae (2020). *Optimal measurement preserving qubit channels*. DOI: [10.1088/1367-2630/abcc9b](https://doi.org/10.1088/1367-2630/abcc9b). URL: <https://arxiv.org/abs/2006.16366>.

*Commentary.*

The goal of minimum error state discrimination is to find the measurement strategy that minimizes the error in guessing the states of a known ensemble correctly, or equivalently, to find the strategy that maximizes the probability of guessing correctly on average. (arXiv PDF, p. 2.) For n labels in Fin n, q gives the real priors and rho gives complex two-by-two matrices. The predicate requires M to be a POVM and compares its success probability with every POVM F on the same labels. Positivity and normalization of the ensemble are separate hypotheses of the assertion below. Matrix.trace(rho(i) * F(i)).re is the real success contribution.

**Definition 1.2 (Optimal measurement preservation).**

$$\forall n \in \mathbb{N},\; \forall q \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \forall rho \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall N \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{IsOMP}\left(q, rho, N\right) \Leftrightarrow (\exists M \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{IsOptimalPOVM}\left(q, rho, M\right)) \land (\operatorname{IsOptimalPOVM}\left(q, (fun i : \operatorname{Fin}\left(n\right) \mapsto N\left(rho\left(i\right)\right)), M\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.IsOMP` (`✓ std3`).

*Citation.* Spiros Kechrimparis; Joonwoo Bae (2020). *Optimal measurement preserving qubit channels*. DOI: [10.1088/1367-2630/abcc9b](https://doi.org/10.1088/1367-2630/abcc9b). URL: <https://arxiv.org/abs/2006.16366>.

*Commentary.*

Definition 1 (arXiv PDF, pp. 2–3): We call a channel 𝒩 optimal measurement preserving (OMP) for an ensemble of states S={qₓ,ρₓ}ⁿₓ₌₁, if an optimal measurement before and after a channel use is the same. The encoding asks for one POVM M optimal both for rho and for the family i maps to N(rho(i)); N is a complex-linear matrix map. Complete positivity and trace preservation are imposed where channels are quantified.

**Definition 1.3 (Isolation).**

$$\forall n \in \mathbb{N},\; \forall q \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \forall rho \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{IsIsolated}\left(q, rho\right) \Leftrightarrow (\forall N \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{IsCPTP}\left(N\right)) \Rightarrow ((\operatorname{IsOMP}\left(q, rho, N\right)) \Rightarrow (N = \operatorname{LinearMap.id})))$$

*Formalization.* `D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.IsIsolated` (`✓ std3`).

*Citation.* Spiros Kechrimparis; Joonwoo Bae (2020). *Optimal measurement preserving qubit channels*. DOI: [10.1088/1367-2630/abcc9b](https://doi.org/10.1088/1367-2630/abcc9b). URL: <https://arxiv.org/abs/2006.16366>.

*Commentary.*

Conclusions (arXiv PDF, p. 11): The first concerns the existence of ensembles whose OMP sets are all trivial. This would imply that such ensembles are isolated in that any CPTP map acting on them necessarily changes all optimal measurements. Trivial here means that the OMP set contains only the identity. Thus every CPTP map N sharing an optimal POVM with the original ensemble must equal LinearMap.id.

**Definition 1.4 (The expectation that no isolated ensembles exist).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; \forall q \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \forall rho \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\forall i \in \operatorname{Fin}\left(n\right),\; 0 < q\left(i\right)) \Rightarrow ((\sum_{i : \operatorname{Fin}\left(n\right)} (q\left(i\right)) = 1) \Rightarrow ((\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsDensity}\left(rho\left(i\right)\right)) \Rightarrow (\neg \operatorname{IsIsolated}\left(q, rho\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.claim` (`✓ std3`).

*Citation.* Spiros Kechrimparis; Joonwoo Bae (2020). *Optimal measurement preserving qubit channels*. DOI: [10.1088/1367-2630/abcc9b](https://doi.org/10.1088/1367-2630/abcc9b). URL: <https://arxiv.org/abs/2006.16366>.

*Commentary.*

Conclusions (arXiv PDF, p. 11): We expect that no isolated ensembles exist but we have not managed to establish the result in general. The assertion ranges over every natural number n, every strictly positive normalized real prior family on Fin n, and every family of positive semidefinite complex two-by-two matrices of trace one. It says that each such ensemble fails IsIsolated. Zero-outcome families cannot satisfy the normalization hypothesis.

**Theorem 1.5 (Four states refute the expectation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.result` (`✓ std3`). ∎

*Resolves.* `Problems/kechrimparis-bae-2020-isolated-qubit-ensembles` (refuted) by `D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kechrimparis-bae-2020-isolated-qubit-ensembles","declaration_gid":"D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Spiros Kechrimparis; Joonwoo Bae (2020). *Optimal measurement preserving qubit channels*. DOI: [10.1088/1367-2630/abcc9b](https://doi.org/10.1088/1367-2630/abcc9b). URL: <https://arxiv.org/abs/2006.16366>.

*Commentary.*

Set G=19 and use the priors (9,9,5,5)/28. Let the four Pauli directions be (3/5,0,4/5), (-3/5,0,4/5), (0,3/5,-4/5), (0,-3/5,-4/5). Write S(i) for the corresponding Pauli matrix. The first two states are (I-S(i)/18)/2; the last two are (I-9S(i)/10)/2. The effects (I-S(i))/4 are positive and sum to I. The dual matrix 19 I/112 has positive slacks of weights 1/56,1/56,9/56,9/56. Equality in the score bound forces each effect into the one-dimensional slack kernel; completeness fixes their weights, giving a unique optimum.

For a channel preserving this optimum, positive quadratic perturbations of individual effects give eight stationarity equalities. The state family spans all two-by-two complex matrices, so these equalities determine the channel on the entire matrix space. Its affine Bloch linear part has diagonal entries 1-9 epsilon, 1-epsilon, 1-9 epsilon/5+tZ and third-column entries tX,tY. Positivity of the Choi matrix forces epsilon=0, followed by tZ=tX=tY=0. The only preserving CPTP channel is therefore the identity, and the positive normalized ensemble contradicts claim.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.IsIsolated`
- Truth anchor: `D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.IsOMP`
- Truth anchor: `D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.IsOptimalPOVM`
- Truth anchor: `D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.result`
- Dependency: [D5/S3/Quantum/Measurement/QuadraticPovmStationarity](QuadraticPovmStationarity.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction](../QuantumChannels/HiaiRuskaiRiemannianContraction.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence](../QuantumChannels/IptPptSquaredEquivalence.md)
- Dependency: [D5/S3/QuantumStates/ZeroWeightSupportFace](../../QuantumStates/ZeroWeightSupportFace.md)
