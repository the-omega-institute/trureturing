# A counterexample to Zhang–Wu–Fei superadditivity

## Abstract

A maximally mixed two-qubit input and a full-rank correlated diagonal reference contradict relative-entropy superadditivity.

**Definition 1.1 (The unitary superadditivity conjecture).**

$$\operatorname{claim} \Leftrightarrow (\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (rho: \operatorname{DensityState}\left((\operatorname{Fin}\left(a\right)\times \operatorname{Fin}\left(b\right))\right)), (\forall (sigma: \operatorname{DensityState}\left((\operatorname{Fin}\left(a\right)\times \operatorname{Fin}\left(b\right))\right)), (((\operatorname{CStarMatrix}.\operatorname{ofMatrix}.\operatorname{symm}\left(\operatorname{val}\left(sigma\right)\right)).\operatorname{PosDef}) \Rightarrow (\exists (UAB: \operatorname{Matrix}\left((\operatorname{Fin}\left(a\right)\times \operatorname{Fin}\left(b\right)), (\operatorname{Fin}\left(a\right)\times \operatorname{Fin}\left(b\right)), \mathbb{C}\right)), (\exists (hAB: UAB\in \operatorname{Matrix}.\operatorname{unitaryGroup}\left((\operatorname{Fin}\left(a\right)\times \operatorname{Fin}\left(b\right)), \mathbb{C}\right)), (\exists (UA: \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(a\right), \mathbb{C}\right)), (\exists (hA: UA\in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(a\right), \mathbb{C}\right)), (\exists (UB: \operatorname{Matrix}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)), (\exists (hB: UB\in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(b\right), \mathbb{C}\right)), (\operatorname{quantumRelativeEntropy}\left(\operatorname{unitaryConjugateState}\left(UA, hA, \operatorname{marginalRight}\left(rho\right)\right), \operatorname{marginalRight}\left(sigma\right)\right) + \operatorname{quantumRelativeEntropy}\left(\operatorname{unitaryConjugateState}\left(UB, hB, \operatorname{marginalLeft}\left(rho\right)\right), \operatorname{marginalLeft}\left(sigma\right)\right) \le \operatorname{quantumRelativeEntropy}\left(\operatorname{unitaryConjugateState}\left(UAB, hAB, rho\right), sigma\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/ZhangWuFeiSuperadditivityRefutation.claim` (`✓ std3`).

*Citation.* Lin Zhang, Junde Wu, and Shao-Ming Fei (2013). *Comment on 'Convergence of macrostates under reproducible processes' [Phys. Lett. A 374: 3715–3717 (2010)]*. DOI: [10.1016/j.physleta.2013.05.047](https://doi.org/10.1016/j.physleta.2013.05.047). URL: <https://arxiv.org/abs/1210.4720v4>.

*Commentary.*

Zhang, Wu and Fei, arXiv:1210.4720v4, p. 6, §4: “Based on the above result, we propose the following conjecture: There exist unitary operators U_A ∈ U(H_A), U_B ∈ U(H_B) and U_AB ∈ U(H_A ⊗ H_B) such that S(U_AB ρ_AB U_AB† ‖ σ_AB) ⩾ S(U_A ρ_A U_A† ‖ σ_A) + S(U_B ρ_B U_B† ‖ σ_B), (4.2) where the reference state σ_AB is required to be full-ranked state. Indeed, our numerical calculations show that inequality (4.2) is true.”

The dimensions a and b range over natural numbers. DensityState means a positive semidefinite complex matrix of trace one. The first subsystem is Fin a and the second is Fin b. marginalRight retains A, while marginalLeft retains B. PosDef expresses full rank of the reference. quantumRelativeEntropy is Re Tr(ρ(log ρ − log σ)), with natural logarithms. The three matrices and their membership proofs express independent joint and local unitaries.

**Theorem 1.2 (The conjecture fails for two qubits).**

$$\neg (\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (rho: \operatorname{DensityState}\left((\operatorname{Fin}\left(a\right)\times \operatorname{Fin}\left(b\right))\right)), (\forall (sigma: \operatorname{DensityState}\left((\operatorname{Fin}\left(a\right)\times \operatorname{Fin}\left(b\right))\right)), (((\operatorname{CStarMatrix}.\operatorname{ofMatrix}.\operatorname{symm}\left(\operatorname{val}\left(sigma\right)\right)).\operatorname{PosDef}) \Rightarrow (\exists (UAB: \operatorname{Matrix}\left((\operatorname{Fin}\left(a\right)\times \operatorname{Fin}\left(b\right)), (\operatorname{Fin}\left(a\right)\times \operatorname{Fin}\left(b\right)), \mathbb{C}\right)), (\exists (hAB: UAB\in \operatorname{Matrix}.\operatorname{unitaryGroup}\left((\operatorname{Fin}\left(a\right)\times \operatorname{Fin}\left(b\right)), \mathbb{C}\right)), (\exists (UA: \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(a\right), \mathbb{C}\right)), (\exists (hA: UA\in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(a\right), \mathbb{C}\right)), (\exists (UB: \operatorname{Matrix}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)), (\exists (hB: UB\in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(b\right), \mathbb{C}\right)), (\operatorname{quantumRelativeEntropy}\left(\operatorname{unitaryConjugateState}\left(UA, hA, \operatorname{marginalRight}\left(rho\right)\right), \operatorname{marginalRight}\left(sigma\right)\right) + \operatorname{quantumRelativeEntropy}\left(\operatorname{unitaryConjugateState}\left(UB, hB, \operatorname{marginalLeft}\left(rho\right)\right), \operatorname{marginalLeft}\left(sigma\right)\right) \le \operatorname{quantumRelativeEntropy}\left(\operatorname{unitaryConjugateState}\left(UAB, hAB, rho\right), sigma\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ZhangWuFeiSuperadditivityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-wu-fei-2012-relative-entropy-superadditivity-conjecture-4-2` (refuted) by `D5/S3/Quantum/Information/ZhangWuFeiSuperadditivityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-wu-fei-2012-relative-entropy-superadditivity-conjecture-4-2","declaration_gid":"D5/S3/Quantum/Information/ZhangWuFeiSuperadditivityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Lin Zhang, Junde Wu, and Shao-Ming Fei (2013). *Comment on 'Convergence of macrostates under reproducible processes' [Phys. Lett. A 374: 3715–3717 (2010)]*. DOI: [10.1016/j.physleta.2013.05.047](https://doi.org/10.1016/j.physleta.2013.05.047). URL: <https://arxiv.org/abs/1210.4720v4>.

*Commentary.*

Take a = b = 2, ρ = I/4 and σ = diag(61,1,1,1)/64 in product order (0,0), (0,1), (1,0), (1,1). All four reference eigenvalues are positive. The two input marginals equal I/2, and the two reference marginals equal diag(31,1)/32. Every unitary fixes the input and its marginals.

The joint relative entropy is log(1/4) − log(61/64)/4 − 3 log(1/64)/4. Each marginal relative entropy is log(1/2) − log(31/32)/2 − log(1/32)/2. Four times the difference between the joint value and twice the marginal value is log(923521/3997696), which is negative. Thus no choice of the three unitaries satisfies the displayed inequality.

## References

- Truth anchor: `D5/S3/Quantum/Information/ZhangWuFeiSuperadditivityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/ZhangWuFeiSuperadditivityRefutation.result`
- Dependency: [D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition](../Divergence/QuantumRelativeEntropyDefectComposition.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](../Dynamics/ProjectionProbabilityFlow.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation](ChenKatoBrandaoCMIRefutation.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation](../Subentropy/StrongSubadditivityRefutation.md)
