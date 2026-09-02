# Fifth-Stage Evidence, Belief, and Decision Theorem Map

## Abstract

A typed fifth-stage map joins evidence separation, belief sufficiency, stopping risk, Bellman optimality, and adaptive observation cost.

**Theorem 1.1 (The typed components of statistical and active completion).**

$$\begin{gathered}KakutaniBridge\left(\right) \land DivergentPairEvidence\left(\right) \Rightarrow PairwiseSingular\left(L, x, y\right) \land ZeroErrorClassifier\left(L\right),\\{}pi_{h} = pi_{h^{prime}} \Rightarrow SameAdaptiveFutureLaws\left(\right) \land SameContinuationValues\left(\right),\\{}PosteriorThresholdStop\left(epsilon\right) \Rightarrow MAPRisk\left(\right) \le epsilon,\\{}0 < gamma < 1 \land Stochastic\left(\right) \Rightarrow GammaContraction\left(T\right) \land UniqueFixedValue\left(T, V^{*}\right),\\{}Greedy\left(mu, V^{*}\right) \Rightarrow V^{mu} = V^{*},\\{}0 < epsilon < \frac{1}{2} \Rightarrow Exact\left(C_{adaptive}\right) \land Expected\left(C_{adaptive}\right) = 1 + 2 \times epsilon < Expected\left(C_{static}\right) = 2,\\{}\exists Countermodel\left(\right): DivergentPairEvidence\left(\right) \land \neg PairwiseSingular\left(L, x, y\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/FifthStageEvidenceBeliefDecisionTheoremMap.fifth_stage_evidence_belief_decision_theorem_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the named evidence-to-singularity bridge, divergent pair evidence yields mutually singular transcript laws and a common zero-error classifier.

Equal posteriors determine finite-horizon adaptive future laws and continuation values, while stopping in a posterior threshold region bounds the resulting MAP error.

For a finite discounted ordinary MDP, the Bellman operator is a strict contraction with a unique fixed value and every globally greedy stationary policy realizes that value.

A concrete three-state tree retains exact identification and strictly reduces expected calls. The final countermodel records that the abstract evidence bridge cannot be omitted.

This theorem deliberately does not identify the components with one closed-loop common fixed point: that sequential synthesis is not available in the repository or pinned Mathlib.

## References

- Truth anchor: `D5/S3/Observer/Completion/FifthStageEvidenceBeliefDecisionTheoremMap.fifth_stage_evidence_belief_decision_theorem_map`
- Dependency: [D5/S3/ConceptDynamics/ExperimentDesign/ThreeStateAdaptiveEarlyStopping](../../ConceptDynamics/ExperimentDesign/ThreeStateAdaptiveEarlyStopping.md)
- Dependency: [D5/S3/Estimation/DataProcessing/AdaptivePosteriorPolicySufficiency](../../Estimation/DataProcessing/AdaptivePosteriorPolicySufficiency.md)
- Dependency: [D5/S3/Estimation/DecisionRisk/PosteriorStoppingMapErrorBound](../../Estimation/DecisionRisk/PosteriorStoppingMapErrorBound.md)
- Dependency: [D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality](../DynamicProgramming/StationaryPolicyOptimality.md)
- Dependency: [D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion](../MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.md)
