# Target Sufficiency Pair Cover

## Abstract

Target sufficiency is exact coverage of target-disagreement pairs.

**Theorem 1.1 (Target sufficiency is target-pair coverage).**

$$\begin{aligned}\forall n: Nat, Experiment, Target: \operatorname{Type},\\Response: Experiment \to \operatorname{Type}, J: \operatorname{Finset}(Experiment),\\q: \forall e: Experiment, \operatorname{Fin}(n) \to Response(e),\\T: \operatorname{Fin}(n) \to Target,\\\operatorname{FactorsThrough}(T, \operatorname{jointReadout}(\operatorname{restrict}(q, J))) \iff \\\{\{x, y\} \mid T(x) \neq T(y)\} = \operatorname{Union}(e \in J, \{\{x, y\} \mid T(x) \neq T(y) \land q(e)(x) \neq q(e)(y)\}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentDesign/TargetSufficiencyPairCover.target_sufficiency_iff_pair_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Models are indexed by Fin(n), and J is a finite selection from the ambient experiment type. The selected observations are assembled by the canonical dependent joint readout.

The required unordered-pair universe contains exactly the model pairs with unequal target values. Each selected experiment contributes only those required pairs whose responses it separates.

The target is constant on joint-readout fibers exactly when those target-relevant separation sets cover the required universe. No baseline observation or full-state injectivity is assumed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentDesign/TargetSufficiencyPairCover.target_sufficiency_iff_pair_cover`
- Dependency: [D5/S3/ConceptDynamics/Experiment/FiniteExperimentCoverCriterion](../Experiment/FiniteExperimentCoverCriterion.md)
