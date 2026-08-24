# Target-Relative Experiment Superiority

## Abstract

Incomparable experiments each serve a target that the other does not.

**Theorem 1.1 (Incomparable experiments have opposite target advantages).**

$$\forall X, E_{1}, E_{2}: \operatorname{Type},\\{}q_{1}: X \to E_{1}, q_{2}: X \to E_{2},\\{}(\neg \operatorname{Refines}\left(q_{1}, q_{2}\right) \land \neg \operatorname{Refines}\left(q_{2}, q_{1}\right)) \Rightarrow\\{}((\exists t_{1}: X \to E_{1}, \operatorname{Refines}\left(t_{1}, q_{1}\right) \land \neg \operatorname{Refines}\left(t_{1}, q_{2}\right)) \land (\exists t_{2}: X \to E_{2}, \operatorname{Refines}\left(t_{2}, q_{2}\right) \land \neg \operatorname{Refines}\left(t_{2}, q_{1}\right))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiments/TargetRelativeExperimentSuperiority.incomparable_experiments_have_opposite_target_advantages` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the first experiment itself as the first target. Reflexivity makes that target available from the first experiment, while the assumed non-refinement excludes it from the second.

Choosing the second experiment itself gives the symmetric witness. Both directional target advantages occur in the public conclusion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiments/TargetRelativeExperimentSuperiority.incomparable_experiments_have_opposite_target_advantages`
- Dependency: [D5/S3/ConceptDynamics/Refinement/RefinementReflexivity](../Refinement/RefinementReflexivity.md)
