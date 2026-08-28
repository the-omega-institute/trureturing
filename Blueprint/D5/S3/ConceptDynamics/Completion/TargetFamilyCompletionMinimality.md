# Minimal Target-Family Completion

## Abstract

Adjoining an entire target family is the coarsest jointly sufficient refinement.

**Theorem 1.1 (Target-family completion is coarsest).**

$$\begin{gathered}\forall X, I, Q: \operatorname{Type}, Y: I \to \operatorname{Type},\\{}q: X \to Q,\\{}T: \forall i: I, X \to Y(i),\\{}\operatorname{Refines}\left(q, \operatorname{conceptJoin}\left(q, \operatorname{jointTarget}\left(T\right)\right)\right) \land\\{}(\forall i: I, \operatorname{Refines}\left(T(i), \operatorname{conceptJoin}\left(q, \operatorname{jointTarget}\left(T\right)\right)\right)) \land\\{}\forall D: \operatorname{Type}, r: X \to D,\\{}\operatorname{Refines}\left(q, r\right) \land (\forall i: I, \operatorname{Refines}\left(T(i), r\right)) \Rightarrow\\{}\operatorname{Refines}\left(\operatorname{conceptJoin}\left(q, \operatorname{jointTarget}\left(T\right)\right), r\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/TargetFamilyCompletionMinimality.target_family_completion_is_coarsest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The completion is constructed canonically by joining the current interface with the dependent readout of every target value.

Projection to the first coordinate recovers the current interface. Projection to the joint-target coordinate followed by evaluation recovers every member of the target family.

Any interface that recovers both the current readout and every target receives the paired factor map from this completion. Thus the same construction covers factual, predictive, causal, sequential-effect, indexed-readout, strategy, and self-relevant target families.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Completion/TargetFamilyCompletionMinimality.target_family_completion_is_coarsest`
- Dependency: [D5/S3/ConceptDynamics/Refinement/MultiTargetMinimalSufficiency](../Refinement/MultiTargetMinimalSufficiency.md)
