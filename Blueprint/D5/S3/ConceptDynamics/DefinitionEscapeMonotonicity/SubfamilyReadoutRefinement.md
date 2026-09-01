# Subfamily Readout Refinement

## Abstract

Every dependent subfamily readout factors through the complete family readout.

**Theorem 1.1 (The complete family refines every subfamily readout).**

$$\begin{aligned}\forall I, X: \operatorname{Type},\\V: I \to \operatorname{Type}, q: \forall i: I, X \to \operatorname{V}\left(i\right),\\J \subseteq I, \operatorname{Refines}\left(\operatorname{jointReadout}\left(\operatorname{restrict}\left(q, J\right)\right), \operatorname{jointReadout}\left(q\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/SubfamilyReadoutRefinement.subfamily_readout_refined_by_full_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be a dependent family of readouts on X and let J be any subset of its index type. The selected observation is the imported jointReadout instantiated on the subtype J.

A complete output tuple restricts to J by discarding all coordinates outside the subfamily. This coordinate restriction factors the subfamily readout through the complete readout.

Here Refines takes the coarser readout first and the finer readout second. Thus the theorem states Refines of the J-readout by the full-family readout, including empty and infinite families.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/SubfamilyReadoutRefinement.subfamily_readout_refined_by_full_family`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
