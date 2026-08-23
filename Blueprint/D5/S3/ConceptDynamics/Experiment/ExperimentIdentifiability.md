# Experiment Identifiability

## Abstract

A target is identifiable exactly when it factors through the joint experiment readout, equivalently when experiment-indistinguishability implies equal targets.

**Theorem 1.1 (Target identifiability has three equivalent forms).**

$$\begin{aligned}\forall S, X, Y: \operatorname{Type}, R: S \to \operatorname{Type},\\e: \forall u: S, X \to R_{u}, t: X \to Y,\\\operatorname{Nonempty}\left(X\right) \Rightarrow \operatorname{TFAE}[\exists f: \prod_{u: S}R_{u} \to Y, t = f \circ \operatorname{jointReadout}\left(e\right),\\\operatorname{jointKernel}\left(e\right) \subseteq \operatorname{targetKernel}\left(t\right),\\\forall x, y: X, (\forall u: S, \operatorname{e}\left(u, x\right) = \operatorname{e}\left(u, y\right)) \Rightarrow \operatorname{t}\left(x\right) = \operatorname{t}\left(y\right)].\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/ExperimentIdentifiability.identifiable_tfae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An experiment family records one response for every index, and its joint readout collects those responses into a dependent tuple. The target is identifiable when a single factor map recovers the target value from that complete response tuple.

The joint kernel contains exactly the state pairs that every experiment fails to distinguish. Containment in the target kernel says that each such pair has the same target value, which is the pointwise fiber-constancy condition in the third clause.

On a nonempty state space, the answerability criterion turns fiber constancy into a factor through the joint readout. Membership in the joint kernel is componentwise equality across all experiment indices, completing the equivalence with kernel containment.

The Boolean examples separate the boundary: an identity experiment identifies the identity target, while a constant experiment fails factorization, kernel containment, and fiber constancy.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/ExperimentIdentifiability.identifiable_tfae`
- Dependency: [D5/S0/Rewriting/Quotients/AnswerabilityCriterion](../../../S0/Rewriting/Quotients/AnswerabilityCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
