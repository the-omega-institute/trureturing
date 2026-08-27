# Joint Lossless Communication Criterion

## Abstract

Joint communication is lossless on realized behavior records, while correlated coordinates can compensate for a lossy component.

**Theorem 1.1 (Losslessness is injectivity on realized joint behavior).**

$$\begin{gathered}\forall I, X: Type,\\{}B: I \to Type, C: I \to Type,\\{}behavior: \pi i: I, X \to B(i), compress: \pi i: I, B(i) \to C(i),\\{}(\operatorname{ker}\left(messageConcept(jointReadout(behavior), \lambda record, i \mapsto compress(i)(record(i)))\right) = \operatorname{ker}\left(jointReadout(behavior)\right) \iff \operatorname{InjOn}\left(\lambda record, i \mapsto compress(i)(record(i)), \operatorname{range}\left(jointReadout(behavior)\right)\right)) \land\\{}((\forall i\in I, \operatorname{InjOn}\left(compress(i), \operatorname{range}\left(behavior(i)\right)\right)) \Rightarrow \operatorname{ker}\left(messageConcept(jointReadout(behavior), \lambda record, i \mapsto compress(i)(record(i)))\right) = \operatorname{ker}\left(jointReadout(behavior)\right)) \land\\{}(\exists behaviorC: \pi i: Bool, Bool \to Bool, compressC: \pi i: Bool, Bool \to Bool,\\{}\operatorname{ker}\left(messageConcept(jointReadout(behaviorC), \lambda record, i \mapsto compressC(i)(record(i)))\right) = \operatorname{ker}\left(jointReadout(behaviorC)\right) \land \neg(\forall i\in Bool, \operatorname{InjOn}\left(compressC(i), \operatorname{range}\left(behaviorC(i)\right)\right))) \land\\{}(\forall Y, W: Type, R1: \operatorname{Setoid}\left(Y\right), R2: \operatorname{Setoid}\left(Y\right),\\{}r: Y \to W, p1: W \to \operatorname{Quotient}\left(R1\right), p2: W \to \operatorname{Quotient}\left(R2\right),\\{}\operatorname{Surjective}\left(r\right) \land \operatorname{Surjective}\left(p1\right) \land \operatorname{Surjective}\left(p2\right) \land\\{}(\forall y\in Y, p1(r(y)) = \operatorname{class}\left(y, R1\right)) \land\\{}(\forall y\in Y, p2(r(y)) = \operatorname{class}\left(y, R2\right)) \Rightarrow\\{}\exists! h: W \to \operatorname{Quotient}\left(\operatorname{inf}\left(R1, R2\right)\right), \operatorname{Surjective}\left(h\right) \land \forall y\in Y, h(r(y)) = \operatorname{class}\left(y, \operatorname{inf}\left(R1, R2\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Communication/JointLosslessCommunicationCriterion.joint_lossless_communication_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full behavior is the canonical dependent jointReadout of all coordinate behaviors. Its message applies each coordinate encoder to the corresponding realized component.

Equality of the message and behavior kernels is equivalent to injectivity of that coordinatewise encoder on the actual joint behavior image. Injectivity outside the realized image is irrelevant.

Coordinatewise injectivity on every realized marginal image is a sufficient condition. It is not necessary: two correlated Boolean coordinates remain jointly lossless when the false-index encoder is constant and the true-index encoder preserves the shared bit.

The final public clause imports the canonical least-common-refinement result: a compatible surjective implementation covering both quotients has a unique surjective descent to their intersection quotient.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Communication/JointLosslessCommunicationCriterion.joint_lossless_communication_criterion`
- Dependency: [D5/S3/ConceptDynamics/Coding/LosslessEncodingCriterion](../Coding/LosslessEncodingCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
- Dependency: [D5/S3/ObserverMemory/Fusion/LeastCommonRefinement](../../ObserverMemory/Fusion/LeastCommonRefinement.md)
