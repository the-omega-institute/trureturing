# Continuous Hard Classification Obstruction

## Abstract

A nonconstant discrete classifier continuously factored through a representation forces a topological or continuity obstruction.

**Theorem 1.1 (Nonconstant hard classification requires a structural obstruction).**

$$\begin{gathered}\forall X, B, Y: \operatorname{Type},\\{}C: X \to B, f: B \to Y, T: X \to Y,\\{}(T = f \circ C \land \operatorname{Continuous}(C)) \Rightarrow\\{}((\operatorname{Continuous}(f) \land \operatorname{IsConnected}(\operatorname{range}(C)) \land \operatorname{DiscreteTopology}(Y)) \Rightarrow (\forall x, xPrime: X, T(x) = T(xPrime))) \land\\{}((\exists x, xPrime: X, T(x) \neq T(xPrime)) \Rightarrow (\neg \operatorname{IsConnected}(\operatorname{range}(C)) \lor \neg \operatorname{Continuous}(f) \lor \neg \operatorname{DiscreteTopology}(Y) \lor \neg \operatorname{IsConnected}(X))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Topology/ContinuousHardClassificationObstruction.continuous_hard_classification_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The classifier is publicly required to factor as a decoder after a continuous representation. If the realized representation image is connected, the decoder is continuous, and the output topology is discrete, the decoder restricted to that image is constant by the imported connected-to-discrete rigidity theorem.

Composing that constant restriction with the representation makes the classifier constant on the entire object domain. This proves the first clause directly on the factorized classifier rather than on an unrelated special case.

For the contrapositive clause, a connected object domain has connected image under the continuous representation. Therefore a witnessed nonconstant classifier forces at least one listed obstruction: the realized representation is disconnected, the decoder is discontinuous, the output is nondiscrete, or the object domain is disconnected.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Topology/ContinuousHardClassificationObstruction.continuous_hard_classification_obstruction`
- Dependency: [D5/S1/Solenoid/Connectivity/ContinuousDiscreteRigidity](../../../S1/Solenoid/Connectivity/ContinuousDiscreteRigidity.md)
