# Connected Discrete Naming Discontinuity

## Abstract

A connected space has no nonconstant continuous discrete naming map.

**Theorem 1.1 (Nonconstant discrete naming forces discontinuity).**

$$\begin{gathered}\forall X, N: \operatorname{Type},\\{}[\operatorname{TopologicalSpace}(X)], [\operatorname{ConnectedSpace}(X)],\\{}[\operatorname{TopologicalSpace}(N)], [\operatorname{DiscreteTopology}(N)],\\{}nu: X \to N,\\{}(\operatorname{Continuous}(nu) \Rightarrow\\{}\forall x, y: X, nu(x) = nu(y)) \land\\{}((\exists x, y: X, nu(x) \neq nu(y)) \Rightarrow \neg\operatorname{Continuous}(nu)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Topology/ConnectedDiscreteNamingDiscontinuity.connected_discrete_naming_discontinuity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be connected and N carry the discrete topology. Every continuous map from X to N has equal values at every pair of points.

The second public clause is the direct contrapositive: a pair of points with distinct names rules out continuity of the same naming map.

The proof applies the frozen connected-to-discrete rigidity owner and uses the resulting equality against the witnessed distinct values.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Topology/ConnectedDiscreteNamingDiscontinuity.connected_discrete_naming_discontinuity`
- Dependency: [D5/S1/Solenoid/Connectivity/ContinuousDiscreteRigidity](../../../S1/Solenoid/Connectivity/ContinuousDiscreteRigidity.md)
