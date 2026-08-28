# Graph, Mechanism, and Law Separation

## Abstract

A fixed graph does not determine its mechanism, and an observational law does not determine its graph.

**Theorem 1.1 (One graph supports distinct mechanisms).**

$$direction\left(MIdentity\right) = direction\left(MFlip\right) \land child\left(MIdentity\right) \ne child\left(MFlip\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/GraphMechanismLawSeparation.same_graph_supports_distinct_mechanisms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both witnesses use the existing X-causes-Y direction and the identity root. Their child mechanisms are identity and Boolean negation. At false the outputs are false and true, proving that the mechanisms differ while the encoded DAG remains fixed.

This is a concrete two-node witness, not a general SCM framework. On an empty carrier functions are unique; on one edgeless node, different constant mechanisms still exist.

**Theorem 1.2 (Opposite graphs share one observational law).**

$$direction\left(MXY\right) \ne direction\left(MYX\right) \land observationalLaw\left(MXY\right) = observationalLaw\left(MYX\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/GraphMechanismLawSeparation.opposite_graphs_same_observational_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reused X-causes-Y and Y-causes-X constructors are unequal causal directions. With identity root and child mechanisms, both map each fair Boolean noise value u to the same observed pair (u,u), so their PMF pushforwards are equal.

FPOD 268.1 instead concerns crosswise recombination of mechanism readouts. It provides neither distinct DAGs nor equality of PMFs and therefore cannot imply this graph-law witness. No prime parameter or primality fact is used.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/GraphMechanismLawSeparation.opposite_graphs_same_observational_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/GraphMechanismLawSeparation.same_graph_supports_distinct_mechanisms`
- Dependency: [D5/S3/ConceptDynamics/Interventions/ObservationInterventionSeparation](../../ConceptDynamics/Interventions/ObservationInterventionSeparation.md)
