# Protected Coordinate Dependent Extensionality

## Abstract

All seven dependent protected-coordinate projections jointly determine the frozen record.

**Theorem 1.1 (Dependent projection agreement characterizes coordinate equality).**

$$\begin{gathered}\forall TargetChain, Domain, Epsilon, Condition, Comparator, Baseline, WeightSpec: \operatorname{Type},\\{}oldCoordinates, newCoordinates: \operatorname{ProtectedCoordinates}\left(TargetChain, Domain, Epsilon, Condition, Comparator, Baseline, WeightSpec\right),\\{}oldCoordinates = newCoordinates \Leftrightarrow\\{}\forall tag: \operatorname{ProtectedCoordinateTag}, \operatorname{protectedCoordinateAt}\left(oldCoordinates, tag\right) = \operatorname{protectedCoordinateAt}\left(newCoordinates, tag\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeRegrade/ProtectedCoordinateExtensionality.protected_coordinate_dependent_extensionality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ProtectedCoordinateTag has exactly the seven labels targetChain, domain, epsilon, conditions, comparator, baseline, and weightSpec. The dependent projection returns each field in its own type.

The reverse implication specializes the universal equality at every label and applies structure extensionality. It assumes no decidable equality for any field type.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeRegrade/ProtectedCoordinateExtensionality.protected_coordinate_dependent_extensionality`
- Dependency: [D5/S3/ConceptDynamics/Governance/TargetLaunderingCriterion](../Governance/TargetLaunderingCriterion.md)
