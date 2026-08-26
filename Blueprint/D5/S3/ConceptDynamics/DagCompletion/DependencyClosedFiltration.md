# Dependency-Closed Filtration

## Abstract

Dependency-closed append-only filtrations order prerequisite birth no later than dependent birth.

**Theorem 1.1 (A prerequisite is born no later than its dependent).**

$$\begin{gathered}\forall edge: V \to V \to Prop, filtration: \operatorname{DependencyFiltration}\left(V, edge\right),\\{}dependentNode: \operatorname{PresentNode}\left(filtration\right), prerequisite: V,\\{}\operatorname{edge}\left(prerequisite, \operatorname{value}\left(dependentNode\right)\right) \Rightarrow\\{}\operatorname{birth}\left(filtration, \operatorname{prerequisiteNode}\left(filtration, prerequisite, dependentNode\right)\right) \leq \operatorname{birth}\left(filtration, dependentNode\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/DependencyClosedFiltration.prerequisite_birth_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Quantify a dependency-filtration structure and a present dependent node. If a vertex is a direct prerequisite of that node, closure of every stage makes the prerequisite present by the dependent's birth.

The conclusion compares canonical birth times with a non-strict inequality. Strictly earlier birth requires the separate strict-staging hypothesis and is not claimed here.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/DependencyClosedFiltration.prerequisite_birth_le`
- Dependency: [D5/S3/ConceptDynamics/DagSemantics/BirthStageFiltration](../DagSemantics/BirthStageFiltration.md)
- Dependency: [D5/S3/ConceptDynamics/DagSemantics/PrerequisiteClosure](../DagSemantics/PrerequisiteClosure.md)
