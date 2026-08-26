# Proof Topology Core

## Abstract

Frozen dependency APIs support finite bases, order simplices, and certificate gluing.

**Theorem 1.1 (Finite support defines a Scott-open release property).**

$$\begin{gathered}\forall V: \operatorname{Type}, seed: \operatorname{Finset}\left(V\right), [\operatorname{DecidableEq}\left(V\right)] \Rightarrow\\{}(\operatorname{PowersetScottOpen}\left(\{release: \operatorname{Set}\left(V\right) \mid seed \subseteq release\}\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Topology/ProofTopologyCore.finiteSupport_scottOpen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite seed of vertices. The release property consists of exactly those vertex sets that contain every seed vertex.

This property is upward closed. If a directed union contains the seed, finiteness places the whole seed inside one member of the directed family.

Thus the property is inaccessible by directed unions and is Scott-open in the displayed powerset order. The statement retains the DecidableEq instance from the Lean signature.

**Theorem 1.2 (Covered realizable local data has a unique gluing).**

$$\begin{gathered}\forall Index: \operatorname{Type},\\{}system: \operatorname{CertificateSystem}\left(Index\right),\\{}localFamily: (\forall index: Index, \operatorname{Local}\left(system, index\right)),\\{}(\operatorname{Covers}\left(system\right) \land \operatorname{Realizable}\left(system, localFamily\right)) \Rightarrow\\{}(\exists! global: \operatorname{Global}\left(system\right), \forall index: Index, \operatorname{restrict}\left(system, index, global\right) = localFamily(index)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Topology/ProofTopologyCore.unique_gluing_of_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A certificate system supplies a global type, an indexed local type, and one restriction map for each index.

Coverage means that the complete family of restrictions is injective. Realizability supplies a global certificate whose restrictions equal the prescribed local family.

Injectivity makes that realizing certificate unique. The theorem does not assert that an arbitrary local family is realizable.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Topology/ProofTopologyCore.finiteSupport_scottOpen`
- Truth anchor: `D5/S3/ConceptDynamics/Topology/ProofTopologyCore.unique_gluing_of_cover`
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/AlexandrovDependencyTopology](../DependencyTopology/AlexandrovDependencyTopology.md)
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/AlexandrovMonotoneContinuity](../DependencyTopology/AlexandrovMonotoneContinuity.md)
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/AxiomClosureMonotonicity](../DependencyTopology/AxiomClosureMonotonicity.md)
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder](../DependencyTopology/DependencyReachabilityOrder.md)
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/DepthClosedFiltration](../DependencyTopology/DepthClosedFiltration.md)
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/DominatorCut](../DependencyTopology/DominatorCut.md)
