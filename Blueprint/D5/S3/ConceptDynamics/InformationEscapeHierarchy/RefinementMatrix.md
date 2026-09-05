# Executable Refinement Matrix

## Abstract

An ordered state enumeration makes every false refinement cell executable, deterministic, and proof-backed.

**Definition 1.1 (Kernel comparison cases).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.KernelComparison`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.KernelComparison` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four cases distinguish equality, either strict direction, and incomparability.

**Definition 1.2 (Classified kernel comparison).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.kernelComparison`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.kernelComparison` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two decidable inclusion cells determine the four-way classification.

**Definition 1.3 (Executable refinement witness).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.refinementWitness`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.refinementWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Spec spelling refinementWitness?. The search uses states.product states, visiting the outer-left state first and the inner-right state second.

**Theorem 1.4 (The selector uses the documented pair order).**

$$\operatorname{refinementWitness}(C, E, i, j) = \operatorname{find}(\operatorname{product}(\operatorname{states}(E), \operatorname{states}(E)), \operatorname{separatesRefinement}(C, i, j)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.refinementWitness_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from executable ordered search and Boolean agreement reflection.

**Theorem 1.5 (No witness exactly means refinement).**

$$\operatorname{refinementWitness}(C, E, i, j) = \operatorname{none}() \Leftrightarrow \operatorname{KernelRefines}(C, i, j).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.refinementWitness_eq_none_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from executable ordered search and Boolean agreement reflection.

**Theorem 1.6 (A returned refinement witness is sound).**

$$\operatorname{refinementWitness}(C, E, i, j) = \operatorname{some}(p) \Rightarrow \left(\operatorname{agrees}(\operatorname{primitives}(\operatorname{theoremAt}(C, i)), \operatorname{fst}(p), \operatorname{snd}(p)) \land \neg\operatorname{agrees}(\operatorname{primitives}(\operatorname{theoremAt}(C, j)), \operatorname{fst}(p), \operatorname{snd}(p))\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.refinementWitness_eq_some_implies` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from executable ordered search and Boolean agreement reflection.

**Theorem 1.7 (A false cell has a deterministic witness).**

$$(\exists p, \operatorname{refinementWitness}(C, E, i, j) = \operatorname{some}(p)) \Leftrightarrow \neg\operatorname{KernelRefines}(C, i, j).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.refinementWitness_exists_iff_not_kernelRefines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from executable ordered search and Boolean agreement reflection.

**Theorem 1.8 (Kernel comparison carries all inclusion and witness payloads).**

$$(\operatorname{kernelComparison}(C, i, j) = equal \Leftrightarrow \operatorname{KernelRefines}(C, i, j) \land \operatorname{KernelRefines}(C, j, i)) \land \left((\operatorname{kernelComparison}(C, i, j) = strictlyFiner \Leftrightarrow \operatorname{KernelRefines}(C, i, j) \land (\exists p, \operatorname{refinementWitness}(C, E, j, i) = \operatorname{some}(p))) \land \left((\operatorname{kernelComparison}(C, i, j) = strictlyCoarser \Leftrightarrow (\exists p, \operatorname{refinementWitness}(C, E, i, j) = \operatorname{some}(p)) \land \operatorname{KernelRefines}(C, j, i)) \land (\operatorname{kernelComparison}(C, i, j) = incomparable \Leftrightarrow (\exists p, \operatorname{refinementWitness}(C, E, i, j) = \operatorname{some}(p)) \land (\exists p, \operatorname{refinementWitness}(C, E, j, i) = \operatorname{some}(p)))\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.kernelComparison_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from executable ordered search and Boolean agreement reflection.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.KernelComparison`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.kernelComparison`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.kernelComparison_spec`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.refinementWitness`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.refinementWitness_eq_none_iff`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.refinementWitness_eq_some_implies`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.refinementWitness_exists_iff_not_kernelRefines`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.refinementWitness_order`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeCounting/Fused](../InformationEscapeCounting/Fused.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws](AnalysisLaws.md)
