# Canonical Passive Joint Boundary

## Abstract

Adaptivity lowers cost but cannot cross the canonical passive joint boundary.

**Theorem 1.1 (Adaptivity cannot cross the complete passive boundary).**

$$\begin{aligned}\forall U, X, Y: \operatorname{Type}, R: U \to \operatorname{Type},\\q: \forall u: U, X \to R_{u}, T: X \to Y,\\\neg\operatorname{Refines}\left(T, \operatorname{jointReadout}\left(q\right)\right) \implies \\D_{ad} < D_{stat} \land \neg\exists pi: \operatorname{PassiveProtocol}\left(U, R\right), \operatorname{Refines}\left(T, \operatorname{runPassiveProtocol}\left(q, pi\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentDesign/CanonicalPassiveJointBoundary.canonical_adaptive_cost_reduction_and_passive_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The modular four-state witness has adaptive depth strictly below its minimum exact fixed-suite depth, so adaptive selection can reduce experiment cost.

For an arbitrary passive experiment family, every deterministic adaptive transcript factors through the canonical joint readout. A target that does not refine that readout therefore cannot refine any such transcript.

Crossing this boundary requires leaving the quantified class through new experiments, a changed object, intervention, expanded observations, or an added domain premise. The proof directly applies the frozen family theorem and redeclares no protocol or readout primitive.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentDesign/CanonicalPassiveJointBoundary.canonical_adaptive_cost_reduction_and_passive_boundary`
- Dependency: [D5/S3/ConceptDynamics/ExperimentBoundary/PassiveJointBoundaryObstruction](../ExperimentBoundary/PassiveJointBoundaryObstruction.md)
