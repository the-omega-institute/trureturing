# Typed Trust Composition

## Abstract

Typed trust composes along one report chain, is characterized by target constancy on report fibers, and can fail when intermediate scopes do not match.

**Definition 1.1 (A report interface aligns with a target).**

$$\forall X, R, T: \operatorname{Type},\\{}qR: X \to R, qT: X \to T,\\{}\operatorname{InterfacesAlign}\left(qR, qT\right) \iff \forall x, y: X, {qR\left(x\right) = qR\left(y\right)} \Rightarrow qT\left(x\right) = qT\left(y\right).$$

*Formalization.* `D5/S3/ConceptDynamics/Trust/TypedTrustComposition.InterfacesAlign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A report interface aligns with a target exactly when the report never identifies two states that the target distinguishes. Equivalently, the target is constant on every fiber of the report.

**Theorem 1.2 (Typed trust composes exactly through aligned interfaces).**

$$\begin{gathered}{\forall X, C, B, T: \operatorname{Type},\\{}qC: X \to C, qB: X \to B, qT: X \to T,\\{}{\operatorname{Refines}\left(qB, qC\right) \land \operatorname{Refines}\left(qT, qB\right)} \Rightarrow \operatorname{Refines}\left(qT, qC\right)} \land\\{}{\forall X, R, T: \operatorname{Type},\\{}qR: X \to R, qT: X \to T,\\{}\operatorname{Nonempty}\left(T\right) \Rightarrow {\operatorname{Refines}\left(qT, qR\right) \iff \operatorname{InterfacesAlign}\left(qR, qT\right)}} \land\\{}\exists qC: Bool \times Bool \to Bool,\\{}qB: Bool \times Bool \to Bool \times Bool,\\{}scope, target: Bool \times Bool \to Bool,\\{}\operatorname{Refines}\left(target, qB\right) \land \operatorname{Refines}\left(scope, qC\right) \land \neg \operatorname{Refines}\left(target, qC\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Trust/TypedTrustComposition.typed_trust_composes_iff_interfaces_align` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Refinement is transitive along a single typed report chain. If the intermediate report factors through the outer report and the target factors through the intermediate report, then the target factors through the outer report.

For a nonempty target codomain, a target factors through a report exactly when it is constant on the report's fibers. The forward direction follows from applying the factor map; the reverse direction is the standard factorization-through-fibers criterion.

The Boolean-pair witness takes the outer report to be the first projection, the richer report to be the identity, the intermediate scope to be the first projection, and the target to be the second projection. The target factors through the identity and the scope factors through the outer report, but the target does not factor through that report.

The failure does not contradict transitivity: the two available refinement premises pass through different intermediate readouts. The states (false, false) and (false, true) have the same outer report while their target values differ, exposing the missing target-relevant distinction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Trust/TypedTrustComposition.InterfacesAlign`
- Truth anchor: `D5/S3/ConceptDynamics/Trust/TypedTrustComposition.typed_trust_composes_iff_interfaces_align`
- Dependency: [D5/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionObstruction](../NormativeStructure/HistorySensitiveOutcomeReductionObstruction.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/RefinementTransitivity](../Refinement/RefinementTransitivity.md)
