# Capture Mass And The Infinite Relation Bridge Failure

## Abstract

Capture mass is submodular; the CAS bridge fails on infinite residual relations.

**Theorem 1.1 (Residual-intersection capture is submodular for every capture weight).**

$$\forall Edge, Definition: Type,\ nu: \operatorname{CaptureWeight}\left(Edge\right), residual: \operatorname{Set}\left(Edge\right), cut: Definition \to \operatorname{Set}\left(Edge\right), A, B: \operatorname{Set}\left(Definition\right),\ \operatorname{mass}\left(nu, \operatorname{apply}\left(captured, \operatorname{union}\left(A, B\right)\right)\right) + \operatorname{mass}\left(nu, \operatorname{apply}\left(captured, \operatorname{intersection}\left(A, B\right)\right)\right) \leq \operatorname{mass}\left(nu, \operatorname{apply}\left(captured, A\right)\right) + \operatorname{mass}\left(nu, \operatorname{apply}\left(captured, B\right)\right),\quad \text{where} \operatorname{apply}\left(captured, S\right) = \operatorname{intersection}\left(residual, \operatorname{iUnion}\left(definition \in S, \operatorname{apply}\left(cut, definition\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionCapture/MeasureCapture.capture_weight_submodular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula is equal in strength to capture_weight_submodular. It is an adjacent capture-mass lemma, not source clause six and not a conjunct of directly_provable_laws. Edge and Definition are the two Lean types; CaptureWeight and Set are the corresponding type constructors; and nu, residual, cut, A, and B are the theorem's explicit arguments.

The displayed name captured is exactly the theorem-local function S => residual intersection iUnion definition in S, cut definition. Formula calls named apply are ordinary Lean function application; union, intersection, and iUnion are respectively Set union, Set intersection, and the bounded iterated union in that local definition. No displayed name introduces an extra predicate or hypothesis.

CaptureWeight has ENNReal-valued mass and exactly one law: mass_union_add_lower_le. ENNReal retains infinite values, while the law says that a lower set inside the intersection may replace that intersection in the union-plus-intersection inequality. The public theorem identifies capture of A union B with the union of the two capture sets and includes capture of A intersection B in their intersection, then applies that law once.

The compiled constructors countingCaptureWeight, nonadditiveCoverageCaptureWeight, and measureCaptureWeight realize count, weight, and measure examples for this adjacent lemma. Their masses are respectively unrestricted Set.encard embedded in ENNReal, a nonadditive nonempty-set coverage weight, and the native values of an arbitrary Mathlib measure. No Finite or IsFiniteMeasure instance is required. The separate theorem measure_capture_submodular states and proves the complete arbitrary-measure specialization, including infinite values. The theorem infinite_counting_cas_bridge_fails separately proves that CAS's F(S) = M(empty) - M(S) cannot equal captured mass for unrestricted infinite counting. This refutes only that infinite-value bridge; it does not refute captured-mass submodularity itself. Its state space is Nat times Bool; its residual is the canonical defectRelation of a constant readout against the identity target; and its single cut is that residual intersected with the complement of the Prod.snd kernel. The residual, remaining relation, and captured cut are symmetric and diagonal-free where applicable. Both remaining masses are infinity, so F is zero, while the captured count is infinity.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionCapture/MeasureCapture.capture_weight_submodular`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/ResidualJoinLaw](../DefinitionEscape/ResidualJoinLaw.md)
