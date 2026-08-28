# Common-Control Approval Collapse

## Abstract

Joint approvals and their final judgment remain below a common control source.

**Theorem 1.1 (A shared control source bounds both joint approvals and final authorization).**

$$\begin{aligned}\forall I, X, Source, Judgment: \operatorname{Type}, B: I \to \operatorname{Type},\\A: \forall i: I, X \to B_{i},\\S: X \to Source, f: {\forall i: I, B_{i}} \to Judgment,\\(\forall i: I, \operatorname{Refines}(A\left(i\right), S)) \Rightarrow\\\operatorname{Refines}(\operatorname{jointReadout}(A), S) \land\\\exists g: Source \to Judgment, f \circ \operatorname{jointReadout}(A) = g \circ S.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InstitutionalCapture/CommonControlApprovalCollapse.common_control_source_approval_collapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each approval node is an independent formal coordinate, but every node is assumed to factor through the same source readout.

The canonical dependent joint readout therefore factors through that source. Composing its factor with the final authorization map gives an explicit source-to-judgment factor g.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InstitutionalCapture/CommonControlApprovalCollapse.common_control_source_approval_collapse`
- Dependency: [D5/S3/ConceptDynamics/Communication/IndexedCommonSourceUpperBound](../Communication/IndexedCommonSourceUpperBound.md)
