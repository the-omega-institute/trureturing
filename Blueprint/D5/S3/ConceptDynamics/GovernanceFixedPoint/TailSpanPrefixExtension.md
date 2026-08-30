# Tail Span Prefix Extension

## Abstract

A tail span preserves a document prefix extension when its start lies in the old document.

**Theorem 1.1 (Tail spans preserve prefix extension).**

$$\begin{aligned}\forall Byte: \operatorname{Type},\\\forall oldDocument, newDocument: List(Byte),\\\forall start: Nat,\\PrefixExtension(oldDocument, newDocument) \land start \le oldDocument.length \Rightarrow \\PrefixExtension(TailBytes(oldDocument, start), TailBytes(newDocument, start)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GovernanceFixedPoint/TailSpanPrefixExtension.tail_span_prefix_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A source suffix remains after dropping any offset contained in the old document.

Thus the old tail is still an exact prefix of the extended document's tail, with the original suffix as witness.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/TailSpanPrefixExtension.tail_span_prefix_extension`
- Dependency: [D5/S3/ConceptDynamics/GovernanceFixedPoint/Core](Core.md)
