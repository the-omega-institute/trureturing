# History Carrier

## Abstract

Finite marker and event histories preserve the source append direction and low-level encoding.

Marker histories form the free monoid on exactly two constructors. Because source expressions extend at the left edge, source append is represented by reversed free-monoid multiplication; its recursive equation and both unit laws follow definitionally from this orientation.

Events carry source history, opcode, input code, and output marker. Event histories embed into marker histories with the literal low-level code `0 -> 00`, `1 -> 01`, and separator `11`; the bridge preserves appending one generated event.

**Theorem 1.1 (Splice is associative with the empty history as two-sided unit).**

$$(\forall a, b, c\in \operatorname{MarkerHistory}, \operatorname{splice}(\operatorname{splice}(a, b), c)=\operatorname{splice}(a, \operatorname{splice}(b, c))) \land (\forall h\in \operatorname{MarkerHistory}, \operatorname{splice}(1, h)=h) \land (\forall h\in \operatorname{MarkerHistory}, \operatorname{splice}(h, 1)=h)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/HistoryCarrier.marker_splice_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three conjuncts are the atomic acceptance theorem for the marker carrier: splice is associative, and the empty history is a unit on the left and on the right. All three follow definitionally from representing source append as reversed free-monoid multiplication, so the proof is the single rewrite that unfolds splice and applies monoid associativity. The prime-power Godel numbering and its decoder round-trip are explicitly outside this producer cluster and tracked separately.

## References

- Truth anchor: `D5/S0/History/HistoryCarrier.marker_splice_laws`
