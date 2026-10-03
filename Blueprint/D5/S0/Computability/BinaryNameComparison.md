# Binary Name Comparison

## Abstract

Comparison of whole binary names includes length mismatch and paid restoration.

**Theorem 1.1 (Restored operands, empty backups and preserved caller frame).**

$$\forall a \in \operatorname{List}\left(\mathit{Bool}\right),\; \forall b \in \operatorname{List}\left(\mathit{Bool}\right),\; \forall output \in \operatorname{List}\left(\mathit{Bool}\right),\; \forall frame \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Nonempty}\left(\operatorname{EvalsToInTime}\left(\operatorname{step}\left(\mathit{compareMachine}\right), \operatorname{compareCfg}\left(\operatorname{some}\left(\mathit{compare}\right), (\mathit{none}, \mathit{none}, \mathit{true}), a, b, \mathit{nil}, \mathit{nil}, \mathit{output}, \mathit{frame}\right), \operatorname{some}\left(\operatorname{compareCfg}\left(\mathit{none}, (\mathit{none}, \mathit{none}, \mathit{true}), a, b, \mathit{nil}, \mathit{nil}, \operatorname{cons}\left(\operatorname{decide}\left(a = b\right), \mathit{output}\right), \mathit{frame}\right)\right), 2 \cdot \left(\operatorname{length}\left(a\right) + \operatorname{length}\left(b\right)\right) + 4\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryNameComparison.name_compare_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary Boolean words a and b, previous output and caller frame, the six-stack, four-label machine consumes both operands into backups, including unequal lengths. It restores each operand, empties both backups, pushes their whole-word equality flag onto the previous output and returns with its initial control. The caller frame is preserved literally.

The native transition bound is twice the sum of the operand lengths plus four. Only symbol comparisons occur; binary names are never expanded into unary numbers. This is a routine boundary with restored operands, rather than the clean haltList boundary of the complete converter.

## References

- Truth anchor: `D5/S0/Computability/BinaryNameComparison.name_compare_run`
