# The Golden Carry Deficit Bridge

## Abstract

Internal golden carries preserve both faces, and the common signed integer deficit vanishes under difference decoding.

**Theorem 1.1 (The golden carry deficit bridge).**

$$\forall k, v_1, v_2\in \mathbb{N},\quad[\forall x\in \{\varphi, \psi\},\quad(x^{k+1}+x^{k+2}=x^{k+3} \land 2x^{k+2}=x^{k+3}+x^k)] \land [c(v_1, v_2)=c'(v_1, v_2) \land (\exists z\in \mathbb{Z}, c(v_1, v_2)=z) \land c(v_1, v_2)=\operatorname{carrySignedCount}(\operatorname{toRaw}(Z(v_1))+\operatorname{toRaw}(Z(v_2)))] \land \frac{c(v_1, v_2)-c'(v_1, v_2)}{\sqrt{5}}=0$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Carry/GoldenCarryDeficitBridge.golden_carry_deficit_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural carry index and each pair of natural operands, the adjacent and higher doubling rewrites preserve both the expanding golden face phi and its conjugate face psi. The normalization deficit is equal on those two faces, is a rational integer, and equals the signed count accumulated from bottom carries: the lowest rule contributes +1, the second contributes -1, and internal carries contribute zero.

The proof directly packages the frozen two-face theorem carry_rewrite_face_invariant with the frozen integer certificate deficit_integer. Since the two deficits are equal, their difference divided by sqrt(5) is zero, making the common integer account invisible to the difference decoder. No carry arithmetic or normalization machinery is reproved in this bridge.

## References

- Truth anchor: `D5/S1/Deficit/Carry/GoldenCarryDeficitBridge.golden_carry_deficit_bridge`
- Dependency: [D5/S1/Deficit/DeficitInteger](../DeficitInteger.md)
- Dependency: [D5/S1/Deficit/GoldenCarryLedger](../GoldenCarryLedger.md)
