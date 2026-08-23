# Golden Model-Set Self-Similarity

## Abstract

The golden conjugate window has unit volume, and the golden beta range splits into two disjoint self-similar branches.

**Lemma 1.1 (The golden conjugate window has unit volume).**

$$\operatorname{volume}\left(\mathit{goldenWindow}\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/GoldenModelSetSelfSimilar.golden_window_volume` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The golden window is the closed real interval from minus the inverse square of the golden ratio to the inverse golden ratio. Its Lebesgue volume is the difference of these endpoints, namely the sum of the two inverse powers.

The inverse-golden recurrence identifies that sum with one, so the closed conjugate window has length and volume exactly one.

**Theorem 1.2 (The golden beta range is a disjoint self-similar union).**

$$\mathit{goldenModelSet} = \operatorname{union}\left(\mathit{phiBranch}, \mathit{phiSquaredBranch}\right) \land \operatorname{Disjoint}\left(\mathit{phiBranch}, \mathit{phiSquaredBranch}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/GoldenModelSetSelfSimilar.golden_model_set_self_similar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write B for the range of the exact GoldenInt-valued beta reading. Every canonical digit string belongs to exactly one of two branches: a zero least digit exposes a one-place shift and contributes phi B, while a one least digit forces the next digit to vanish and contributes phi squared plus phi squared B.

Conversely, shifting a canonical string by one place and prefixing a canonical one-zero pair both preserve admissibility, so both branches lie in B. Their least digits differ, and uniqueness of canonical golden digits makes the two images disjoint. Thus B is exactly their disjoint union.

## References

- Truth anchor: `D5/S1/Deficit/GoldenModelSetSelfSimilar.golden_model_set_self_similar`
- Truth anchor: `D5/S1/Deficit/GoldenModelSetSelfSimilar.golden_window_volume`
- Dependency: [D5/S1/Deficit/DoubleFaceLength](DoubleFaceLength.md)
- Dependency: [D5/S1/Digit/Admissibility/LeastDigitDecomposition](../Digit/Admissibility/LeastDigitDecomposition.md)
