# Two Faced Privilege

## Abstract

Deficit integrality holds on two faces and does not transfer to three.

On the quadratic tower the deficit read on the expanding face equals the one read on the contracting face, and it is an integer. The reason is structural: those two faces are the entire conjugate set, so the irrational parts cancel when they are subtracted.

On the cubic tower that cancellation is unavailable. Splitting off the expanding root leaves a pair whose sum is one minus the base, and that number is irrational. Integrality of the deficit is therefore a privilege of having exactly two faces, which is what the source claims and what this conjunction states.

Both halves were already proved and neither is restated. What did not exist was any statement putting them together, so a claim whose two halves were green had no formal counterpart. Building the cubic deficit itself would require an integer-indexed naming layer that does not exist; the contrast needs none of it.

**Theorem 1.1 (Integrality is a two-faced privilege).**

$$\left(\forall v1 \in N, v2 \in N,\; \operatorname{deficit}\left(\mathit{v1}, \mathit{v2}\right) = \operatorname{deficitContraction}\left(\mathit{v1}, \mathit{v2}\right)\right) \land \operatorname{Irrational}\left(1 - \mathit{tribonacciConstant}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Irrationality/TwoFacedPrivilege.integrality_is_a_two_faced_privilege` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed left conjunct is the agreement of the two faces, which is the mechanism; the integrality it yields is carried alongside it in the theorem. The right conjunct is the cubic obstruction.

## References

- Truth anchor: `D5/S3/Constants/Irrationality/TwoFacedPrivilege.integrality_is_a_two_faced_privilege`
- Dependency: [D5/S1/Deficit/DeficitInteger](../../../S1/Deficit/DeficitInteger.md)
- Dependency: [D5/S3/Constants/Irrationality/CubicConjugateTrace](CubicConjugateTrace.md)
