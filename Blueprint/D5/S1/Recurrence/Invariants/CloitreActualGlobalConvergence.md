# Actual Cloitre Global Convergence

## Abstract

Under the complete Hyp21_1, golden convergence of the actual Cloitre sequence is equivalent to vanishing positive selected jumps.

**Definition 1.1 (Half-open Fibonacci block position).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualGlobalConvergence.position`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualGlobalConvergence.position` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let q(n) be the greatest Fibonacci index with F(q(n)) at most n. The position of n is (n-F(q(n)))/F(q(n)-1). For n at least eight this position lies in the unit interval. It is an analysis coordinate, independent of the actual iteration time.

**Theorem 1.2 (Positive jumps and the global golden limit).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualGlobalConvergence.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CloitreActualGlobalConvergence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural-valued upper envelope U satisfying the complete Hyp21_1, set alpha to the inverse golden ratio. Let beta be the limsup of C(N)/N over all natural roots, and kappa the limsup of max(g(N)-T(N,g(N)),0)/N, taking the signed difference before its positive part. Then beta is at most alpha plus the golden ratio times kappa. Moreover C(N)/N tends to alpha if and only if the positive selected-jump ratio tends to zero.

For the upper bound, choose the least block-position cluster among roots approaching the global limsup. The actual split recurrence and uniformly positive child weights force both child ratios to approach the same extremum. If the upper bound failed, the selected child's weight would be strictly below alpha, placing it in the preceding Fibonacci block and giving a smaller extremal position.

If the global value ratio converges, every point of the actual selected cycle has uniformly small value-ratio error. The inner map contracts normalized distance to alpha up to that error. Maximizing on the same finite cycle bounds the selector and its successor uniformly, so their positive jump vanishes. In the opposite direction the limsup bound and the golden floor lower envelope squeeze the value ratio to alpha. All finite source foundations remain conditional.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualGlobalConvergence.position`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualGlobalConvergence.result`
- Dependency: [D5/S1/Recurrence/Invariants/CloitreActualRightProfile](CloitreActualRightProfile.md)
