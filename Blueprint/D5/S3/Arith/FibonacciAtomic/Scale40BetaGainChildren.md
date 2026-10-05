# Beta Resources in an Actual Leaf History

## Abstract

Actual leaf reports fix beta frontiers in literal Fibonacci blocks.

**Definition 1.1 (Actual beta frontier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Scale40BetaGainChildren.betaLeaves`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Scale40BetaGainChildren.betaLeaves` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The beta frontier filters the existing actual leaf-address set by the original beta reply. Addresses are finite left/right words, including the empty root.

**Definition 1.2 (Fixed beta union).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Scale40BetaGainChildren.psi`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Scale40BetaGainChildren.psi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each block decoded from an actual leaf report, prefix its actual beta frontier by its block root. Take the finite union of these addresses. A contributes LL and R; C contributes LLL, LR and RL. Branch and absent reports contribute no blocks, and repeated addresses are counted once.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Scale40BetaGainChildren.betaLeaves`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Scale40BetaGainChildren.psi`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualStrictHistoryCapacity](ActualStrictHistoryCapacity.md)
