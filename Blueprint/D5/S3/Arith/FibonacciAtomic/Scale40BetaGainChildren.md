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

**Theorem 1.3 (Strict beta growth).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Scale40BetaGainChildren.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Scale40BetaGainChildren.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite family consist of pairwise nonconflicting actual third images, and retain the members matching every report in a finite history. Suppose an actual address strictly splits this survivor queue and has a nonempty alpha or beta leaf child. The old fixed beta union is contained in every surviving member's beta frontier. Adding the leaf report increases the fixed union by one, two or three addresses. The increase is one exactly when the report forces C and its immediately left A was already decoded from the history. A new A contributes two beta addresses; a new C contributes three unless its left A already contributes LLL and LR. The leaf reply label is unique. If d counts the nonempty branch and absent reply fibers, then one is at most d and d is at most both two and the beta increase. When the increase is one, every survivor has a node at the queried address, so the absent child is empty.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Scale40BetaGainChildren.betaLeaves`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Scale40BetaGainChildren.psi`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Scale40BetaGainChildren.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualStrictHistoryCapacity](ActualStrictHistoryCapacity.md)
