# Interval Diagnostic Merging

## Abstract

Adjacent interval messages compute the earliest failed seam while retaining the incoming bit.

A word has k+1 literal windows, indexed from zero through k. A nonterminal seam is bad when the left window's last bit and the right window's first bit are both one. The task returns the smallest bad seam, or the final coordinate when the last window is zero, or acceptance when neither failure occurs. Intervals are half-open: [a,b) contains coordinates a through b-1. Ordered trees join adjacent nonempty blocks at every fork and allow every binary parenthesization.

A failed message stores the first bad internal seam and its interval's incoming bit. It has no outgoing field. A live message stores the incoming bit and the last window's outgoing bit, except that a block ending at k+1 stores the terminal-zero flag. The incoming bit is the first window's first bit, fixed to zero at coordinate zero. A leaf is always live; terminal zero is tested only by the root readout.

The merger has four rules, in order. A failed left child keeps its message. Otherwise, an outgoing one meeting an incoming one fails at the joining seam, retaining the left incoming bit. Otherwise, a failed right child passes its position with the left incoming bit. Otherwise, the merged live message keeps the left incoming bit and the right outgoing or terminal flag. The seam coordinate is the greatest leaf coordinate of the left child; no word is read by the merger.

**Theorem 1.1 (Every Ordered Tree Computes the Prescribed Messages).**

$$\forall k,t,w, \operatorname{Ordered}\left(k, 0, k+1, t\right) \implies \operatorname{Full}\left(t\right) \land \operatorname{leaves}\left(t\right) = \operatorname{univ}\left(\operatorname{Fin}\left(k+1\right)\right) \land (\forall s \in \operatorname{subtrees}\left(t\right), \exists a,b, a < b \land b \le k+1 \land \operatorname{leaves}\left(s\right) = \operatorname{interval}\left(k, a, b\right) \land (\forall m, \operatorname{Semantics}\left(a, b, w, m\right) \iff m = \operatorname{evaluate}\left(\operatorname{implementation}\left(k\right), s, w\right))) \land \operatorname{read}\left(\operatorname{evaluate}\left(\operatorname{implementation}\left(k\right), t, w\right)\right) = \operatorname{task}\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/IntervalDiagnosticMerge.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Semantics describes a message independently of evaluation. In a failed message, its position lies inside the interval, is a bad internal seam, and every earlier internal seam is good. Its incoming field equals the left boundary bit. In a live message, every internal seam is good and both fields equal their prescribed boundary bits. The equivalence characterizes the evaluated message uniquely at every subtree.

For adjacent blocks [a,b) and [b,c), an internal bad seam belongs to the left block, is b-1, or belongs to the right block. Every left internal seam precedes the joining seam, which precedes every right internal seam. These three ordered possibilities prove the four merger rules and propagate the incoming bit even after failure. Induction over the tree proves the same message meaning at every descendant. At the root the only remaining test is the terminal-zero flag, giving exactly the first rejection task.

Combining interval summaries is the classical segment-tree pattern; associative reductions and prefix scans are treated by Guy E. Blelloch in Prefix Sums and Their Applications. The concrete summary here retains an incoming bit after internal failure because a later merge with an earlier block can expose an earlier joining failure.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/IntervalDiagnosticMerge.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/FirstRejectionCutCapacity](FirstRejectionCutCapacity.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/FourMessageTreeRigidity](FourMessageTreeRigidity.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/TreeMessageRealization](TreeMessageRealization.md)
