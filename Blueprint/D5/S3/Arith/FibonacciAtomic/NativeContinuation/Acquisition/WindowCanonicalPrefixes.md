# Actual prefixes in the extended execution

## Abstract

Actual prefixes in the extended execution.

For every split into a prefix and suffix, the very same final accepting execution contains the actual boundary after that prefix. Its state stores the original Horner coordinates and the actual number of windows read, including null padding.

The prefix time is at most the final time and at most four plus the prefix length multiplied by the sum of fifteen times the whole height and forty-six. At that boundary the packed work head is at origin, the source head is at the split, and the saved low bit is the exact prefix seam.

**Theorem 1.1 (source prefix registers).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowCanonicalPrefixes.source_prefix_registers`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowCanonicalPrefixes.source_prefix_registers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: source_prefix_registers (pre suf : List Window) (e : Bool) (T : ℕ) (hg : D5.S3.Arith.ZeckendorfFutureKernel.legal false (NativeContinuation.NullReplyFiber.highBits ((pre ++ suf).map Original.letter))) (hfinal : run (initial (pre++suf) e) T = registerEnd (pre++suf) e) : ∃ q : ℕ, q ≤ T ∧ q ≤ 4+pre.length*(15*(pre++suf).length+46) ∧ run (initial (pre++suf) e) q = base (boundary (inputSource (pre++suf) e) pre.length (columnsAfter [zeros] pre) 0 (.source (seamAfter false pre))) ∧ Original.pair (columnsAfter [zeros] pre) = NativeContinuation.JointLaw.composition (pre.map Original.letter) ∧ valueCount (columnsAfter [zeros] pre) = pre.length ∧ (columnsAfter [zeros] pre).length ≤ 1+3*pre.length

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowCanonicalPrefixes.source_prefix_registers`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowAcquisitionFidelity](WindowAcquisitionFidelity.md)
