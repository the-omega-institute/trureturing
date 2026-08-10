# The Per-Axis Trace-Map Recursion

## Abstract

Per-axis admissible-word partial sums satisfy the closed golden trace-map recursion.

**Theorem 1.1 (Partial sums and weights close under the trace-map recursion).**

$$W_{K+1}=W_K+t_{K+1}W_{K-1}, t_{K+1}=t_Kt_{K-1}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/TraceMap.trace_map_recursion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The per-axis partial sum of bit depth K ranges over admissible words: sets of Zeckendorf indices from one to K with no two consecutive indices selected. Each index is weighted by an exponential reading of the two faces, the expansion variable against the golden ratio power and the contraction variable against the golden conjugate power, one past the index. The theorem records that these partial sums and weights close as a recursion pair: the sum of depth K plus two splits along its top bit, whose use forces the neighbouring bit empty and so leaves a word two depths down, while the top weight itself is the product of the two preceding weights.

The first equation is pure finite combinatorics over an arbitrary weight sequence: the admissible words of a given depth partition into those avoiding the top bit, which are exactly the words one depth down, and those using it, which are top-bit insertions of words two depths down. The second equation is the golden instance: both golden powers satisfy the Fibonacci recurrence, so the exponential weights are multiplicative along consecutive indices. Together the pair drives the whole tower of per-axis partial sums from its two lowest depths, which is the trace-map mechanism of the source atom.

## References

- Truth anchor: `D5/S1/Recurrence/TraceMap.trace_map_recursion`
