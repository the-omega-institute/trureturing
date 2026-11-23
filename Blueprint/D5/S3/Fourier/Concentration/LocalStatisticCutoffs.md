# Changing the Index Set of a Local Tuple Statistic

## Abstract

Local neighborhood counts control the change in a tuple statistic under a new cutoff.

Let S and T be nonempty subsets of a finite index set J with real frequencies g. Write s and t for their respective sizes and b for the size of their symmetric difference. Fix a natural number k and a real score on ordered distinct-index tuples of length k+1. The score has magnitude at most M≥0. For a nonzero score, all frequencies of the tuple have distance at most R from its first frequency. For each index in S∪T the number of indices of S∪T within distance 2R of its frequency is at most the natural number D. Let A(U) sum the scores over ordered tuples with every index in U. Write L for M times the falling factorial of max(D−1,0) of order k.

**Theorem 1.1 (Local tuple sums vary with the changed indices).**

$$\left|\frac{\operatorname{A}\left(S\right)}{s}-\frac{\operatorname{A}\left(T\right)}{t}\right| \le \operatorname{min}\left(\frac{L \cdot {{k + 1} \cdot b + \left|s-t\right|}}{\operatorname{max}\left(s, t\right)}, 2 \cdot L\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/LocalStatisticCutoffs.local_statistic_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only tuples with a changed index can contribute to the difference of the two sums. Mark one slot containing a changed index. Every other slot is within distance 2R of the marked frequency by the triangle inequality, including when the mark is outside the first slot. Fix the marked index and slot and assign distinct entries from its neighborhood after erasing the marked index itself.

When bounding one sum, use only the first slot as the mark. Its size is then bounded by the number of eligible first indices times L. Compare the sums over the larger denominator and use this bound for the renormalization of the smaller set. The magnitude of each normalized sum is at most L, giving the second bound.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/LocalStatisticCutoffs.local_statistic_cutoff`
