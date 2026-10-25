# Simultaneous fixed and moving tail limits

## Abstract

Simultaneous fixed and moving tail limits

**Theorem 1.1 (Simultaneous fixed and moving tail limits).**

Lean statement: `D5/S3/Topology/Measures/L1TailSelection.exists_selection`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1TailSelection.exists_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q be a real array indexed by two naturals, bounded between zero and a real B, and antitone in its second index. Let P(i,N,K) be any proposition such that, for each i and N, it holds eventually in natural K. There exist natural sequences j,K,N, a real sequence c and a real alpha such that j is strictly increasing, i < K(i), alpha >= 0, alpha <= c(k) for every k, c tends to alpha, Q(j(i),k) tends to c(k) for every fixed k, and Q(j(i),K(i)) tends to alpha. In addition P(i,N(i),K(i)) holds for every i, and j(h) <= N(i) whenever h < i. A common scalar Hilbert selector first makes the whole countable array converge coordinatewise. A recursive choice then enforces the old-source constraint and a moving-tail error tending to zero. This avoids any assumption that a limsup is attained.

## References

- Truth anchor: `D5/S3/Topology/Measures/L1TailSelection.exists_selection`
- Dependency: [D5/S3/Topology/Measures/L1WeakExtraction](L1WeakExtraction.md)
