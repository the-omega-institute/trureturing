# Reversed Prefixes Are Fully Right-Special

## Abstract

The reverse of every natural-start prefix of the literal m-bonacci word is an actual fully right-special factor.

**Definition 1.1 (Original sentinel iterates).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(sentinelIter\left(m, 0\right) = nil\left(\right) \land \left(\forall k \in \mathbb{N},\; sentinelIter\left(m, k + 1\right) = T\left(m, sentinelIter\left(m, k\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/MBonacciReversedPrefixFRS.sentinelIter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sentinelIter(0) is the empty list and sentinelIter(k+1) is T(sentinelIter(k)). This is the original recursive sentinel, definitionally related by induction to the original function iterate. The Parikh converse uses this same sequence.

**Theorem 1.2 (All original sentinel right extensions).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall t \in \mathbb{N},\; FRS\left(m, sentinelIter\left(m, t\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciReversedPrefixFRS.sentinel_frs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least two and every k, the original sentinelIter(k) is fully right-special on the same actual infinite word. The empty case uses the existing occurrence of every letter. Each successor uses the original cyclic predecessor and the exact right-extension occurrence bridge. This supplies all m attained vectors for the converse.

For every natural order m at least two, write word, Occ and FRS for the literal m-bonacci word and its predicates at that order. For every natural length ell, include its position-zero prefix. The factor is taken at a natural start and then reversed; occurrence starts remain natural and may depend on the appended letter.

**Theorem 1.3 (Every reversed prefix is fully right-special).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall ell \in \mathbb{N},\; length\left(reverse\left(factor\left(word, 0, ell\right)\right)\right) = ell \land \left(\left(\exists q \in \mathbb{N},\; Occ\left(reverse\left(factor\left(word, 0, ell\right)\right), q\right)\right) \land FRS\left(reverse\left(factor\left(word, 0, ell\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciReversedPrefixFRS.reversed_prefix_fully_right_special` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof constructs sentinel iterates T repeatedly from the empty source. Public actual-word laws transport their occurrence at zero and strict boundary growth gives ell at most the iterate length. The literal images make every sentinel iterate palindromic. Its suffix of length ell is the reversed prefix, and dropping the common prefix from each actual right extension preserves a natural-start occurrence of the reversed suffix.

The result covers ell equal to zero and m equal to two. The relation between the Parikh-vector cardinality of all factors of a given length and greedy numeration digits requires further results.

## References

- Truth anchor: `D5/S1/Words/MBonacciReversedPrefixFRS.reversed_prefix_fully_right_special`
- Truth anchor: `D5/S1/Words/MBonacciReversedPrefixFRS.sentinelIter`
- Truth anchor: `D5/S1/Words/MBonacciReversedPrefixFRS.sentinel_frs`
- Dependency: [D5/S1/Words/MBonacciSentinelDesubstitution](MBonacciSentinelDesubstitution.md)
