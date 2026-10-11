# Reversed Prefixes Are Fully Right-Special

## Abstract

The reverse of every natural-start prefix of the literal m-bonacci word is an actual fully right-special factor.

For every natural order m at least two, write word, Occ and FRS for the literal m-bonacci word and its predicates at that order. For every natural length ell, include its position-zero prefix. The factor is taken at a natural start and then reversed; occurrence starts remain natural and may depend on the appended letter.

**Theorem 1.1 (Every reversed prefix is fully right-special).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall ell \in \mathbb{N},\; length\left(reverse\left(factor\left(word, 0, ell\right)\right)\right) = ell \land \left(\left(\exists q \in \mathbb{N},\; Occ\left(reverse\left(factor\left(word, 0, ell\right)\right), q\right)\right) \land FRS\left(reverse\left(factor\left(word, 0, ell\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciReversedPrefixFRS.reversed_prefix_fully_right_special` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof constructs sentinel iterates T repeatedly from the empty source. Public actual-word laws transport their occurrence at zero and strict boundary growth gives ell at most the iterate length. The literal images make every sentinel iterate palindromic. Its suffix of length ell is the reversed prefix, and dropping the common prefix from each actual right extension preserves a natural-start occurrence of the reversed suffix.

The result covers ell equal to zero and m equal to two. The relation between the Parikh-vector cardinality of all factors of a given length and greedy numeration digits requires further results.

## References

- Truth anchor: `D5/S1/Words/MBonacciReversedPrefixFRS.reversed_prefix_fully_right_special`
- Dependency: [D5/S1/Words/MBonacciSentinelDesubstitution](MBonacciSentinelDesubstitution.md)
