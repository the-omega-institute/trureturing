# Unordered fork decorations

## Abstract

Normalized fork decorations correspond bijectively to the actual qualifying rooted-tree classes.

**Definition 1.1 (A bijection at each total size).**

$$\forall n \in \mathbb{N}, W_{n} \equiv T_{n}$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.classification` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Tₙ is the type of classes of actual parent maps on Fin n for which vertex height equals internal-vertex count. Wₙ consists of fork parameters b and c, one nonnegative leaf multiplicity at each of the b+c+1 spine nonterminals, and two nonnegative tip offsets. The tip multiplicities are one plus those offsets. At c=0 the offsets are sorted. The weight is b+c+5 plus the sum of all offsets and spine multiplicities, and equals n.

Inflation followed by labelling the carrier gives the forward map. The inverse prunes the original leaves and reads the multiplicities on the canonical fork. Fork depth and maximum depth fix b and c. A fork automorphism fixes the nonterminals in depth order and can exchange tips only when c=0. Sorting removes that ambiguity, including the case of equal fibre sizes.

## References

- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.classification`
- Dependency: [D5/S3/Combinatorics/UnorderedTrees/LeafDecoration](LeafDecoration.md)
