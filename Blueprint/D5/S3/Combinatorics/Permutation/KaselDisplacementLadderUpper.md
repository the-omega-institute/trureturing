# Kasel displacement upper construction

## Abstract

A normalized valid stage scheme attains displacement at most m minus two.

**Theorem 1.1 (An attaining normalized scheme).**

$$\forall m \in \mathbb {N}, 2 \le m \implies \exists s, r: \mathbb {N} \to \mathbb {N}, \operatorname{Valid}\left(\operatorname{SA}\left(m\right), s, r\right) \land \operatorname{Normalized}\left(\operatorname{SA}\left(m\right), s\right) \land (\forall v \in distinguished, \operatorname{s}\left(v\right) \le \lfloor \operatorname{block}\left(v\right)/2\rfloor + (m - 2))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderUpper.upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m at least two, there are stage and fibre-position functions on the natural numbers giving a valid normalized scheme on S_A at horizon 4^m. Every distinguished value has stage at most half its dyadic block index, rounded down, plus m minus two. The distinguished set is {3,4,9,10,11,12,13,14,15,16}.

Place 3 and 4 at stage one, and every other value at stage m. In the final fibre, all evens precede all odds. Within each parity, reverse the lowest 2m+1 binary digits after XOR with target 4 for evens or target 3 for odds. This finite numeric rank decides comparisons at the lowest differing bit and puts its target first. It is injective below 2^(2m+1).

The endpoints of an arithmetic progression have equal parity. A different middle parity makes its position an extreme; equal parities reduce the same obstruction recursively by division by two. An early endpoint 4 is the least position, and an early endpoint 3 is least among odds. If an AP starts at 3 with an even middle value y greater than 4, the endpoint 2y-3 has block index block(y)+1 and cannot belong to S_A. No considered AP has middle value 3 or 4. These facts exclude both increasing and decreasing APs in the stage concatenation.

Membership bounds the block index by 2m, giving normalization at stage m. The early values have block index two. The remaining distinguished values have block index four, so their displacement is exactly m minus two. This theorem establishes the upper construction; a matching lower bound is a separate assertion.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderUpper.upper_bound`
- Dependency: [D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs](KaselDisplacementLadderDefs.md)
