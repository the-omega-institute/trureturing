# Parity of the Indices at Value Five in OEIS A374911

## Abstract

Every index at which OEIS A374911 takes value five is even.

**Theorem 1.1 (Value five forces an even index).**

$$\forall n \in \mathbb{N},\; \operatorname{seq}\left(n\right) = 5 \Rightarrow 2 \mid n$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PowerResidueRecursionFive.oeisA374911_valueFive_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2024). *OEIS A374911*. URL: <https://oeis.org/A374911>.

*Commentary.*

The sequence is the power-residue recursion with initial value one. For an index with value five, both recursive terms are positive. A left value of one forces the index to be a positive power of two, where the sequence has value three. A right value of one makes the index divide the power of three, hence the index is divisible by three. The left value would then be four, placing the left remainder at three or nine. This would make the power of two divisible by three. For an index greater than one, if a base raised to the index is congruent to one modulo the index, its order modulo the least prime factor divides both the index and that prime minus one. These two numbers are coprime. The base is therefore one modulo the least prime factor. Base two rules out a left recursive value of two. The only remaining ordered pair is three and two, so value five occurs exactly when the base-two remainder is a positive power of two and the base-three remainder is one. Base three then forces the least prime factor to be two.

## References

- Truth anchor: `D5/S3/Arith/Congruence/PowerResidueRecursionFive.oeisA374911_valueFive_even`
- Dependency: [D5/S3/Arith/Congruence/PowerResidueRecursionFour](PowerResidueRecursionFour.md)
