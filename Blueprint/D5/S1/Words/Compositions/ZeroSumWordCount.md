# Zero-sum word counts

## Abstract

Factorial bounds for zero-sum words with distinct letters.

For a finite integer alphabet S, an ordering is a list using each letter of S exactly once. A weak word has nonnegative sums for all prefixes. A strict word has positive sums for all nonempty proper prefixes. The functions weakCount and strictCount count these words. The alphabet sum is the sum of its integer letters. Subtraction in factorial arguments is natural subtraction.

**Theorem 1.1 (Upper bound for strict words).**

$$\forall S: \operatorname{Finset}\left(\mathbb{Z}\right), \operatorname{sum}\left(S\right) = 0 \implies \operatorname{Nonempty}\left(S\right) \implies \operatorname{strictCount}\left(S\right) \le \operatorname{factorial}\left((\operatorname{card}\left(S\right) - 1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/ZeroSumWordCount.strictCount_le_factorial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rotate each strict word to a fixed initial letter. Two words with the same image lie in the same rotation class. For a zero-sum word, two different strict rotations would give a segment with both positive and negative sum. The map into anchored orderings is therefore injective.

**Theorem 1.2 (Lower bound for weak words).**

$$\forall S: \operatorname{Finset}\left(\mathbb{Z}\right), \operatorname{sum}\left(S\right) = 0 \implies \operatorname{Nonempty}\left(S\right) \implies \operatorname{factorial}\left((\operatorname{card}\left(S\right) - 1)\right) \le \operatorname{weakCount}\left(S\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/ZeroSumWordCount.factorial_le_weakCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cut each zero-sum word after a minimum prefix sum. The resulting rotation has nonnegative prefix sums, so every rotation class contains a weak word. Rotating weak words to a fixed letter maps onto all anchored orderings. There are exactly (|S|-1)! anchored orderings.

**Theorem 1.3 (Trivial upper bound).**

$$\forall S: \operatorname{Finset}\left(\mathbb{Z}\right), \operatorname{weakCount}\left(S\right) \le \operatorname{factorial}\left(\operatorname{card}\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/ZeroSumWordCount.weakCount_le_factorial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weak words form a subset of all orderings, whose number is |S|!.

## References

- Truth anchor: `D5/S1/Words/Compositions/ZeroSumWordCount.factorial_le_weakCount`
- Truth anchor: `D5/S1/Words/Compositions/ZeroSumWordCount.strictCount_le_factorial`
- Truth anchor: `D5/S1/Words/Compositions/ZeroSumWordCount.weakCount_le_factorial`
- Dependency: [D5/S1/Words/Compositions/PhiTailEncoding](PhiTailEncoding.md)
