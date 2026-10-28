# Double-Tail Self-Shuffle Support

## Abstract

A triangular set of three unary gaps gives the exact distinct support of a double-tail self-shuffle.

All scalar variables are natural numbers. A word is a finite list of Boolean digits, with true representing one and false representing zero. The ordinaryShuffles operation completely consumes both operands in their internal order; converting its list of outputs to a finite set removes schedule multiplicities. Subtraction and division below are natural-number operations, with subtraction truncated at zero.

**Definition 1.1 (Unary prefix and two terminal zeros).**

$$\forall (m: \mathbb{N}), \operatorname{root}\left(m\right) = \operatorname{List.append}\left(\operatorname{List.replicate}\left(m, true\right), \operatorname{list}\left(false, false\right)\right)$$

*Formalization.* `D5/S1/Words/DoubleTailShuffleSupport.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operand has m initial ones followed by exactly two zeros. Empty unary prefixes are allowed.

**Theorem 1.2 (Exact triangular cardinality).**

$$\forall (m: \mathbb{N}), \operatorname{card}\left(\operatorname{toFinset}\left(\operatorname{ordinaryShuffles}\left(\operatorname{root}\left(m\right), \operatorname{root}\left(m\right)\right)\right)\right) = \operatorname{Nat.div}\left((m + 2) \cdot (m + 1), 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/DoubleTailShuffleSupport.self_shuffle_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every output is a ones, zero, b ones, zero, c ones, zero, zero, where a+b+c=2m and a is at least m. To see necessity, first shuffle a single zero against a unary prefix with two terminal zeros, then two zeros against that word, and finally two unary prefixes by induction on their total length. In each recursive branch the next digit comes from one operand, and all terminal zeros remain accounted for. Conversely put i=b+c and j=b. For every pair 0<=j<=i<=m, read all m ones from the first copy, m-i ones from the second, the first zero from the first copy, j ones from the second, the second zero from the first copy, and finally the remaining i-j ones and two zeros from the second. This produces precisely the three runs of lengths m+(m-i), j and i-j. The unary-gap uniqueness theorem recovers i and j from the output word. Thus the support is an injective image of the triangular parameter set, whose cardinality is the sum of i+1 for i from zero through m. This is an equality of distinct-word cardinalities for every natural m, including zero.

**Theorem 1.3 (Ordinary numeral of a power minus four).**

$$\forall (k: \mathbb{N}), 3 \le k\implies \operatorname{binaryWord}\left(2^{k} - 4\right) = \operatorname{root}\left(k - 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/DoubleTailShuffleSupport.binary_root_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least three, the positive natural number 2^k-4 equals four times the quantity (2^(k-2)-1). The latter factor has k-2 binary ones; multiplication by four appends two zeros. The existing binaryWord definition reverses the least-significant-first base-two digits and maps digit one to true. This is the ordinary numeral without leading zeros.

**Theorem 1.4 (The full eventual minus-four identity).**

$$\exists (K: \mathbb{N}), (3 \le K\land \forall (k: \mathbb{N}), K \le k\implies \operatorname{distinctSelfShuffleCount}\left(2^{k} - 4\right) = \operatorname{Nat.div}\left(k \cdot (k - 1), 2\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/DoubleTailShuffleSupport.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John W. Layman (2011). *OEIS A193020, distinct binary self-shuffles*. URL: <https://oeis.org/A193020>.

*Commentary.*

The published sequence counts distinct complete self-shuffle output words of an ordinary positive binary numeral. Choose K=3. For every k at least K, the numeral identity identifies the operand with root(k-2), and the exact support cardinality gives k*(k-1)/2. The existential threshold and every subsequent index are retained. The definition of the sequence comes from OEIS A193020; the proof of this minus-four assertion is the support argument given here.

## References

- Truth anchor: `D5/S1/Words/DoubleTailShuffleSupport.binary_root_original`
- Truth anchor: `D5/S1/Words/DoubleTailShuffleSupport.result`
- Truth anchor: `D5/S1/Words/DoubleTailShuffleSupport.root`
- Truth anchor: `D5/S1/Words/DoubleTailShuffleSupport.self_shuffle_card`
- Dependency: [D5/S1/Words/EndpointShuffleSupport](EndpointShuffleSupport.md)
