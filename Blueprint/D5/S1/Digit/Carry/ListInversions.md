# List Inversions and Local Replacement Bounds

## Abstract

Local list replacements have inversion costs bounded by surrounding occurrence counts.

All entries are natural numbers, and P and S are arbitrary surrounding lists. The notation ++ denotes list concatenation, count(L, x) counts occurrences of x in L, and every map, filter, and sum is a list operation. Repeated entries retain their multiplicity. Subtraction is natural-number subtraction.

**Definition 1.1 (Count inversions by head recursion).**

$$inv\left([]\right) = 0 \land \forall x \in Nat, \forall xs \in List\left(Nat\right), inv\left(x :: xs\right) = inv\left(xs\right) + countP\left(xs, (y \mapsto decide\left(y < x\right))\right)$$

*Formalization.* `D5/S1/Digit/Carry/ListInversions.inv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An inversion is a pair of positions p < q whose entries satisfy s[p] > s[q]. The empty list has no inversions. For a head x and tail xs, the inversions inside xs are retained, and each tail entry strictly smaller than x contributes one inversion with the head.

**Theorem 1.2 (Separate the window from its surroundings).**

$$\forall P \in List\left(Nat\right), \forall W \in List\left(Nat\right), \forall S \in List\left(Nat\right), inv\left(P ++ W ++ S\right) = (inv\left(P\right) + inv\left(S\right) + sum\left(map\left((p \mapsto length\left(filter\left((q \mapsto decide\left(q < p\right)), S\right)\right)), P\right)\right)) + inv\left(W\right) + sum\left(map\left((x \mapsto length\left(filter\left((p \mapsto decide\left(x < p\right)), P\right)\right)), W\right)\right) + sum\left(map\left((x \mapsto length\left(filter\left((q \mapsto decide\left(q < x\right)), S\right)\right)), W\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/ListInversions.inv_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural-number lists P, W, and S, the parenthesized term counts inversions inside P, inside S, and from P to S; it is independent of W. The remaining terms count inversions inside W, from P to W, and from W to S. Each occurrence of a window entry contributes separately. The proof inducts on the prefix and interchanges the two finite list counts.

**Theorem 1.3 (Replace a repeated entry above two).**

$$\forall P \in List\left(Nat\right), \forall S \in List\left(Nat\right), \forall i \in Nat, 2 < i \Rightarrow inv\left(P ++ [i - 2, i + 1] ++ S\right) \le inv\left(P ++ [i, i] ++ S\right) + (count\left(P ++ S, i - 1\right) + count\left(P ++ S, i\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/ListInversions.inv_replace_double` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural i with 2 < i, replacing [i, i] by [i - 2, i + 1] in any surroundings increases the inversion count by at most the total occurrences of i - 1 and i in P ++ S. The hypothesis 2 < i is part of the statement. Splitting the crossing counts at successive thresholds isolates these occurrence counts; monotonicity bounds the other terms.

**Theorem 1.4 (Merge consecutive entries).**

$$\forall P \in List\left(Nat\right), \forall S \in List\left(Nat\right), \forall a \in Nat, inv\left(P ++ [a + 2] ++ S\right) \le inv\left(P ++ [a, a + 1] ++ S\right) + count\left(P ++ S, a + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/ListInversions.inv_replace_adjacent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural a, replacing [a, a + 1] by [a + 2] increases the inversion count by at most the occurrences of a + 1 in P ++ S. There is no positivity assumption on a. The new suffix threshold adds exactly the occurrences of a + 1 in S, while the prefix contribution is bounded by the previous crossing counts.

**Theorem 1.5 (Merge two ones).**

$$\forall P \in List\left(Nat\right), \forall S \in List\left(Nat\right), inv\left(P ++ [2] ++ S\right) \le inv\left(P ++ [1, 1] ++ S\right) + count\left(P ++ S, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/ListInversions.inv_replace_ones` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replacing [1, 1] by [2] in arbitrary natural-number surroundings increases the inversion count by at most the occurrences of 1 in P ++ S. Zeros in the suffix are allowed: their contribution remains in the count of entries below 1. The threshold from 1 to 2 adds only suffix ones.

**Theorem 1.6 (Replace two twos).**

$$\forall P \in List\left(Nat\right), \forall S \in List\left(Nat\right), inv\left(P ++ [1, 3] ++ S\right) \le inv\left(P ++ [2, 2] ++ S\right) + count\left(P ++ S, 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/ListInversions.inv_replace_twos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replacing [2, 2] by [1, 3] in arbitrary natural-number surroundings increases the inversion count by at most the occurrences of 2 in P ++ S. The prefix threshold from 2 to 1 and the suffix threshold from 2 to 3 contribute the prefix and suffix twos, respectively; the other crossing terms are bounded by monotonicity.

## References

- Truth anchor: `D5/S1/Digit/Carry/ListInversions.inv`
- Truth anchor: `D5/S1/Digit/Carry/ListInversions.inv_replace_adjacent`
- Truth anchor: `D5/S1/Digit/Carry/ListInversions.inv_replace_double`
- Truth anchor: `D5/S1/Digit/Carry/ListInversions.inv_replace_ones`
- Truth anchor: `D5/S1/Digit/Carry/ListInversions.inv_replace_twos`
- Truth anchor: `D5/S1/Digit/Carry/ListInversions.inv_window`
