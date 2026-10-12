# Convex Endpoint Matching

## Abstract

Convex endpoint matching bounds the sum of inner gaps.

A matching consists of disjoint endpoint pairs in the positions zero through n minus one. For an increasing, discretely convex natural-valued function, nesting the pairs at the extremes bounds every matching cost. All subtraction below is truncated subtraction in Nat.

**Definition 1.1 (Disjoint endpoint pairs).**

$$\forall I \in Type,\; \forall s \in \operatorname{Finset}\left(I\right),\; \forall l \in I \to Nat,\; \forall h \in I \to Nat,\; \forall n \in Nat,\; \operatorname{matchValid}\left(s, l, h, n\right) \Leftrightarrow \left(\left(\forall i \in I,\; i \in s \Rightarrow \left(l\left(i\right) < h\left(i\right) \land h\left(i\right) < n\right)\right) \land \left(\forall i \in I,\; i \in s \Rightarrow \left(\forall j \in I,\; j \in s \Rightarrow \left(\left(l\left(i\right) = l\left(j\right) \Rightarrow i = j\right) \land \left(\left(h\left(i\right) = h\left(j\right) \Rightarrow i = j\right) \land l\left(i\right) \ne h\left(j\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/ScatteredPalindromeMatching.matchValid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both endpoints are in range, every lower endpoint is strictly below its upper endpoint, endpoints of the same kind are injective, and a lower endpoint never equals an upper endpoint.

**Definition 1.2 (Cost of the nested matching).**

$$\forall f \in Nat \to Nat,\; \forall n \in Nat,\; \forall r \in Nat,\; \operatorname{nestSum}\left(f, n, r\right) = \sum_{i \in \operatorname{Finset}.range\left(r\right)} f\left(n - 2 \cdot \left(i + 1\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/ScatteredPalindromeMatching.nestSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The i-th nested pair leaves n−2(i+1) interior positions.

**Theorem 1.3 (Removing the outer nested pair).**

$$\forall f \in Nat \to Nat,\; \forall n \in Nat,\; \forall r \in Nat,\; \operatorname{nestSum}\left(f, n, r + 1\right) = f\left(n - 2\right) + \operatorname{nestSum}\left(f, n - 2, r\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/ScatteredPalindromeMatching.nestSum_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first summand has gap n minus two; the remaining summands form the nested cost on n minus two positions.

**Theorem 1.4 (The convex matching inequality).**

$$\forall I \in Type,\; [\operatorname{DecidableEq}\left(I\right)], \forall f \in Nat \to Nat,\; \operatorname{Monotone}\left(f\right) \Rightarrow \left(\operatorname{Monotone}\left(fun (k: Nat) \mapsto f\left(k + 1\right) - f\left(k\right)\right) \Rightarrow \left(\forall s \in \operatorname{Finset}\left(I\right),\; \forall l \in I \to Nat,\; \forall h \in I \to Nat,\; \forall n \in Nat,\; \operatorname{matchValid}\left(s, l, h, n\right) \Rightarrow \sum_{i \in s} f\left(h\left(i\right) - l\left(i\right) - 1\right) \le \operatorname{nestSum}\left(f, n, \operatorname{Finset}.card\left(s\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/ScatteredPalindromeMatching.matching_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the smallest lower endpoint and largest upper endpoint. When they belong to different pairs, discrete convexity bounds the cost after exchanging partners. Remove the outer pair and shift the remaining endpoints down by one. Strong induction on the number of pairs gives the bound, including the empty matching.

## References

- Truth anchor: `D5/S1/Words/Palindromes/ScatteredPalindromeMatching.matchValid`
- Truth anchor: `D5/S1/Words/Palindromes/ScatteredPalindromeMatching.matching_bound`
- Truth anchor: `D5/S1/Words/Palindromes/ScatteredPalindromeMatching.nestSum`
- Truth anchor: `D5/S1/Words/Palindromes/ScatteredPalindromeMatching.nestSum_succ`
