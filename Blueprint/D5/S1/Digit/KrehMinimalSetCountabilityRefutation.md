# Kreh's Minimal-Set Countability Conjecture

## Abstract

Uncountably many infinite positive decimal-subsequence sets have first minimal-layer sizes 2 and 1.

**Definition 1.1 (The asserted countability of the exceptional family).**

$$claim \Leftrightarrow \operatorname{Countable}\left(\{M \subseteq \mathbb{N} \mid (\forall n \in \mathbb{N},\; (n \in M \Rightarrow 0 < n)) \land ((\operatorname{Infinite}\left(M\right)) \land (\operatorname{eta}\left(M, 1\right) \le \operatorname{eta}\left(M, 0\right)))\}\right)$$

*Formalization.* `D5/S1/Digit/KrehMinimalSetCountabilityRefutation.claim` (`✓ std3`).

*Citation.* Martin Kreh (2015). *Minimal Sets, Journal of Integer Sequences 18 (2015), Article 15.5.3*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL18/Kreh/kreh2.pdf>.

*Commentary.*

This is the first sentence of Conjecture 18. Here N includes zero, and the explicit positivity condition restricts every member of M to Kreh's positive integers. Countable applies to the collection of sets M. The function eta(M,k) counts the minimal elements after k successive removals in the decimal-string subsequence order. It is the source's eta with superscript k; Definition 16 abbreviates eta(M,1) as eta(M). No computability or definability restriction is placed on M.

**Theorem 1.2 (The family is uncountable).**

$$\neg \operatorname{Countable}\left(\{M \subseteq \mathbb{N} \mid (\forall n \in \mathbb{N},\; (n \in M \Rightarrow 0 < n)) \land ((\operatorname{Infinite}\left(M\right)) \land (\operatorname{eta}\left(M, 1\right) \le \operatorname{eta}\left(M, 0\right)))\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/KrehMinimalSetCountabilityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Kreh (2015). *Minimal Sets, Journal of Integer Sequences 18 (2015), Article 15.5.3*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL18/Kreh/kreh2.pdf>.

*Commentary.*

Kreh's Theorem 14 and Examples 15 and 17 already supply the two-seed chain mechanism with minimal-layer sizes 2, 1, 1, and then 1 forever. The argument here makes an arbitrary-subset encoding explicit to deduce uncountability.

For an arbitrary subset A of N, put u(j)=16*10^j. Let T(A) contain every u(2n) and also u(2n+1) exactly when n belongs to A, and put F(A)={1,6} union T(A). The printed digits of u(j) are 1 and 6 followed by j zeros. Thus u(i) is a decimal subsequence of u(j) exactly when i is at most j.

The seeds 1 and 6 are incomparable, while 1 precedes every tail element. No tail element precedes either seed. Hence minimal(F(A))={1,6}; removing it leaves T(A). The mandatory element u(0)=16 precedes every element of T(A), so its minimal set is {16}. Both minimal sets are finite, and their cardinalities are exactly 2 and 1. The convention that ncard is zero on infinite sets plays no role.

Every element is positive, and the injective map n to u(2n) proves that F(A) is infinite even when A is empty. Membership of u(2j+1) in F(A) recovers membership of j in A: such a value is neither a seed nor an even-indexed value. Therefore A to F(A) is injective on the entire powerset of N. If the displayed collection were countable, composing this injection with its natural-number encoding would contradict Cantor's theorem.

## References

- Truth anchor: `D5/S1/Digit/KrehMinimalSetCountabilityRefutation.claim`
- Truth anchor: `D5/S1/Digit/KrehMinimalSetCountabilityRefutation.result`
- Dependency: [D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation](KrehMinimalSetLayerGrowthRefutation.md)
