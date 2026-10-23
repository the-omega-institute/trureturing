# Integer intervals represented by run-avoiding words

## Abstract

The actual integer weighted sum uniquely represents the initial k-bonacci interval.

Fix a natural order k at least two. Write G(j)=dbonacci k (j+2). For j<k the weight is 2^j; for j at least k it is the sum of the preceding k weights. These are the initial-power and recurrence laws of DBonacci.Names. A word has exactly n Boolean coordinates. Coordinate zero is the least significant digit, and a true bit contributes its integer weight while a false bit contributes zero.

**Definition 1.1 (The specified integer weighted sum).**

$$\forall (k,n: \mathbb{N}), (\forall (w: \operatorname{Fin}\left(n\right) \to \operatorname{Bool}\left(\right)), (\operatorname{integerValue}\left(k, w\right) = \sum_{i: \operatorname{Fin}\left(n\right)} \operatorname{ite}\left(w\left(i\right), \operatorname{ofNat}\left(\operatorname{dbonacci}\left(k, \operatorname{val}\left(i\right)+2\right)\right), 0\right)))$$

*Formalization.* `D5/S1/Words/AdmissibleWords/KBonacciIntegerInterval.integerValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here val(i) is the natural coordinate of a finite index, ofNat is the canonical embedding into the integers, and ite selects its first value on a true Boolean. Thus the value is the exact sum of bit times integer weight.

**Theorem 1.2 (Every length, every order, and the actual value map).**

$$\forall (k,n: \mathbb{N}), (2\leq k \implies \operatorname{BijOn}\left(\operatorname{integerValue}\left(k\right), \{w: \operatorname{Fin}\left(n\right) \to \operatorname{Bool}\left(\right) \mid \forall (s: \mathbb{N}), (\neg \operatorname{TrueBlock}\left(w, s, k\right))\}, \operatorname{Ico}\left(0, \operatorname{ofNat}\left(\operatorname{dbonacci}\left(k, n+2\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciIntegerInterval.integer_value_interval_bijection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

TrueBlock(w,s,k) requires s+k at most n and every bit in [s,s+k) to be true. Ico denotes a lower-closed, upper-open integer interval, so the target is precisely the integers from zero through G(n)-1. BijOn includes membership of every value in that interval, injectivity on all literal legal words, and surjectivity onto every integer in the interval.

Read a word from its highest bit while keeping the scanner's remaining true-bit budget. A zero resets the budget and leaves the tail value unchanged. A one consumes one unit of budget and adds G(q), where q is the tail length. The existing bounded-run split separates these cases. Induction on length proves that each tail's actual weighted sum is below the cardinality of its budget layer and is injective. The zero branch is below G(q); the one branch is at least G(q). Within either branch, tail injectivity applies. The existing layer count then makes this bounded integer map surjective.

For n at least k, iterate this split to the first zero. Every legal high-first word has a unique prefix of j ones followed by zero, with 0 at most j and j<k, and a legal tail of length n-j-1. Put A(0)=0 and A(j)=G(n-1)+G(n-2)+...+G(n-j). The prefix contributes exactly A(j). The tail bijection therefore gives the whole group exactly the interval [A(j),A(j)+G(n-j-1)), which is [A(j),A(j+1)). The endpoints are adjacent; positivity of the weights makes the groups disjoint. The recurrence gives A(k)=G(n), so these groups exhaust the target interval. Locating the group of a target value, subtracting its prefix contribution, and recurring on the shorter tail gives the fixed-length encoding procedure.

For n<k every word is legal and all used weights are powers of two. The same induction includes this binary case. At n=0 there is one empty word, its sum is zero, and G(0)=1. Reversing finite indices changes high-first printing into the least-significant-first coordinates of the formula. A forbidden block beginning at s becomes the block beginning at n-(s+k), including a block ending at the final bit. The scanner and literal block condition agree at every length: the closed-word equivalence supplies n at least k, and both conditions are automatic at shorter lengths. Finally the natural sum embeds exactly into the nonnegative integers; every nonnegative target integer is recovered from its toNat representative.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciIntegerInterval.integerValue`
- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciIntegerInterval.integer_value_interval_bijection`
- Dependency: [D5/S1/Words/ClosedRunStarts](../ClosedRunStarts.md)
