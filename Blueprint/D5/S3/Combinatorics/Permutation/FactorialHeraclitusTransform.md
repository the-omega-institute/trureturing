# The Factorial Heraclitus Transform

## Abstract

Every integer occurs in the factorial Heraclitus transform.

The natural index starts at zero. Values are integers. Factorial distances are k! with k at least one. Ranking enumerates 0, 1, -1, 2, -2, and so on: smaller absolute value first, positive first on ties. The sequence uses its entire actual history, not a finite approximation or a substitute recurrence.

**Definition 1.1 (The exact integer order).**

$$\operatorname{unrank}\left(r\right) = \operatorname{ifodd}\left(r, \operatorname{div}\left(\operatorname{add}\left(r, 1\right), 2\right), \operatorname{neg}\left(\operatorname{div}\left(r, 2\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.unrank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At odd rank r the value is (r+1)/2; at even rank it is -r/2. Both quotients are natural floor division. The private inverse rank proves bijectivity and the stated absolute-value order.

**Definition 1.2 (Allowed distances).**

$$\operatorname{IsFactorial}\left(d\right) \iff \exists k \in \mathbb{N}, 1 \le k \land d = \operatorname{factorial}\left(k\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.IsFactorial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The witness k is a natural number at least one. Thus 1 and 2 are allowed distances, and zero is excluded.

**Definition 1.3 (The least unused admissible value).**

$$\operatorname{next}\left(l, c\right) = \operatorname{unrank}\left(\operatorname{find}\left(\operatorname{admissible}\left(l, c\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.next` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nat.find minimizes rank among values outside the supplied list at factorial distance from the current integer. A sufficiently large positive factorial displacement proves that this set is nonempty.

**Definition 1.4 (The complete reversed history).**

$$\operatorname{terms}\left(0\right) = \operatorname{singleton}\left(0\right) \land \operatorname{terms}\left(\operatorname{add}\left(n, 1\right)\right) = \operatorname{cons}\left(\operatorname{next}\left(\operatorname{terms}\left(n\right), \operatorname{headD}\left(\operatorname{terms}\left(n\right), 0\right)\right), \operatorname{terms}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.terms` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial history is [0]. A successor prepends next(terms(n), headD(terms(n),0)). Histories have length n+1 and no repeated value.

**Definition 1.5 (OEIS A393434).**

$$\operatorname{a}\left(n\right) = \operatorname{headD}\left(\operatorname{terms}\left(n\right), 0\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value a(n) is the head of terms(n), with default zero. The history is always nonempty, so this default does not alter the rule.

**Definition 1.6 (The surjectivity conjecture).**

$$\forall z \in \mathbb{Z}, \exists n \in \mathbb{N}, \operatorname{a}\left(n\right) = z$$

*Formalization.* `D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every integer is the value at some natural index, exactly the conjecture quoted in the supplied OEIS A393434 source.

**Theorem 1.7 (Every integer appears).**

$$\forall z \in \mathbb{Z}, \exists n \in \mathbb{N}, \operatorname{a}\left(n\right) = z$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a393434-factorial-heraclitus` (proved) by `D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a393434-factorial-heraclitus","declaration_gid":"D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The 25-term base block covers [-12,12] and ends at -11. For k at least four, a complete interval [-k!/2,k!/2] ending at 1-k!/2 extends to the next factorial interval. Minimal rank forces the jump upward, the consecutive positive ascent, and the jump to the negative endpoint. During descent, a distance-2 candidate prevents adjacent visited magnitudes except at the bottom. The remaining magnitudes can therefore be filled in increasing order with steps 1 or 2, ending at 1-(k+1)!/2. Factorial growth places each integer in one of these intervals. History length, absence of repetitions and interval cardinality identify the boundary index as k!, giving the full block invariant. No closed formula for the negative-term order is needed.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.IsFactorial`
- Truth anchor: `D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.a`
- Truth anchor: `D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.claim`
- Truth anchor: `D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.next`
- Truth anchor: `D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.result`
- Truth anchor: `D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.terms`
- Truth anchor: `D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.unrank`
