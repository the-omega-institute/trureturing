# Order on Zeckendorf Representations

## Abstract

Greatest-index-first Zeckendorf representations carry numerical order lexicographically.

**Theorem 1.1 (Lexicographic order matches Fibonacci sums).**

$$\operatorname{IsZeck}(l) \land \operatorname{IsZeck}(k) \implies \left(l <_{\text{lex}} k \iff \sum_{i \in l} F_i < \sum_{j \in k} F_j\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ZeckendorfOrder.isZeckendorfRep_lex_iff_sum_fib_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two valid Zeckendorf index lists ordered from greatest index downward, strict lexicographic order is equivalent to strict order of the corresponding sums of Fibonacci numbers.

**Theorem 1.2 (Canonical Zeckendorf representations preserve strict order).**

$$\operatorname{zeck}(m) <_{\text{lex}} \operatorname{zeck}(n) \iff m < n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ZeckendorfOrder.zeckendorf_lex_iff_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's canonical Zeckendorf representation maps natural numbers to greatest-index-first lists so that list lexicographic order holds exactly when the original natural numbers are strictly ordered.

## References

- Truth anchor: `D5/S1/Words/ZeckendorfOrder.isZeckendorfRep_lex_iff_sum_fib_lt`
- Truth anchor: `D5/S1/Words/ZeckendorfOrder.zeckendorf_lex_iff_lt`
