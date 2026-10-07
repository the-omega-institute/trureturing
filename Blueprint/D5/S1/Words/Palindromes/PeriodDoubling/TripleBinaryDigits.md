# Minimum Signed Digits from Triple Binary Differences

## Abstract

Ordinary binary digits determine a minimum nonadjacent signed expansion.

**Theorem 1.1 (A minimum signed expansion from ordinary binary digits).**

$$\forall X \in \mathbb{N},\; \forall h \in \mathbb{N},\; 3 \cdot X < 2^{h + 1} \Rightarrow \left(\left(\operatorname{foldr}\left(z:\mathbb{Z} \mapsto acc:\mathbb{Z} \mapsto z + 2 \cdot acc, 0, \operatorname{ofFn}\left(i:\operatorname{Fin}\left(h\right) \mapsto \operatorname{cast}\left(\operatorname{mod}\left(\operatorname{Nat.div}\left(3 \cdot X, 2^{\operatorname{val}\left(i\right) + 1}\right), 2\right), \mathbb{Z}\right) - \operatorname{cast}\left(\operatorname{mod}\left(\operatorname{Nat.div}\left(X, 2^{\operatorname{val}\left(i\right) + 1}\right), 2\right), \mathbb{Z}\right)\right)\right) = \operatorname{cast}\left(X, \mathbb{Z}\right) \land \operatorname{IsChain}\left(\operatorname{ofFn}\left(i:\operatorname{Fin}\left(h\right) \mapsto \operatorname{cast}\left(\operatorname{mod}\left(\operatorname{Nat.div}\left(3 \cdot X, 2^{\operatorname{val}\left(i\right) + 1}\right), 2\right), \mathbb{Z}\right) - \operatorname{cast}\left(\operatorname{mod}\left(\operatorname{Nat.div}\left(X, 2^{\operatorname{val}\left(i\right) + 1}\right), 2\right), \mathbb{Z}\right)\right), a:\mathbb{Z} \mapsto b:\mathbb{Z} \mapsto a = 0 \lor b = 0\right)\right) \land \operatorname{signedWeight}\left(\operatorname{cast}\left(X, \mathbb{Z}\right)\right) = \operatorname{length}\left(\operatorname{filter}\left(z:\mathbb{Z} \mapsto (z != 0), \operatorname{ofFn}\left(i:\operatorname{Fin}\left(h\right) \mapsto \operatorname{cast}\left(\operatorname{mod}\left(\operatorname{Nat.div}\left(3 \cdot X, 2^{\operatorname{val}\left(i\right) + 1}\right), 2\right), \mathbb{Z}\right) - \operatorname{cast}\left(\operatorname{mod}\left(\operatorname{Nat.div}\left(X, 2^{\operatorname{val}\left(i\right) + 1}\right), 2\right), \mathbb{Z}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/TripleBinaryDigits.triple_digits_value_and_minimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At position i, the signed digit is the difference of the binary digits at position i+1 of 3X and X. The bound on h pads both numbers by leading zeros. The resulting signed digit list has value X, no adjacent nonzero digits, and exactly the minimum number of nonzero digits. Nat.div and mod denote natural integer division and remainder. Cast denotes the natural-to-integer embedding. Digits are listed from the lowest position upward.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/TripleBinaryDigits.triple_digits_value_and_minimality`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/NonadjacentSignedDigits](NonadjacentSignedDigits.md)
