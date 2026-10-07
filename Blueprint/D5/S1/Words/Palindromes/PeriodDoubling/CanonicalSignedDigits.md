# Uniqueness of Nonadjacent Signed Digits

## Abstract

Sparse signed binary expansions are uniquely determined by their value at any fixed digit length.

**Theorem 1.1 (Equal values force identical digit lists).**

$$\forall digits \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall other \in \operatorname{List}\left(\mathbb{Z}\right),\; \left(\left(\left(\left(\left(\left(\forall z \in \mathbb{Z},\; z \in digits \Rightarrow \left(z = \operatorname{neg}\left(1\right) \lor \left(z = 0 \lor z = 1\right)\right)\right) \land \left(\forall z \in \mathbb{Z},\; z \in other \Rightarrow \left(z = \operatorname{neg}\left(1\right) \lor \left(z = 0 \lor z = 1\right)\right)\right)\right) \land \operatorname{IsChain}\left(digits, a:\mathbb{Z} \mapsto b:\mathbb{Z} \mapsto a = 0 \lor b = 0\right)\right) \land \operatorname{IsChain}\left(other, a:\mathbb{Z} \mapsto b:\mathbb{Z} \mapsto a = 0 \lor b = 0\right)\right) \land \operatorname{length}\left(digits\right) = \operatorname{length}\left(other\right)\right) \land \operatorname{foldr}\left(z:\mathbb{Z} \mapsto x:\mathbb{Z} \mapsto z + 2 \cdot x, 0, digits\right) = \operatorname{foldr}\left(z:\mathbb{Z} \mapsto x:\mathbb{Z} \mapsto z + 2 \cdot x, 0, other\right)\right) \Rightarrow digits = other$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/CanonicalSignedDigits.nonadjacent_digits_unique` (`✓ std3`). ∎

*Citation.* Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone (1996). *Handbook of Applied Cryptography*. URL: <https://cacr.uwaterloo.ca/hac/about/chap14.pdf>.

*Commentary.*

Fact 14.124(i), page 628: "Every integer e has a unique sparse signed-digit representation." The lists here are ordered from the least significant digit upward, have the same length, and retain zero padding. Each digit belongs to minus one, zero, or one, and every adjacent pair has a zero. Equal radix-two values force equal low digits by parity and modulo-four rigidity; induction then identifies the complete lists.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/CanonicalSignedDigits.nonadjacent_digits_unique`
