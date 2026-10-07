# Minimum Weight of Nonadjacent Signed Digits

## Abstract

Every finite nonadjacent signed digit list realizes the minimum signed binary weight.

**Theorem 1.1 (Every nonadjacent signed expansion is minimal).**

$$\forall digits \in \operatorname{List}\left(\mathbb{Z}\right),\; \left(\left(\forall z \in \mathbb{Z},\; z \in digits \Rightarrow \left(z = \operatorname{neg}\left(1\right) \lor \left(z = 0 \lor z = 1\right)\right)\right) \land \operatorname{IsChain}\left(digits, a:\mathbb{Z} \mapsto b:\mathbb{Z} \mapsto a = 0 \lor b = 0\right)\right) \Rightarrow \operatorname{signedWeight}\left(\operatorname{foldr}\left(z:\mathbb{Z} \mapsto acc:\mathbb{Z} \mapsto z + 2 \cdot acc, 0, digits\right)\right) = \operatorname{length}\left(\operatorname{filter}\left(z:\mathbb{Z} \mapsto (z != 0), digits\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/NonadjacentSignedDigits.signed_weight_nonadjacent` (`✓ std3`). ∎

*Citation.* Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone (1996). *Handbook of Applied Cryptography*. URL: <https://cacr.uwaterloo.ca/hac/about/chap14.pdf>.

*Commentary.*

The list contains only minus one, zero, and one, in increasing binary-position order. Each adjacent pair contains a zero. Folding by z+2 acc computes its signed binary value, and filtering nonzero digits counts its weight. List induction resolves both possible nonzero low digits and proves that this count is the true minimum over all signed-power representations.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/NonadjacentSignedDigits.signed_weight_nonadjacent`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SignedWeight](SignedWeight.md)
