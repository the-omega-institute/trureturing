# Signed Tail Phase

## Abstract

The last nonzero signed coefficient gives the literal negative phase.

**Theorem 1.1 (Dominance of the highest signed coefficient).**

$$\forall ds \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall delta \in \operatorname{Bool},\; \left(\forall z \in \mathbb{Z},\; z \in ds \Rightarrow \left(z = \operatorname{neg}\left(1\right) \lor \left(z = 0 \lor z = 1\right)\right)\right) \Rightarrow \left(2 \cdot \operatorname{foldr}\left(\lambda z:\mathbb{Z} x:\mathbb{Z} \mapsto z + 2 \cdot x, 0, ds\right) - \operatorname{cast}\left(\operatorname{toNat}\left(delta\right), \mathbb{Z}\right) < 0 \Leftrightarrow \left(\operatorname{getD}\left(\operatorname{ite}\left(\operatorname{filter}\left(z:\mathbb{Z} \mapsto (z != 0), ds\right) = [], \operatorname{none}, \operatorname{some}\left(\operatorname{List.getLast}\left(\operatorname{filter}\left(z:\mathbb{Z} \mapsto (z != 0), ds\right)\right)\right)\right), 0\right) < 0 \lor \left(\operatorname{filter}\left(z:\mathbb{Z} \mapsto (z != 0), ds\right) = [] \land delta = \operatorname{true}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/SignedDigitPhase.signed_digits_negative_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite signed binary list is read least significant first. Every coefficient is minus one, zero or plus one. Its highest nonzero digit dominates all lower positions, so 2T minus the Boolean parity is negative exactly when the last nonzero sign is negative, or when the tail is empty and the parity is one. Nonadjacency is unnecessary. The empty list and absent last element use default zero. The last-option expression is none for an empty list and some(List.getLast(...)) otherwise; the nonempty proof argument is implicit.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/SignedDigitPhase.signed_digits_negative_phase`
