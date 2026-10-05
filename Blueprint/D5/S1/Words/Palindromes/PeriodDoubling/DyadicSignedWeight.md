# Dyadic Splitting of Signed Weight

## Abstract

A dyadic boundary has exactly two possible carry costs.

**Theorem 1.1 (The exact dyadic minimum).**

$$\forall h \in \mathbb{N},\; \forall M \in \mathbb{Z},\; \forall u \in \mathbb{N},\; u \le 2^{h} \Rightarrow \operatorname{signedWeight}\left(M \cdot 2^{h} + \operatorname{cast}\left(u, \mathbb{Z}\right)\right) = \operatorname{min}\left(\operatorname{signedWeight}\left(M\right) + \operatorname{signedWeight}\left(\operatorname{cast}\left(u, \mathbb{Z}\right)\right), \operatorname{signedWeight}\left(M + 1\right) + \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{Nat.sub}\left(2^{h}, u\right), \mathbb{Z}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/DyadicSignedWeight.signed_weight_dyadic_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The high part M is any integer. The low part u is a natural number in the closed interval from zero to the dyadic power. The second branch uses truncated natural subtraction 2^h minus u, then coerces to an integer. Binary induction couples both carries, including the two endpoints.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/DyadicSignedWeight.signed_weight_dyadic_split`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SignedWeight](SignedWeight.md)
