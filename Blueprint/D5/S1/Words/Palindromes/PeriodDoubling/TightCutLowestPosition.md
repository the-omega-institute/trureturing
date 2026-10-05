# Lowest-Position Monotonicity

## Abstract

The lowest nonzero signed position never decreases on a tight legal cut.

**Theorem 1.1 (The literal minimum-position transition law).**

$$\forall n \in \mathbb{N},\; \forall j \in \mathbb{N},\; \left(\left(\left(\operatorname{classS}\left(n\right) \land j < n\right) \land \operatorname{Palindrome}\left(\operatorname{ofFn}\left(i:\operatorname{Fin}\left(\operatorname{NatSub}\left(n, j\right)\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(j + \operatorname{val}\left(i\right)\right)\right)\right)\right) \land \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{div}\left(n + 1, 2\right), \mathbb{Z}\right)\right) = \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{div}\left(j + 1, 2\right), \mathbb{Z}\right)\right) + 1\right) \Rightarrow \left(j = 0 \lor \operatorname{padicValNat}\left(2, \operatorname{div}\left(n + 1, 2\right)\right) \le \operatorname{padicValNat}\left(2, \operatorname{div}\left(j + 1, 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/TightCutLowestPosition.tight_cut_lowest_position` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A cut is tight when the minimum signed weight of the rounded half drops by exactly one. Complete cut realization excludes the invalid class mode. Lifting the base path to the minimum product gives a persistent flag for output nonzero digits emitted before any input nonzero digit. Its accepting potential bound zero excludes a true flag on a path with signed-weight drop one. Digit induction then yields the order of the first nonzero coefficients, and their literal dyadic valuations give the stated inequality. The zero endpoint is listed separately because its dyadic valuation is defined to be zero. div denotes natural integer quotient, and NatSub denotes truncated natural subtraction.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/TightCutLowestPosition.tight_cut_lowest_position`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseArithmetic](BaseArithmetic.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseLowestPosition](BaseLowestPosition.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/CutRepresentation](CutRepresentation.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SignedDigitValuation](SignedDigitValuation.md)
