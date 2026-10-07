# Lowest Signed Digit and Dyadic Valuation

## Abstract

The first coefficient equal to plus or minus one fixes the dyadic valuation of the signed value.

**Theorem 1.1 (Peeling the zero prefix).**

$$\forall ds \in \operatorname{List}\left(\mathbb{Z}\right),\; \forall k \in \mathbb{N},\; \left(\left(\forall i \in \mathbb{N},\; i < k \Rightarrow \operatorname{getD}\left(\operatorname{ite}\left(i < \operatorname{List.length}\left(ds\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(ds, i\right)\right), \operatorname{none}\left(\right)\right), 0\right) = 0\right) \land \left(\operatorname{getD}\left(\operatorname{ite}\left(k < \operatorname{List.length}\left(ds\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(ds, k\right)\right), \operatorname{none}\left(\right)\right), 0\right) = \operatorname{neg}\left(1\right) \lor \operatorname{getD}\left(\operatorname{ite}\left(k < \operatorname{List.length}\left(ds\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(ds, k\right)\right), \operatorname{none}\left(\right)\right), 0\right) = 1\right)\right) \Rightarrow \operatorname{padicValInt}\left(2, \operatorname{foldr}\left(\lambda z:\mathbb{Z} x:\mathbb{Z} \mapsto z + 2 \cdot x, 0, ds\right)\right) = k$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/SignedDigitValuation.signed_digits_lowest_valuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite integer list is read least significant first. All positions below k vanish, and its coefficient at k is either minus one or plus one. Higher coefficients are arbitrary integers; nonadjacency is not required. The value is a nonzero multiple of exactly 2 to the power k, because the first residual is odd. Option lookup uses default zero. padicValInt is Mathlib's valuation of the natural absolute value of the integer.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/SignedDigitValuation.signed_digits_lowest_valuation`
