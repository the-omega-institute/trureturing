# Sparse Family Initial Arithmetic

## Abstract

Sparse Family Initial Arithmetic

**Theorem 1.1 (Sparse Family Initial Arithmetic).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \left(\left(\left(\operatorname{mod}\left(\operatorname{sum}\left(\operatorname{range}\left(a\right), i:\mathbb{N} \mapsto 2^{2 \cdot b + 2 + 3 \cdot i}\right) + \operatorname{sum}\left(\operatorname{range}\left(b\right), j:\mathbb{N} \mapsto 2^{2 \cdot j + 1}\right), 2\right) = 0 \land \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{div}\left(\operatorname{sum}\left(\operatorname{range}\left(a\right), i:\mathbb{N} \mapsto 2^{2 \cdot b + 2 + 3 \cdot i}\right) + \operatorname{sum}\left(\operatorname{range}\left(b\right), j:\mathbb{N} \mapsto 2^{2 \cdot j + 1}\right) + 1, 2\right), \mathbb{Z}\right)\right) = a + b\right) \land \operatorname{classS}\left(\operatorname{sum}\left(\operatorname{range}\left(a\right), i:\mathbb{N} \mapsto 2^{2 \cdot b + 2 + 3 \cdot i}\right) + \operatorname{sum}\left(\operatorname{range}\left(b\right), j:\mathbb{N} \mapsto 2^{2 \cdot j + 1}\right)\right)\right) \land \operatorname{signedDigitCharge}\left(\operatorname{sum}\left(\operatorname{range}\left(a\right), i:\mathbb{N} \mapsto 2^{2 \cdot b + 2 + 3 \cdot i}\right) + \operatorname{sum}\left(\operatorname{range}\left(b\right), j:\mathbb{N} \mapsto 2^{2 \cdot j + 1}\right)\right) = 2 \cdot a + \operatorname{mod}\left(a, 2\right) + b\right) \land \operatorname{markedPrefix}\left(\operatorname{sum}\left(\operatorname{range}\left(a\right), i:\mathbb{N} \mapsto 2^{2 \cdot b + 2 + 3 \cdot i}\right) + \operatorname{sum}\left(\operatorname{range}\left(b\right), j:\mathbb{N} \mapsto 2^{2 \cdot j + 1}\right), a, 2 \cdot b + 1, \operatorname{cast}\left(\operatorname{sum}\left(\operatorname{range}\left(b\right), k:\mathbb{N} \mapsto 2^{2 \cdot k}\right), \mathbb{Z}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/SparseInitialArithmetic.sparse_initial_arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any natural a and b, the literal sparse-family integer is even. Its rounded-half signed weight is a+b, it belongs to class S, its signed-digit charge is 2a plus a mod 2 plus b, and its a upper positive digits form a marked prefix at position 2b+1 above the displayed nonnegative tail. The nonadjacent expansion is identified with the canonical triple-binary digits using uniqueness with zero padding. div and mod denote natural integer quotient and remainder; cast records natural-to-integer coercions.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/SparseInitialArithmetic.sparse_initial_arithmetic`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/CutRepresentation](CutRepresentation.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixArithmetic](MarkedPrefixArithmetic.md)
