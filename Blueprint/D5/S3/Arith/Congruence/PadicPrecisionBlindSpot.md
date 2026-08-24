# The p-adic Precision Blind Spot

## Abstract

Prime-power readings agree through the p-adic valuation of a nonzero difference, and its successor is the first precision that distinguishes the integers.

**Lemma 1.1 (Reading agreement lasts exactly through the p-adic valuation).**

$$\begin{gathered}\forall p, k \in \mathbb{N},\\{}x, y \in \mathbb{Z},\\{}(\operatorname{Prime}\left(p\right) \land x \neq y) \Rightarrow (\operatorname{precisionReading}\left(p, k, x\right) = \operatorname{precisionReading}\left(p, k, y\right)) \iff k \leq \operatorname{padicValInt}\left(p, x - y\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PadicPrecisionBlindSpot.precision_reading_eq_iff_le_padicValInt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a prime p and two distinct integers x and y. Their precision-k readings are their residues modulo p^k. These readings agree exactly when k is at most the p-adic valuation of x - y.

Thus the valuation measures the complete blind range of the prime-power readout: every precision through that value hides the nonzero difference, while every larger precision detects it.

**Theorem 1.2 (The valuation successor is the first distinguishing precision).**

$$\begin{gathered}\forall p \in \mathbb{N},\\{}x, y \in \mathbb{Z},\\{}(\operatorname{Prime}\left(p\right) \land x \neq y) \Rightarrow \operatorname{IsLeast}\left(\{k \in \mathbb{N} \mid \operatorname{precisionReading}\left(p, k, x\right) \neq \operatorname{precisionReading}\left(p, k, y\right)\}, \operatorname{padicValInt}\left(p, x - y\right) + 1\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PadicPrecisionBlindSpot.first_distinguishing_precision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p and distinct integers x and y, one more than the p-adic valuation of x - y is a precision at which their prime-power readings differ.

Every smaller precision is at most the valuation and therefore gives equal readings. The successor consequently belongs to the set of distinguishing precisions and is no greater than any other member, so it is the least such precision.

## References

- Truth anchor: `D5/S3/Arith/Congruence/PadicPrecisionBlindSpot.first_distinguishing_precision`
- Truth anchor: `D5/S3/Arith/Congruence/PadicPrecisionBlindSpot.precision_reading_eq_iff_le_padicValInt`
