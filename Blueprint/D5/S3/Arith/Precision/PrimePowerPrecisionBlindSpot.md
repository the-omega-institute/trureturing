# Prime-Power Precision Blind Spot

## Abstract

For a fixed prime, the valuation of a nonzero integer difference exactly controls both the blind residue precisions and the first precision that separates it.

**Theorem 1.1 (The valuation controls agreement and the first distinguishing precision).**

$$\begin{gathered}\forall p, k \in \mathbb{N},\\{}x, y \in \mathbb{Z},\\{}(\operatorname{Prime}\left(p\right) \land x \neq y) \Rightarrow ((\operatorname{precisionReading}\left(p, k, x\right) = \operatorname{precisionReading}\left(p, k, y\right)) \iff k \leq \operatorname{padicValInt}\left(p, x - y\right)) \land\\{}(\operatorname{firstDistinguishingPrecision}\left(p, x, y\right) = \operatorname{padicValInt}\left(p, x - y\right) + 1).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Precision/PrimePowerPrecisionBlindSpot.prime_power_precision_blind_spot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a prime p, a natural precision k, and distinct integers x and y. The precision reading is the residue modulo p^k. The two readings agree exactly when k does not exceed the p-adic valuation of x - y.

The named firstDistinguishingPrecision is the source's kappa_p(x,y): the least positive precision whose readings differ. Its value is exactly one more than that same valuation.

## References

- Truth anchor: `D5/S3/Arith/Precision/PrimePowerPrecisionBlindSpot.prime_power_precision_blind_spot`
- Dependency: [D5/S3/Arith/Congruence/PadicPrecisionBlindSpot](../Congruence/PadicPrecisionBlindSpot.md)
