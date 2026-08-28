# P-Adic Observation Distance

## Abstract

The first unequal prime-power reading induces the p-adic distance formula.

**Theorem 1.1 (Observation distance equals the p-adic valuation scale).**

$$\begin{gathered}\forall p \in \mathbb{N},\\{}x, y \in \mathbb{Z},\\{}(\operatorname{Prime}\left(p\right) \land x \neq y) \Rightarrow \operatorname{observationDistance}\left(p, x, y\right) = p^{-\operatorname{padicValInt}\left(p, x - y\right)}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PadicObservationDistance.observation_distance_eq_padic_valuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p, the precision-k reading of an integer is its residue modulo p^k. The observation distance between distinct integers is p raised to one minus the first precision at which those readings differ.

The frozen precision theorem identifies that first distinguishing precision with one plus the p-adic valuation of x - y. Subtracting it from one gives the negative valuation, yielding the displayed distance identity.

## References

- Truth anchor: `D5/S3/Arith/Congruence/PadicObservationDistance.observation_distance_eq_padic_valuation`
- Dependency: [D5/S3/Arith/Congruence/PadicPrecisionBlindSpot](PadicPrecisionBlindSpot.md)
