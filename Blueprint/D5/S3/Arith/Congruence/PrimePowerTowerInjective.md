# Integer Separation by the Prime-Power Tower

## Abstract

Positive prime-power reductions separate integers, and equality of their complete reduction towers is exactly integer equality.

**Theorem 1.1 (Positive prime-power reductions determine an integer).**

$$\begin{gathered}\forall p \in \mathbb{N},\\{}\operatorname{Prime}\left(p\right) \Rightarrow \operatorname{Injective}\left(\operatorname{precisionTower}\left(p\right) : \mathbb{Z} \to \prod_{k \in \mathbb{N}} \operatorname{ZMod}\left(p^{k + 1}\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PrimePowerTowerInjective.precision_tower_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a prime p. The precision tower sends an integer x to the family whose coordinate k is the residue of x modulo p^(k + 1). The shift starts the tower at the first positive precision p^1 and omits the trivial exponent-zero quotient.

If two distinct integers had the same tower, let v be the p-adic valuation of their difference. Equality of coordinate v would make their precision-(v + 1) readings equal, while the preceding least-distinguishing-precision theorem says that this is exactly a precision where they differ. Thus every tower collision is an integer equality.

**Proposition 1.2 (Tower equality is exactly integer equality).**

$$\begin{gathered}\forall p \in \mathbb{N},\\{}x, y \in \mathbb{Z},\\{}\operatorname{Prime}\left(p\right) \Rightarrow (\operatorname{precisionTower}\left(p, x\right) = \operatorname{precisionTower}\left(p, y\right) \iff x = y).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PrimePowerTowerInjective.precision_tower_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed prime, two integers have identical families of reductions modulo every positive power of that prime exactly when the integers themselves are equal.

The forward direction is the injectivity of the complete precision tower. The reverse direction follows because equal integers have equal reductions in every coordinate.

## References

- Truth anchor: `D5/S3/Arith/Congruence/PrimePowerTowerInjective.precision_tower_eq_iff`
- Truth anchor: `D5/S3/Arith/Congruence/PrimePowerTowerInjective.precision_tower_injective`
- Dependency: [D5/S3/Arith/Congruence/PadicPrecisionBlindSpot](PadicPrecisionBlindSpot.md)
