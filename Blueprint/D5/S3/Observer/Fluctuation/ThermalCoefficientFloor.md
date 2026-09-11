# Thermal Coefficient Floor

## Abstract

The thermal response coefficient is bounded below by the inverse temperature, with no common floor on the mode frequencies.

**Theorem 1.1 (A hyperbolic estimate).**

$$\forall x \in \mathbb{R},\; 0 \leq x \Rightarrow \operatorname{sinh}\left(x\right) \leq x \cdot \operatorname{cosh}\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.sinh_le_self_mul_cosh_of_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference between the two sides vanishes at the origin and has derivative equal to the argument times the hyperbolic sine, which is nonnegative on the nonnegative axis. Monotonicity from a nonnegative derivative then gives the estimate. The pinned library carries the derivatives and the sign of the hyperbolic sine, but no inequality of this shape.

**Definition 1.2 (The hyperbolic cotangent).**

$$\forall x \in \mathbb{R},\; \operatorname{coth}\left(x\right) = \frac{\operatorname{cosh}\left(x\right)}{\operatorname{sinh}\left(x\right)}$$

*Formalization.* `D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.coth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quotient is taken in the real numbers, so it is totalized at the origin. Every statement below assumes a positive argument, where the denominator is positive and the quotient is the intended one.

**Lemma 1.3 (Companion: the product is at least one).**

$$\forall x \in \mathbb{R},\; 0 < x \Rightarrow 1 \leq x \cdot \operatorname{coth}\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.one_le_self_mul_coth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Clearing the positive denominator turns the claim into the estimate above.

**Lemma 1.4 (Companion: the cotangent dominates the reciprocal).**

$$\forall x \in \mathbb{R},\; 0 < x \Rightarrow \frac{1}{x} \leq \operatorname{coth}\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.inv_le_coth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same inequality divided by the positive argument. This is the form the coefficient bound consumes.

**Theorem 1.5 (The coefficient floor).**

$$\forall beta \in \mathbb{R}, hbar \in \mathbb{R}, nu \in \mathbb{R},\; 0 < beta \land 0 < hbar \land 0 < nu \Rightarrow \frac{1}{beta} \leq \frac{hbar \cdot nu}{2} \cdot \operatorname{coth}\left(\frac{beta \cdot hbar \cdot nu}{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.inv_le_thermal_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The right-hand side is the inverse temperature alone. Its proof uses only that this one frequency is positive; no quantity shared across frequencies enters. The two positive constants cancel exactly, which is why nothing about their size survives into the bound.

**Theorem 1.6 (The finite spectral form).**

$$\forall a, 0 < \operatorname{nu}\left(a\right) \land 0 \leq \operatorname{w}\left(a\right) \Rightarrow \frac{1}{beta} \cdot \sum_{a} \frac{\operatorname{w}\left(a\right)}{{\operatorname{nu}\left(a\right)}^{2}} \leq \sum_{a} \frac{hbar \cdot \operatorname{nu}\left(a\right)}{2} \cdot \operatorname{coth}\left(\frac{beta \cdot hbar \cdot \operatorname{nu}\left(a\right)}{2}\right) \cdot \frac{\operatorname{w}\left(a\right)}{{\operatorname{nu}\left(a\right)}^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.inv_mul_sum_le_thermal_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each mode carries its own positive frequency and a nonnegative weight, so the pointwise bound applies term by term over a finite index type. No summability hypothesis is needed and none is claimed; extending to a countable index would require convergence of both sides and is not addressed here.

The source states this bound together with a second one under a single hypothesis: a common positive floor below every frequency. Only the second bound uses that floor, and its coefficient displays it. The first bound, isolated here, holds under the weaker hypothesis that each frequency is positive in its own right.

Nothing here identifies the sum with a physical fluctuation. That identification is an equilibrium preparation statement and is a separate hypothesis; no canonical quantization, state preparation, or measurement rule is formalized in this module.

## References

- Truth anchor: `D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.coth`
- Truth anchor: `D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.inv_le_coth`
- Truth anchor: `D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.inv_le_thermal_coefficient`
- Truth anchor: `D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.inv_mul_sum_le_thermal_sum`
- Truth anchor: `D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.one_le_self_mul_coth`
- Truth anchor: `D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.sinh_le_self_mul_cosh_of_nonneg`
