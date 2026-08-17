# Golden Critical-Band Scaling

## Abstract

Golden-square scaling maps the second-order band exactly onto a band containing one half.

**Theorem 1.1 (The scaled golden band contains the critical midpoint).**

$$\varphi^{2}\times(\frac{1}{2\times\varphi^{3}}, \frac{1}{\varphi^{3}}) = (\frac{1}{2\times\varphi}, \frac{1}{\varphi}) \land \frac{1}{2} \in (\frac{1}{2\times\varphi}, \frac{1}{\varphi}).$$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/Powers/GoldenCriticalBandScaling.golden_critical_band_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's Set.image_mul_left_Ioo theorem gives the image of an open interval under multiplication by a positive scalar. Applying it to the positive scalar phi squared reduces the image claim to cancellation of nonzero powers of phi.

The strict bounds 1 < phi < 2 then place one half inside the resulting open interval.

Scope: this formalizes only the first sentence of remark 6.20, namely the golden-square interval map and its coverage of one half. It makes no claim about zeta zeros, Z_qc singularities, structural zeros, analytic control, or later pullback consequences in the source atom.

## References

- Truth anchor: `D5/S0/Carrier/Powers/GoldenCriticalBandScaling.golden_critical_band_scaling`
