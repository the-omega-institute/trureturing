# Escape Threshold

## Abstract

Past three plus the square root of thirteen, one conjugate step cannot be undone by subtracting a digit.

The threshold is two divided by the excess of the conjugate modulus over one, which in closed form is three plus the square root of thirteen. Past it the image of one step is strictly farther from the origin than its source, for every digit between zero and two.

**Theorem 1.1 (The escape threshold is a threshold).**

$$\left(\left|\mathit{betaThirteenConjugate}\right| - 1\right) \cdot \mathit{escapeThreshold} = 2 \land \left(\forall x \in R, d \in R,\; \mathit{escapeThreshold} < \left|x\right| \Rightarrow \left|x\right| < \left|\mathit{betaThirteenConjugate} \cdot x - d\right|\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisotFrontier/EscapeThreshold.escape_threshold_is_a_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the general half of the coefficient-growth argument. The other half is exhibiting one point of the orbit past the threshold; measurement puts the conjugate orbit exactly at the threshold on the third step and one beyond it on the fourth, but that is not proved here.

## References

- Truth anchor: `D5/S0/Tower/NonPisotFrontier/EscapeThreshold.escape_threshold_is_a_threshold`
- Dependency: [D5/S0/Tower/NonPisotFrontier/ConjugateBridge](ConjugateBridge.md)
