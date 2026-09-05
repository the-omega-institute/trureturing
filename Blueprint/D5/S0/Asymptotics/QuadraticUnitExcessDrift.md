# Quadratic-Unit Excess Drift

## Abstract

The reciprocal excess identity determines the quadratic-unit drift slope exactly.

**Theorem 1.1 (The excess identity fixes the drift and its reciprocal zero criterion).**

$$\begin{aligned}\forall x>0, \operatorname{V}\left(x\right) + \operatorname{V}\left(x^{-1}\right) = \frac{\pi}{6} \times {x + x^{-1}} - \frac{\pi}{2} + \operatorname{s}\left(x\right) \times \log x,\\\forall x>0, \operatorname{s}\left(x^{-1}\right) = -\operatorname{s}\left(x\right),\\epsilon>1, epsilon + epsilon^{-1} = 2\times t, \operatorname{V}\left(epsilon\right) + \operatorname{V}\left(epsilon^{-1}\right) = 0 \Rightarrow\\\operatorname{s}\left(epsilon\right) = -\frac{\pi \times {2\times t - 3}}{6 \times \log epsilon} \land \forall x>0, \operatorname{s}\left(x^{-1}\right) = \operatorname{s}\left(x\right) \Rightarrow \operatorname{s}\left(x\right) = 0.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/QuadraticUnitExcessDrift.quadratic_unit_excess_drift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the reciprocal excess law for positive x and the drift antisymmetry s(x inverse) = -s(x). At a real unit epsilon greater than one, suppose epsilon plus its inverse is 2t and the paired V values cancel. Substitution into the excess law and division by the positive log epsilon give the displayed closed slope.

If a reciprocal orbit also preserves the drift, preservation and antisymmetry give s(x) = -s(x), hence s(x) = 0. This is the exact algebraic content needed by the norm-minus-one criterion.

The source statement was tightened by making epsilon > 1 explicit. Lean's Real.log is total and equals zero at one, so this condition is needed for the division in the slope formula. The analytic construction of V and the Cesaro-Abel convergence assertions are inputs, not re-proved by this algebraic closure.

## References

- Truth anchor: `D5/S0/Asymptotics/QuadraticUnitExcessDrift.quadratic_unit_excess_drift`
