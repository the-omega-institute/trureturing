# Finite-Window Exponential Agreement

## Abstract

Hyperbolic budget tubes force uniform exponential agreement on every fixed window.

**Theorem 1.1 (Every fixed window agrees at the hyperbolic exponential rate).**

$$\begin{aligned}\forall a, R_{*}, T \in \mathbb{R},\\0 < a \land 0 \le R_{*} \land 0 \le T \land \operatorname{BoundedLocalCoshLaw}(a, R_{*}) \Rightarrow\\(\forall L, 0 < L, T < 2 \cdot L \Rightarrow \forall t, \left|t\right| \le T \Rightarrow \left|\operatorname{DeltaH}(L, t)\right| \le \frac{R_{*}}{\operatorname{sinh}(a \cdot L)^{2}} \cdot \operatorname{cosh}(a \cdot T)) \land\\(\exists C \geq 0, \operatorname{eventually}(L, \forall t, \left|t\right| \le T \Rightarrow \left|\operatorname{DeltaH}(L, t)\right| \le C \cdot \operatorname{exp}(-2 \cdot a \cdot L))) \land (a = \frac{1}{2} \Rightarrow \exists C \geq 0, \operatorname{eventually}(L, \forall t, \left|t\right| \le T \Rightarrow \left|\operatorname{DeltaH}(L, t)\right| \le C \cdot \operatorname{exp}(-L))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/FiniteWindowExponentialAgreement.finite_window_exponential_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypotheses are the same bounded-correlation and local cosh difference law used by the frozen hyperbolic budget tube. Positivity of the scale and resolvent excludes the totalized sinh denominator at zero.

The two tube walls bound both signs of the budget deviation by R-star divided by sinh(aL) squared. Monotonicity of cosh in absolute value then makes the bound independent of time on the fixed window.

For sufficiently large L, exp(aL)/4 is at most sinh(aL). This gives one time-independent constant multiplying exp(-2aL); when a is one half, the exponent simplifies exactly to -L.

## References

- Truth anchor: `D5/S3/Weil/FiniteWindowExponentialAgreement.finite_window_exponential_agreement`
- Dependency: [D5/S3/Weil/Budget/ExplicitHyperbolicDegreeThreshold](Budget/ExplicitHyperbolicDegreeThreshold.md)
- Dependency: [D5/S3/Weil/ZetaGamma/HyperbolicBudgetTube](ZetaGamma/HyperbolicBudgetTube.md)
