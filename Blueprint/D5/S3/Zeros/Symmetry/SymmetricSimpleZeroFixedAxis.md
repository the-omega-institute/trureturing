# Symmetric Simple Zero Fixed Axis

## Abstract

A symmetric simple zero has a public unique local continuation fixed by completed reflection.

**Theorem 1.1 (A symmetric simple zero remains reflection-fixed).**

$$\forall F: \mathbb{R} \to \mathbb{C} \to \mathbb{C}, d_{tau}: \mathbb{R} \to \mathbb{C} \to \operatorname{ContinuousLinearMap}(\mathbb{R}, \mathbb{R}, \mathbb{C}), d_{s}: \mathbb{R} \to \mathbb{C} \to \mathbb{C},\\{}tau_{0}\in \mathbb{R}, s_{0}\in \mathbb{C},\ (\forall tau \in \mathbb{R}, s \in \mathbb{C},\; \operatorname{F}(tau, \operatorname{mirror}(s)) = \overline{\operatorname{F}(tau, s)}) \land\\{}\operatorname{EventuallyAt}({tau, s}, \operatorname{nhds}({tau_{0}, s_{0}}), \operatorname{HasFDerivAt}(\operatorname{timeSlice}(F, s), \operatorname{d_{tau}}(tau, s), tau)) \land \operatorname{EventuallyAt}({tau, s}, \operatorname{nhds}({tau_{0}, s_{0}}), \operatorname{HasDerivAt}(\operatorname{spaceSlice}(F, tau), \operatorname{d_{s}}(tau, s), s)) \land\\{}\operatorname{ContinuousAt}({tau, s}\mapsto\operatorname{d_{tau}}(tau, s), {tau_{0}, s_{0}}) \land \operatorname{ContinuousAt}({tau, s}\mapsto\operatorname{d_{s}}(tau, s) \operatorname{smul}(\operatorname{id}(\mathbb{C})), {tau_{0}, s_{0}}) \Rightarrow\\{}(\operatorname{F}(tau_{0}, s_{0}) = 0 \land \operatorname{d_{s}}(tau_{0}, s_{0}) \neq 0 \land \operatorname{mirror}(s_{0}) = s_{0}) \Rightarrow\\{}\exists delta: \mathbb{R}, 0 < delta \land\\{}\exists epsilon: \mathbb{R}, 0 < epsilon \land\\{}\exists rho: \mathbb{R} \to \mathbb{C},\\{}\operatorname{rho}(tau_{0}) = s_{0} \land \operatorname{ContinuousAt}(rho, tau_{0}) \land\\{}(\forall kappa: \mathbb{R}, \left|kappa - tau_{0}\right| < delta \Rightarrow \operatorname{rho}(kappa) \in \operatorname{ball}(s_{0}, epsilon)) \land\\{}(\forall kappa: \mathbb{R}, \left|kappa - tau_{0}\right| < delta \Rightarrow \operatorname{F}(kappa, \operatorname{rho}(kappa)) = 0) \land\\{}(\forall kappa: \mathbb{R}, \left|kappa - tau_{0}\right| < delta \Rightarrow \forall s: \mathbb{C}, s \in \operatorname{ball}(s_{0}, epsilon) \Rightarrow \operatorname{F}(kappa, s) = 0 \Rightarrow s = \operatorname{rho}(kappa)) \land\\{}(\forall kappa: \mathbb{R}, \left|kappa - tau_{0}\right| < delta \Rightarrow \operatorname{mirror}(\operatorname{rho}(kappa)) = \operatorname{rho}(kappa)) \land\\{}(\forall kappa: \mathbb{R}, \left|kappa - tau_{0}\right| < delta \Rightarrow \Re(\operatorname{rho}(kappa)) = criticalAbscissa).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/SymmetricSimpleZeroFixedAxis.symmetric_simple_zero_fixed_axis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement exposes positive parameter and zero radii together with the implicit-function continuation through the base zero.

The continuation is continuous at the base parameter, is the unique zero in the displayed ball, and remains fixed by completed reflection on the whole displayed parameter interval.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/SymmetricSimpleZeroFixedAxis.symmetric_simple_zero_fixed_axis`
- Dependency: [D5/S3/Zeros/Symmetry/SimpleZeroNoBifurcation](SimpleZeroNoBifurcation.md)
