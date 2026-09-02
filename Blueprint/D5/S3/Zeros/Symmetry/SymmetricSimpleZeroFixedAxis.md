# Symmetric Simple Zero Fixed Axis

## Abstract

A symmetric simple zero stays fixed by completed reflection along its unique local continuation.

**Theorem 1.1 (A symmetric simple zero remains reflection-fixed).**

$$\forall F: \mathbb{R} \to \mathbb{C} \to \mathbb{C}, d_{tau}: \mathbb{R} \to \mathbb{C} \to \operatorname{ContinuousLinearMap}(\mathbb{R}, \mathbb{R}, \mathbb{C}), d_{s}: \mathbb{R} \to \mathbb{C} \to \mathbb{C},\\{}tau_{0}\in \mathbb{R}, s_{0}\in \mathbb{C},\ (\forall tau \in \mathbb{R}, s \in \mathbb{C},\; \operatorname{F}(tau, \operatorname{mirror}(s)) = \overline{\operatorname{F}(tau, s)}) \land\\{}\operatorname{EventuallyAt}({tau, s}, \operatorname{nhds}({tau_{0}, s_{0}}), \operatorname{HasFDerivAt}(\operatorname{timeSlice}(F, s), \operatorname{d_{tau}}(tau, s), tau)) \land \operatorname{EventuallyAt}({tau, s}, \operatorname{nhds}({tau_{0}, s_{0}}), \operatorname{HasDerivAt}(\operatorname{spaceSlice}(F, tau), \operatorname{d_{s}}(tau, s), s)) \land\\{}\operatorname{ContinuousAt}({tau, s}\mapsto\operatorname{d_{tau}}(tau, s), {tau_{0}, s_{0}}) \land \operatorname{ContinuousAt}({tau, s}\mapsto\operatorname{d_{s}}(tau, s) \operatorname{smul}(\operatorname{id}(\mathbb{C})), {tau_{0}, s_{0}}) \Rightarrow\\{}(\operatorname{F}(tau_{0}, s_{0}) = 0 \land \operatorname{d_{s}}(tau_{0}, s_{0}) \neq 0 \land \operatorname{mirror}(s_{0}) = s_{0}) \Rightarrow \operatorname{EventuallyAt}({tau, s}, \operatorname{nhds}({tau_{0}, s_{0}}), \operatorname{F}(tau, s) = 0 \Rightarrow (\operatorname{mirror}(s) = s \land \Re(s) = criticalAbscissa)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/SymmetricSimpleZeroFixedAxis.symmetric_simple_zero_fixed_axis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the reflected function family, both local derivative fields, and their continuity assumptions on the real-complex product.

The imported simple-zero theorem puts every nearby zero on the critical line. The canonical reflection equivalence then makes each such zero fixed, so both conclusions are public.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/SymmetricSimpleZeroFixedAxis.symmetric_simple_zero_fixed_axis`
- Dependency: [D5/S3/Zeros/Symmetry/SimpleZeroNoBifurcation](SimpleZeroNoBifurcation.md)
