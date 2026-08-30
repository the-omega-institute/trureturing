# Simple-Zero No-Bifurcation

## Abstract

Completed reflection keeps a simple critical-line zero on the line, so an off-line birth requires a multiple zero.

**Theorem 1.1 (A simple reflected zero has no off-line bifurcation).**

$$\forall F: \mathbb{R} \to \mathbb{C} \to \mathbb{C}, d_{tau}: \mathbb{R} \to \mathbb{C} \to \operatorname{ContinuousLinearMap}(\mathbb{R}, \mathbb{R}, \mathbb{C}), d_{s}: \mathbb{R} \to \mathbb{C} \to \mathbb{C},\\{}tau_{0}\in \mathbb{R}, s_{0}\in \mathbb{C},\ \forall tau\in \mathbb{R}, s\in \mathbb{C},\ \operatorname{F}(tau, \operatorname{mirror}(s)) = \overline{\operatorname{F}(tau, s)} \land\\{}\operatorname{EventuallyAt}({tau, s}, \operatorname{nhds}({tau_{0}, s_{0}}), \operatorname{HasFDerivAt}(\operatorname{timeSlice}(F, s), \operatorname{d_{tau}}(tau, s), tau)) \land \operatorname{EventuallyAt}({tau, s}, \operatorname{nhds}({tau_{0}, s_{0}}), \operatorname{HasDerivAt}(\operatorname{spaceSlice}(F, tau), \operatorname{d_{s}}(tau, s), s)) \land\\{}\operatorname{ContinuousAt}({tau, s}\mapsto\operatorname{d_{tau}}(tau, s), {tau_{0}, s_{0}}) \land \operatorname{ContinuousAt}({tau, s}\mapsto\operatorname{d_{s}}(tau, s) \operatorname{smul}(\operatorname{id}(\mathbb{C})), {tau_{0}, s_{0}}) \Rightarrow\\{}((\operatorname{F}(tau_{0}, s_{0}) = 0 \land \operatorname{d_{s}}(tau_{0}, s_{0}) \neq 0 \land \Re(s_{0}) = criticalAbscissa) \Rightarrow \operatorname{EventuallyAt}({tau, s}, \operatorname{nhds}({tau_{0}, s_{0}}), \operatorname{F}(tau, s) = 0 \Rightarrow \Re(s) = criticalAbscissa)) \land\\{}((\Re(s_{0}) = criticalAbscissa \land \exists tau: \mathbb{N} \to \mathbb{R}, s: \mathbb{N} \to \mathbb{C},\ \operatorname{Tendsto}(tau, \operatorname{atTop}(\mathbb{N}), \operatorname{nhds}(tau_{0})) \land \operatorname{Tendsto}(s, \operatorname{atTop}(\mathbb{N}), \operatorname{nhds}(s_{0})) \land\\{}\forall n\in \mathbb{N},\ \operatorname{F}(tau_{n}, s_{n}) = 0 \land \Re(s_{n}) \neq criticalAbscissa) \Rightarrow \operatorname{F}(tau_{0}, s_{0}) = 0 \land \operatorname{d_{s}}(tau_{0}, s_{0}) = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/SimpleZeroNoBifurcation.simple_zero_no_bifurcation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The family parameter is real and the zero coordinate is complex. The public assumptions retain completed reflection, both local partial derivatives, and continuity of their real-linear fields.

At a simple critical-line zero, the bivariate implicit-function theorem constructs a unique local zero branch. Reflecting that branch gives another nearby zero branch, so uniqueness makes every nearby zero reflection-fixed and hence critical-line valued.

The second public conjunct considers convergent sequences of off-line zeros. Joint continuity supplies the limiting zero; if its complex derivative were nonzero, the first conjunct would put the sequence on the critical line eventually, a contradiction.

Repository search found no exact frozen owner. The construction imports the canonical reflection ledger and directly applies Mathlib's bivariate implicit-function theorem and complex-to-real derivative.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/SimpleZeroNoBifurcation.simple_zero_no_bifurcation`
- Dependency: [D5/S3/Weil/ReflectionLedger](../../Weil/ReflectionLedger.md)
