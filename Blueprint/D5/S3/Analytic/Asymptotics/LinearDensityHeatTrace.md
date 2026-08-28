# Linear Density Heat Trace

## Abstract

Linear counting density gives the reciprocal leading term of the spectral heat trace.

**Theorem 1.1 (Linear density determines the leading heat-trace term).**

$$\begin{gathered}\forall \lambda: \mathbb{N} \to \mathbb{R}, c \in \mathbb{R},\\(\forall n \in \mathbb{N}, 0 < \lambda\left(n\right)) \land \operatorname{StrictMono}(\lambda) \land\\(\forall u \in \mathbb{R}, \operatorname{Finite}(\{n \in \mathbb{N} \mid \lambda\left(n\right) \leq u\})) \land \left(N_{\lambda}\right)\left(u\right) - cu = \operatorname{O}(1)_{u\to\infty} \Rightarrow\\\left(Theta_{\lambda}\right)\left(t\right) - c/t = \operatorname{O}(1)_{t\to0^{+}},\\\text{where}\quad\left(N_{\lambda}\right)\left(u\right) := \operatorname{card}(\{n \in \mathbb{N} \mid \lambda\left(n\right) \leq u\}),\quad\left(Theta_{\lambda}\right)\left(t\right) := \sum_{n=0}^{\infty} \exp{-t\lambda\left(n\right)}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/LinearDensityHeatTrace.linear_density_heat_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let lambda be a positive strictly increasing real spectrum. For every real cutoff u, its sublevel set is required to be finite, so N_lambda(u) is the genuine cardinality of the set of indices with lambda(n) at most u. If N_lambda(u)-c u is bounded at infinity, then the residual of the exponential heat trace after subtracting c/t is bounded as t approaches zero through positive values.

The proof first upgrades the eventual counting residual bound to a uniform bound on the positive half-line by monotonicity of finite sublevel cardinalities. The linear exponential moment and the bounded residual against the exponential kernel are therefore integrable.

For each spectral value, its exponential term is written as the integral of t exp(-t u) over u at least lambda(n). Mathlib's nonnegative Tonelli theorem exchanges the integral and infinite sum. Pointwise, finiteness of the counting set identifies the sum of indicators with N_lambda(u). This proves both summability of the heat trace and the counting-integral identity rather than assuming that bridge.

Pinned Mathlib's Gamma integral evaluates the linear moment as 1/t^2. The residual integral has norm at most K/t, so multiplication by t leaves the uniform bound K. The result uses no Riemann hypothesis or other conjectural input and makes no lower-order limit claim.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/LinearDensityHeatTrace.linear_density_heat_trace`
