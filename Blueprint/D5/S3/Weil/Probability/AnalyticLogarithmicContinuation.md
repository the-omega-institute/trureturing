# AnalyticLogarithmicContinuation

## Abstract

Classical analytic continuation preserves the actual scalar series and excludes zeros through analytic orders.

**Theorem 1.1 (All smaller radii have absolute convergence).**

$$\forall a \in \mathbb{N}\to\mathbb{C},\; \forall C \in \mathbb{R},\; \left(\forall n \in \mathbb{N},\; \left\lVert \operatorname{a}\left(n\right) \right\rVert \le C \cdot \left(n + 1\right)^{2}\right) \Rightarrow \left(\forall r \in \mathbb{R}_{\geq0},\; r < 1 \Rightarrow \operatorname{Summable}\left((n:\mathbb{N}\mapsto\left\lVert \operatorname{a}\left(n\right) \right\rVert \cdot r^{n})\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/AnalyticLogarithmicContinuation.quadratic_coefficients_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A bound on every coefficient is compared with polynomial-weighted geometric series, including radius zero.

**Theorem 1.2 (Analyticity of the original scalar sum).**

$$\forall a \in \mathbb{N}\to\mathbb{C},\; \left(\forall r \in \mathbb{R}_{\geq0},\; r < 1 \Rightarrow \operatorname{Summable}\left((n:\mathbb{N}\mapsto\left\lVert \operatorname{a}\left(n\right) \right\rVert \cdot r^{n})\right)\right) \Rightarrow \operatorname{AnalyticOnNhd}\left(\mathbb{C}, (z:\mathbb{C}\mapsto\sum_{n=0}^{\infty}\operatorname{a}\left(n\right) \cdot z^{n}), \operatorname{ball}\left(0, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/AnalyticLogarithmicContinuation.scalar_series_analytic_unit_disk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing formal scalar-series radius and analyticity theorems apply to the actual coefficient sum throughout the unit disk.

**Theorem 1.3 (A nonzero analytic solution stays nonzero).**

$$\forall U \in \operatorname{Set}\left(\mathbb{C}\right),\; \forall f \in \mathbb{C}\to\mathbb{C},\; \forall g \in \mathbb{C}\to\mathbb{C},\; \forall p \in \mathbb{C},\; \operatorname{IsOpen}\left(U\right) \Rightarrow \left(\operatorname{IsPreconnected}\left(U\right) \Rightarrow \left(\operatorname{AnalyticOnNhd}\left(\mathbb{C}, f, U\right) \Rightarrow \left(\operatorname{AnalyticOnNhd}\left(\mathbb{C}, g, U\right) \Rightarrow \left(p \in U \Rightarrow \left(\operatorname{f}\left(p\right) \ne 0 \Rightarrow \left(\left(\forall z \in U,\; \operatorname{deriv}\left(f, z\right) = \operatorname{g}\left(z\right) \cdot \operatorname{f}\left(z\right)\right) \Rightarrow \left(\forall z \in U,\; \operatorname{f}\left(z\right) \ne 0\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/AnalyticLogarithmicContinuation.analytic_linear_ode_zero_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a putative zero, differentiation lowers finite analytic order while multiplication by an analytic coefficient cannot. Connectedness and the nonzero initial value exclude infinite order.

**Theorem 1.4 (A local identity gives a global nonvanishing result).**

$$\forall U \in \operatorname{Set}\left(\mathbb{C}\right),\; \forall f \in \mathbb{C}\to\mathbb{C},\; \forall g \in \mathbb{C}\to\mathbb{C},\; \forall p \in \mathbb{C},\; \operatorname{IsOpen}\left(U\right) \Rightarrow \left(\operatorname{IsPreconnected}\left(U\right) \Rightarrow \left(\operatorname{AnalyticOnNhd}\left(\mathbb{C}, f, U\right) \Rightarrow \left(\operatorname{AnalyticOnNhd}\left(\mathbb{C}, g, U\right) \Rightarrow \left(p \in U \Rightarrow \left(\operatorname{f}\left(p\right) \ne 0 \Rightarrow \left((\forall^{f} z \in \mathcal{N}(p), \operatorname{deriv}\left(f, z\right) = \operatorname{g}\left(z\right) \cdot \operatorname{f}\left(z\right)) \Rightarrow \left(\left(\forall z \in U,\; \operatorname{deriv}\left(f, z\right) = \operatorname{g}\left(z\right) \cdot \operatorname{f}\left(z\right)\right) \land \left(\forall z \in U,\; \operatorname{f}\left(z\right) \ne 0\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/AnalyticLogarithmicContinuation.local_logarithmic_equation_zero_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The analytic identity theorem extends the original derivative equation from a germ. Neither a global logarithm nor an already zero-free domain is supplied.

## References

- Truth anchor: `D5/S3/Weil/Probability/AnalyticLogarithmicContinuation.analytic_linear_ode_zero_free`
- Truth anchor: `D5/S3/Weil/Probability/AnalyticLogarithmicContinuation.local_logarithmic_equation_zero_free`
- Truth anchor: `D5/S3/Weil/Probability/AnalyticLogarithmicContinuation.quadratic_coefficients_summable`
- Truth anchor: `D5/S3/Weil/Probability/AnalyticLogarithmicContinuation.scalar_series_analytic_unit_disk`
