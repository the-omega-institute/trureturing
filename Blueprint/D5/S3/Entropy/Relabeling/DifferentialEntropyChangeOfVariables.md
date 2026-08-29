# Differential Entropy Change of Variables

## Abstract

Differential entropy changes by the expected logarithm of the absolute Jacobian.

**Theorem 1.1 (A differentiable equivalence contributes its log-Jacobian correction).**

$$\begin{gathered}\forall n\in \mathbb{N}, p: \mathbb{R}^{n} \to \mathbb{R},\\{}f: \operatorname{Equiv}(\mathbb{R}^{n}, \mathbb{R}^{n}), A: \mathbb{R}^{n} \to \operatorname{ContinuousLinearMap}(\mathbb{R}, \mathbb{R}^{n}, \mathbb{R}^{n}),\\{}(\forall x\in \mathbb{R}^{n}, 0 \leq p(x)) \land\\{}\int_{\mathbb{R}^{n}} (p(x)) dx = 1 \land\\{}\operatorname{Integrable}((x \mapsto p(x) \cdot \operatorname{log}(p(x)))) \land\\{}\operatorname{Integrable}((x \mapsto p(x) \cdot \operatorname{log}(\lvert\operatorname{det}(A(x))\rvert))) \land\\{}(\forall x\in \mathbb{R}^{n}, \operatorname{HasFDerivAt}(f, A(x), x)) \land\\{}(\forall x\in \mathbb{R}^{n}, 0 < \lvert\operatorname{det}(A(x))\rvert)\\{}\Rightarrow \operatorname{let}(J(x) := \lvert\operatorname{det}(A(x))\rvert,\\{}q(y) := \frac{p(\operatorname{symm}(f, y))}{J(\operatorname{symm}(f, y))},\\{}h(r) := -\int_{\mathbb{R}^{n}} (r(x) \cdot \operatorname{log}(r(x))) dx)\;\\{}\operatorname{Integrable}((y \mapsto q(y) \cdot \operatorname{log}(q(y)))) \land\\{}h(q) = h(p) + \int_{\mathbb{R}^{n}} (p(x) \cdot \operatorname{log}(J(x))) dx \land\\{}(\forall c\in \mathbb{R}, 0 < c \Rightarrow (\forall x\in \operatorname{support}(p), J(x) = c) \Rightarrow \int_{\mathbb{R}^{n}} (p(x) \cdot \operatorname{log}(J(x))) dx = \operatorname{log}(c)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Relabeling/DifferentialEntropyChangeOfVariables.differential_entropy_change_of_variables` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the real vector space R^n. A nonnegative unit-mass density p, a differentiable equivalence f, its derivative A, and an everywhere-positive absolute determinant construct J(x) = |det A(x)| and the transformed density q(y) = p(f^{-1}(y))/J(f^{-1}(y)).

Integrability of p log p expresses finite source differential entropy. Integrability of p log J expresses finite absolute expected log-Jacobian. The transformed entropy integrand is integrable, and h(q) equals h(p) plus the density-weighted integral of log J.

If J is the positive constant c on the support of p, normalization makes the correction exactly log c. The qualitative observation that the correction usually depends on both the map and the distribution is not universalized.

The proof directly applies Mathlib's Jacobian change-of-variables theorem and its integrability equivalence. The remaining pointwise identity is log(p/J) = log p - log J, with the zero-density case handled separately.

## References

- Truth anchor: `D5/S3/Entropy/Relabeling/DifferentialEntropyChangeOfVariables.differential_entropy_change_of_variables`
- Dependency: [D5/S3/Entropy/Relabeling/InjectiveInvariance](InjectiveInvariance.md)
