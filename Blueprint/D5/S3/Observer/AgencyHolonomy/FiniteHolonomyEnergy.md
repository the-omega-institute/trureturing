# Finite Holonomy Energy

## Abstract

Finite stable swap curvature aggregates into a faithful nonnegative energy.

**Theorem 1.1 (Finite Stable Holonomy Energy Bound).**

$$\begin{gathered}\forall K: \operatorname{Type}, \iota: \operatorname{Type}, [\operatorname{NormedField}(K)], [\operatorname{Fintype}(\iota)],\\{}a: K, r: \iota \to K, v: \iota \to K, \varepsilon: \mathbb{R},\\{}(0 \leq \varepsilon \land (\forall p: \iota, \left\lVert v(p) \right\rVert \leq 1) \land (\forall p: \iota, \left\lVert r(p) \right\rVert \leq \varepsilon)) \Rightarrow\\{}\operatorname{let} E := \operatorname{stableResidualHolonomyEnergy}(a, r, v),\\{}(0 \leq E \land\\{}E \leq \operatorname{card}_{\mathbb{R}}(\iota)^{2} \times (2 \times \left\lVert (a - 1) \right\rVert \times \varepsilon + 2 \times \varepsilon^{2})^{2} \land\\{}(E = 0 \iff \forall p, q: \iota, \operatorname{stableResidualSwapCurvature}(a, r(p), r(q), v(p), v(q)) = 0) \land\\{}(\varepsilon = 0 \Rightarrow E = 0)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy.finite_stable_holonomy_energy_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite carrier, assume every channel has norm at most one and every residual norm is bounded by a common nonnegative envelope. The stable residual holonomy energy is nonnegative and is at most the square of the carrier cardinality times the squared pairwise residual bound.

The energy is zero exactly when every ordered-pair stable residual swap curvature is zero, and a zero envelope forces zero energy. These claims concern only the finite unnormalized sum; they assert no residual decay, infinite-prime limit, or spectral-energy comparison.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy.finite_stable_holonomy_energy_bound`
- Dependency: [D5/S3/Observer/AgencyHolonomy/StableResidualSwapCurvatureBound](StableResidualSwapCurvatureBound.md)
