# Marginal Monotonicity of Finite Classical KL Divergence

## Abstract

Taking the first-coordinate marginal cannot increase finite real-valued classical KL divergence.

**Theorem 1.1 (The first-coordinate marginal does not increase finite classical KL divergence).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p, q: \iota\times\kappa\to \mathbb{R},\\(\forall i, j, 0<p(i,j) \land 0<q(i,j)) \Rightarrow\\D(p_{\iota}\Vert\Vert q_{\iota}) \le D(p\Vert\Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MarginalMonotone.kl_divergence_marginal_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let iota and kappa be finite types, and let p and q be strictly positive real functions on their product. Only strict positivity of p and q is assumed; no normalization of either joint function is assumed.

This theorem is a composition of two repository results. The wave-10 chain rule D5/S3/Divergence/ChainRule.kl_divergence_chain_rule supplies the exact decomposition of joint divergence into the first-coordinate marginal divergence plus a marginal-weighted sum of conditional divergences. The Grandmother theorem D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg supplies nonnegativity of each conditional divergence, and Finset.sum_nonneg combines those pointwise bounds.

The Grandmother theorem's normalization premises are discharged, not assumed: for every first coordinate, both conditionals sum to one, proved directly from the definitions. Its absolute-continuity premise is trivial here because both conditionals are strictly positive. The empty second coordinate is handled explicitly, so the theorem carries no Nonempty hypothesis.

This is the finite real-valued klDivergence of ClassicalDPI, the repository's single source for the definition, not a measure-theoretic divergence. Mathlib's InformationTheory.klDiv_compProd_eq_add is not used, and no ENNReal/finite-sum bridge is established here.

This module claims monotonicity only under taking the first-coordinate marginal; it does not claim a general data-processing inequality over arbitrary channels.

## References

- Truth anchor: `D5/S3/Divergence/MarginalMonotone.kl_divergence_marginal_le`
- Dependency: [D5/S3/Divergence/ChainRule](ChainRule.md)
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](GrandmotherTheorem.md)
