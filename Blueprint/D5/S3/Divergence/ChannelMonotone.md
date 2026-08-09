# Channel Monotonicity of Finite Classical KL Divergence

## Abstract

A strictly positive finite channel cannot increase finite real-valued classical KL divergence.

**Theorem 1.1 (A strictly positive finite channel does not increase classical KL divergence).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Nonempty}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to\mathbb{R}, W: X\to Y\to\mathbb{R},\\((\forall x: X, 0<p(x)) \land \sum_{x}p(x)=1) \Rightarrow\\((\forall x: X, 0<q(x)) \land \sum_{x}q(x)=1) \Rightarrow\\((\forall x: X, y: Y, 0<W(x, y)) \land (\forall x: X, \sum_{y}W(x, y)=1)) \Rightarrow\\D(Wp\Vert\Vert Wq) \le D(p\Vert\Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/ChannelMonotone.kl_divergence_channel_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X and Y be finite types, with X nonempty. Let p and q be strictly positive normalized real mass functions on X, and let W be a strictly positive stochastic kernel from X to Y, meaning that every row sums to one. These are exactly the hypotheses required by the wave-3 identity; nothing beyond them is assumed.

This theorem is a composition of repository results, not new divergence machinery. The wave-3 identity D5/S3/Divergence/ClassicalDPI.classical_dpi_identity supplies the exact decomposition of input divergence into output divergence plus an output-weighted sum of posterior divergences. The Grandmother theorem D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg supplies nonnegativity of each posterior divergence, and Finset.sum_nonneg combines those pointwise bounds.

The Grandmother theorem's premises are discharged, not assumed: each posterior is strictly positive and sums to one, proved directly from the definitions and positivity of the output mass. Its absolute-continuity premise is trivial because the second posterior is strictly positive.

This is the data-processing inequality that wave 11's D5/S3/Divergence/MarginalMonotone module explicitly did not claim. At the level of the data-processing operation, wave 11's first-coordinate marginalization is the special case of forgetting a coordinate. Its deterministic forgetting kernel has zero transition probabilities, so the wave-11 theorem is proved separately rather than by instantiating this theorem.

This is the finite real-valued klDivergence of ClassicalDPI, the repository's single source for the definition, not a measure-theoretic divergence. Mathlib's InformationTheory.klDiv_compProd_eq_add is not used, and no ENNReal/finite-sum bridge is established here.

The remaining limits are full-support requirements: strict positivity of the kernel and of both input distributions is required. Channels with zero transition probabilities and distributions with zero mass are outside this module's scope.

## References

- Truth anchor: `D5/S3/Divergence/ChannelMonotone.kl_divergence_channel_le`
- Dependency: [D5/S3/Divergence/ClassicalDPI](ClassicalDPI.md)
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](GrandmotherTheorem.md)
