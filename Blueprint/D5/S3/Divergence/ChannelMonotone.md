# Channel Monotonicity of Finite Classical KL Divergence

## Abstract

A strictly positive finite channel cannot increase finite real-valued classical KL divergence.

**Theorem 1.1 (A strictly positive finite channel does not increase classical KL divergence).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Nonempty}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to\mathbb{R}, W: X\to Y\to\mathbb{R},\\((\forall x: X, 0<p(x)) \land \sum_{x}p(x)=1) \Rightarrow\\((\forall x: X, 0<q(x)) \land \sum_{x}q(x)=1) \Rightarrow\\((\forall x: X, y: Y, 0<W(x, y)) \land (\forall x: X, \sum_{y}W(x, y)=1)) \Rightarrow\\D(Wp\Vert\Vert Wq) \le D(p\Vert\Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/ChannelMonotone.kl_divergence_channel_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X and Y be finite types, with X nonempty. Let p and q be strictly positive normalized real mass functions on X, and let W be a strictly positive stochastic kernel from X to Y, meaning that every row sums to one. These are exactly the hypotheses required by D5/S3/Divergence/DpiDefect.dpi_defect_nonneg; nothing beyond them is assumed.

This module restates D5/S3/Divergence/DpiDefect.dpi_defect_nonneg in inequality form. The proof of the mathematical content lives in DpiDefect. ChannelMonotone only converts its nonnegative defect conclusion into the equivalent output-at-most-input inequality.

This module is a redundant re-proof: the same proposition was already frozen as D5/S3/Divergence/DpiDefect.dpi_defect_nonneg before this module was deposited. The theorem remains true and machine-verified; the redundancy lies in this module, not in the mathematics. It is retained, rather than removed, only because the frozen ledger currently has no revoke writer (issue #1030); removal is the resolution that CLAUDE.md 第6条 would require. Therefore, this module is a documented compromise and does not by itself satisfy 唯一真源 / single source of truth. Readers and downstream work should depend on D5/S3/Divergence/DpiDefect.dpi_defect_nonneg, not on this module.

This is the data-processing inequality that wave 11's D5/S3/Divergence/MarginalMonotone module explicitly did not claim. At the level of the data-processing operation, wave 11's first-coordinate marginalization is the special case of forgetting a coordinate. Its deterministic forgetting kernel has zero transition probabilities, so the wave-11 theorem is proved separately rather than by instantiating this theorem.

This is the finite real-valued klDivergence of ClassicalDPI, the repository's single source for the definition, not a measure-theoretic divergence. Mathlib's InformationTheory.klDiv_compProd_eq_add is not used, and no ENNReal/finite-sum bridge is established here.

The remaining limits are full-support requirements: strict positivity of the kernel and of both input distributions is required. Channels with zero transition probabilities and distributions with zero mass are outside this module's scope.

## References

- Truth anchor: `D5/S3/Divergence/ChannelMonotone.kl_divergence_channel_le`
- Dependency: [D5/S3/Divergence/DpiDefect](DpiDefect.md)
