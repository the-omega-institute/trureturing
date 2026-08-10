# Data Processing for Finite Renyi Divergence

## Abstract

Finite nonnegative row-stochastic processing cannot increase Renyi divergence at orders strictly between zero and one under positive overlap.

**Theorem 1.1 (Half-order data processing is a corollary of frozen results).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to \mathbb{R}, W: X\to Y\to \mathbb{R},\\((\forall x, 0\le p(x)) \land \\(\forall x, 0\le q(x)) \land \\(\exists x, 0< p(x) \land 0< q(x)) \land \\((\forall x, y, 0\le W(x, y)) \land (\forall x, \sum _{y} W(x, y)=1))) \Rightarrow \\D_{\frac{1}{2}}(\operatorname{channelOutput}(W, p)\Vert \Vert \operatorname{channelOutput}(W, q))\le D_{\frac{1}{2}}(p\Vert \Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/DataProcessing.renyi_divergence_one_half_channel_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This named theorem is a corollary of frozen results, not a new proof of the half-order mathematics. Its Lean doc comment opens with that provenance and expressly disclaims novelty at half order. The frozen theorem bhattacharyya_channel_le states that a nonnegative row-stochastic channel increases Bhattacharyya affinity, while the frozen identity renyi_divergence_one_half identifies D_(1/2) with -2 log BC. Monotonicity of the logarithm followed by multiplication by the negative factor -2 gives the displayed inequality in one step.

Positive input overlap keeps the affinity strictly positive, so the logarithmic comparison is legitimate under the repository convention Real.log 0 = 0. Output nonnegativity follows directly from nonnegative input masses and channel entries. No normalization of p or q is used.

The corollary is stated with explicit provenance because a consequence of an earlier frozen theorem is presented as that theorem's corollary, never as a rival derivation of the same structure. Its separate name also preserves the established half-order interface for later users.

The corollary also serves as a consistency check on the general theorem below. The Lean module contains a compiled example whose conjunction has the corollary's exact statement on both sides: one conjunct is discharged by the frozen-material corollary, and the other by specializing the general theorem to alpha = 1/2. A general statement that silently disagreed with an already-frozen special case would signal an error in its formulation; the overlap is precisely where such an error is least costly to detect. The caller reproduced this compiled check independently.

**Theorem 1.2 (Sub-unit Renyi divergence obeys data processing).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Fintype}(Y)],\\\forall \alpha \in \mathbb{R}, 0< \alpha < 1,\\\forall p, q: X\to \mathbb{R}, W: X\to Y\to \mathbb{R},\\((\forall x, 0\le p(x)) \land \\(\forall x, 0\le q(x)) \land \\(\exists x, 0< p(x) \land 0< q(x)) \land \\((\forall x, y, 0\le W(x, y)) \land (\forall x, \sum _{y} W(x, y)=1))) \Rightarrow \\D_{\alpha }(\operatorname{channelOutput}(W, p)\Vert \Vert \operatorname{channelOutput}(W, q))\le D_{\alpha }(p\Vert \Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/DataProcessing.renyi_divergence_channel_le_of_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Processing an observation cannot increase finite Renyi divergence at any real order strictly between zero and one. The repository already contained data processing for classical divergence and total variation, together with affinity growth for the Bhattacharyya coefficient and contraction of squared Hellinger distance. This theorem places the sub-unit Renyi family in the same finite-channel framework.

The theorem covers every real alpha with 0 < alpha < 1, every pair of finite pointwise nonnegative mass functions p and q having at least one coordinate at which both are positive, and every pointwise nonnegative row-stochastic channel W. Neither input is required to be normalized. This distinction is substantive: the sibling squared Hellinger contraction does require both inputs to have unit mass.

For each output coordinate, finite Holder bounds the sum of the mixed alpha and 1-alpha powers by the corresponding powers of the two output masses. Summation over outputs, interchange of the finite sums, and the unit row sums of W show that the Renyi power sum cannot decrease under the channel. Positive overlap makes the input power sum strictly positive. The logarithm therefore preserves the comparison, whereas the prefactor 1/(alpha-1) is nonpositive and reverses it, yielding the displayed data-processing inequality.

At alpha = 1 the repository's definition is literally zero because its totalized prefactor vanishes. Data processing at that order is thus a trivial equality for this definition, not the order-one or Kullback--Leibler interpretation. No such interpretation is claimed.

Above order one, the displayed theorem is false under its minimal support hypotheses, and the Lean module compiles a counterexample. At order two, take the uniform law p on Bool and a point mass q, which still have positive overlap, and send both through the constant channel to Unit. The output divergence is 0, while the input divergence is -2 log 2, so the asserted inequality 0 <= -2 log 2 fails.

This failure is produced by the formalization's totalizing conventions, not by Renyi divergence itself. At the unsupported coordinate, the order-two contribution is mathematically infinite, but Lean's x/0 = 0 erases it. The surrounding definition likewise stipulates Real.log 0 = 0; together these conventions replace support-boundary infinities by finite values. The compiled example records an artifact of this formal definition and must not be read as evidence that mathematical Renyi data processing fails above order one.

Nonpositive orders are not claimed. The Holder conjugates used by the proof require alpha and 1-alpha to be positive, and hence require strictly positive sub-unit order.

No order-one limit, data-processing theorem above order one, equality characterization, or measure-theoretic analogue is claimed. All logarithms are natural, so the units are nats.

## References

- Truth anchor: `D5/S3/RenyiDivergence/DataProcessing.renyi_divergence_channel_le_of_lt_one`
- Truth anchor: `D5/S3/RenyiDivergence/DataProcessing.renyi_divergence_one_half_channel_le`
- Dependency: [D5/S3/RenyiDivergence/Monotone](Monotone.md)
- Dependency: [D5/S3/TotalVariation/HellingerDataProcessing](../TotalVariation/HellingerDataProcessing.md)
