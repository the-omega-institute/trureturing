# Data Processing for Finite Total Variation

## Abstract

A nonnegative row-stochastic finite channel contracts total variation for arbitrary real input functions.

**Theorem 1.1 (Stochastic channels contract total variation).**

$$\begin{gathered}\forall X, Y: \operatorname{Type},\ [\operatorname{Fintype}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to \mathbb{R}, W: X\to Y\to \mathbb{R},\\((\forall x, y, 0\le W(x, y)) \land (\forall x, \sum_{y}W(x, y)=1)) \Rightarrow\\\operatorname{TV}(\operatorname{channelOutput}(W, p), \operatorname{channelOutput}(W, q))\le \operatorname{TV}(p, q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/DataProcessing.total_variation_channel_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No processing of an observation can make two laws easier to distinguish. This contraction property is what makes total variation a legitimate measure of statistical distinguishability, and it is the total-variation counterpart of the divergence data-processing result already frozen in this repository.

The hypothesis set is strikingly small, and this economy is the document's most informative point. Only the channel W is constrained: its entries are nonnegative and every row sums to one. The input mass functions p and q are arbitrary real functions. They need not be nonnegative, neither function need be normalized, their total masses need not be equal, and no absolute-continuity or zero-support convention is imposed.

This is a structural contrast with the frozen divergence theorem. That result requires nonnegativity of both input mass functions, normalization of both and hence equality of total mass, and the zero-support implication expressing absolute continuity. Divergence contains logarithms and division, so positivity and a convention at zero support are indispensable. Total variation contains only absolute values and finite sums, which impose none of these input conditions. Channel nonnegativity is used only to replace |W(x,y)| by W(x,y), while row normalization is used only to collapse the factored channel mass to one.

The proof route was chosen for strength, not elegance. For each output coordinate y, the difference is rewritten as the sum over x of (p(x)-q(x))W(x,y). The triangle inequality for finite sums bounds its absolute value pointwise. Nonnegativity removes the absolute value from W; the two finite sums are then interchanged; and row normalization completes the estimate.

A route through the variational characterization appears more conceptual but is weaker here in two respects. It would import an equal-mass assumption, and an output event pulls back through a general channel only to a randomized input test. That approach would therefore require a separate argument absent from the direct proof. A route that forces extra hypotheses merely to appear conceptual is the wrong choice.

The inequality is genuinely strict. Take X = Bool, Y = Unit, and the constant channel W(x,()) = 1; it is nonnegative and every row sums to one. Let p(true) = 1 and p(false) = 0, while q(false) = 1 and q(true) = 0. These are disjoint unit point masses, so their input total variation is 1, whereas both channel outputs are the same unit mass and therefore have total variation 0. This witness was compiled independently. Thus the bound is not secretly an equality: a channel that discards its input collapses all distinguishability.

This theorem supplies the contraction component of the TotalVariation bucket's three-part narrative, alongside Pinsker's bound and the metric structure with its variational characterization. Where divergence is mentioned, logarithms are natural and the units are nats.

No reverse bound of Bretagnolle-Huber type is claimed. There is no characterization of equality or of the channels that preserve total variation, and no continuous or measure-theoretic analogue is given.

## References

- Truth anchor: `D5/S3/TotalVariation/DataProcessing.total_variation_channel_le`
- Dependency: [D5/S3/TotalVariation/Pinsker](Pinsker.md)
