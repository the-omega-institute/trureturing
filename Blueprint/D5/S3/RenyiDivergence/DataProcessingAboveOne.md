# Above-One Data Processing for Finite Renyi Divergence

## Abstract

Above one, finite Renyi divergence obeys data processing under discrete absolute continuity, while a compiled order-two witness shows why that support hypothesis is necessary for the totalized definition.

**Theorem 1.1 (Above-one Renyi divergence obeys data processing under absolute continuity).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Fintype}(Y)],\\\forall \alpha \in \mathbb{R}, 1< \alpha,\\\forall p, q: X\to \mathbb{R}, W: X\to Y\to \mathbb{R},\\((\forall x, 0\le p(x)) \land \\(\forall x, 0\le q(x)) \land \\(\forall x, q(x)=0 \Rightarrow p(x)=0) \land \\((\forall x, y, 0\le W(x, y)) \land (\forall x, \sum _{y} W(x, y)=1)))) \Rightarrow \\D_{\alpha }(\operatorname{channelOutput}(W, p)\Vert \Vert \operatorname{channelOutput}(W, q))\le D_{\alpha }(p\Vert \Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/DataProcessingAboveOne.renyi_divergence_channel_le_of_one_lt_of_ac` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem closes the precise open sentence in the frozen below-one data-processing module: orders above one were excluded because, with merely nonnegative masses, missing support and zero powers could reverse the desired inequality. Discrete absolute continuity, namely q x = 0 implies p x = 0, is the stronger support hypothesis supplied here. The frozen sentence is: "Orders above one are not covered: with merely nonnegative masses, missing support and zero powers can reverse the desired inequality. Stronger support hypotheses may recover that range, but no such theorem is claimed here."

The sign bookkeeping reverses relative to the sub-unit theorem. When 0 < alpha < 1, the prefactor 1/(alpha - 1) is negative, so the power sum must increase and the prefactor reverses the logarithmic comparison. For alpha > 1 the prefactor is positive, so the power sum must decrease. Holder therefore uses the conjugate pair alpha and alpha/(alpha - 1), both strictly greater than one.

No normalization and no pointwise strict positivity is assumed. Nonnegative p and q may share zero coordinates; absolute continuity only prevents p from being nonzero where q vanishes. The channel is likewise only pointwise nonnegative and row-stochastic.

The authored display is legal because the current statement projector has no pinned projectable fixture for this declaration, so construction records a ProjectionGap rather than pretending that the presentation is Lean-derived.

**Theorem 1.2 (Order two has a compiled Bool-to-Unit data-processing failure).**

$$\begin{gathered}X=Bool, Y=Unit, \alpha=2,\\p=(\frac{1}{2}, \frac{1}{2}), q=(1, 0), W=1,\\((p\geq 0) \land p= 1, (q\geq 0) \land q= 1, (W\geq 0) \land W= 1) \Rightarrow\\D_{2}(\operatorname{channelOutput}(W, p)\Vert \Vert \operatorname{channelOutput}(W, q))> D_{2}(p\Vert \Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/DataProcessingAboveOne.renyi_divergence_data_processing_failure_order_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is an explicit compiled counterexample at alpha = 2. The source takes X = Bool, Y = Unit, p = (1/2, 1/2), q = (1, 0), and the constant channel W x y = 1. Both masses are pointwise nonnegative and normalized, and W is pointwise nonnegative with every row sum equal to one. Nevertheless the post-channel divergence is 0, whereas the pre-channel divergence is -2 log 2, so the strict inequality is reversed.

The witness makes the absolute-continuity hypothesis machine-proved necessary for this totalized formal definition rather than merely convenient. q has a zero coordinate where p is nonzero. At order two the corresponding contribution has a negative q exponent; the repository's totalization sends a zero base with that negative exponent to zero instead of infinity. The pre-channel divergence is therefore understated and becomes negative, while mixing through the constant channel raises it to zero.

The counterexample does not establish that q must be pointwise strictly positive. The main theorem explicitly permits p and q to share zero coordinates, provided every zero of q is also a zero of p. Its claim is exactly the weaker discrete absolute-continuity condition.

The authored display is legal for the same reason as the preceding theorem: no pinned projectable statement fixture exists for this declaration, and construction records the resulting ProjectionGap.

## References

- Truth anchor: `D5/S3/RenyiDivergence/DataProcessingAboveOne.renyi_divergence_channel_le_of_one_lt_of_ac`
- Truth anchor: `D5/S3/RenyiDivergence/DataProcessingAboveOne.renyi_divergence_data_processing_failure_order_two`
- Dependency: [D5/S3/RenyiDivergence/DataProcessing](DataProcessing.md)
