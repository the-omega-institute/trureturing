# Classical Data Processing as a Chain Identity

## Abstract

The finite classical data-processing identity from two decompositions of joint relative entropy.

**Theorem 1.1 (Joint relative entropy has two chain decompositions).**

$$\begin{gathered}D(a\Vert\Vert b):=\sum_{i}a(i) \log(\frac{a(i)}{b(i)}),\\(Wr)(y):=\sum_{x}r(x)W(x, y),\\\widehat{r}_{y}(x):=\frac{r(x)W(x, y)}{(Wr)(y)};\\\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Nonempty}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to\mathbb{R}, W: X\to Y\to\mathbb{R},\\((\forall x: X, 0<p(x)) \land \sum_{x}p(x)=1) \Rightarrow\\((\forall x: X, 0<q(x)) \land \sum_{x}q(x)=1) \Rightarrow\\((\forall x: X, y: Y, 0<W(x, y)) \land (\forall x: X, \sum_{y}W(x, y)=1)) \Rightarrow\\D(p\Vert\Vert q)=D(Wp\Vert\Vert Wq)+\sum_{y}(Wp)(y)D(\widehat{p}_{y}\Vert\Vert\widehat{q}_{y}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/ClassicalDPI.classical_dpi_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X and Y be finite types, with X nonempty. Let p and q be strictly positive normalized real mass functions on X, and let W be a strictly positive row-stochastic channel from X to Y. The displayed definitions agree pointwise with the Lean definitions klDivergence, channelOutput, and posterior. Under these hypotheses every output mass and every posterior denominator is positive, so all logarithms are evaluated on positive ratios.

For the joint mass functions P(x,y) = p(x)W(x,y) and Q(x,y) = q(x)W(x,y), decomposition by the input coordinate cancels the common channel factor and gives D(P||Q) = D(p||q). Decomposition by the output coordinate uses P(x,y) = (Wp)(y) p-hat_y(x) and the analogous factorization of Q, giving D(P||Q) = D(Wp||Wq) plus the Wp-weighted sum of posterior divergences. Equating the two checked finite sums proves the identity. The declaration formalizes the full-support case only; it does not claim the zero-support extension obtained by absolute continuity and the convention 0 log 0 = 0.

## References

- Truth anchor: `D5/S3/Divergence/ClassicalDPI.classical_dpi_identity`
