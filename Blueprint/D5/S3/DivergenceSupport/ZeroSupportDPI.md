# Classical Data Processing on General Support

## Abstract

The finite classical data-processing identity under discrete absolute continuity and general support.

**Theorem 1.1 (The classical DPI chain identity extends to zero support).**

$$\begin{gathered}D(a\Vert\Vert b):=\sum_{i}a(i) \log(\frac{a(i)}{b(i)}),\\(Wr)(y):=\sum_{x}r(x)W(x, y),\\\widehat{r}_{y}(x):=\frac{r(x)W(x, y)}{(Wr)(y)};\\\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to \mathbb{R}, W: X\to Y\to \mathbb{R},\\((\forall x: X, 0\le p(x)) \land \sum_{x}p(x)=1) \Rightarrow\\((\forall x: X, 0\le q(x)) \land \sum_{x}q(x)=1) \Rightarrow\\(\forall x: X, q(x)=0 \Rightarrow p(x)=0) \Rightarrow\\((\forall x: X, y: Y, 0\le W(x, y)) \land (\forall x: X, \sum_{y}W(x, y)=1)) \Rightarrow\\D(p\Vert\Vert q)=D(Wp\Vert\Vert Wq)+\sum_{y}(Wp)(y)D(\widehat{p}_{y}\Vert\Vert \widehat{q}_{y}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/ZeroSupportDPI.classical_dpi_identity_zero_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X and Y be finite types. The functions p and q are nonnegative normalized masses with discrete absolute continuity: q(x) = 0 implies p(x) = 0. The channel W is nonnegative and each row sums to one. The displayed D, channel output, and posterior are exactly the definitions imported from the frozen ClassicalDPI module.

Those definitions are total at zero. Real.log 0 is zero, real division by zero is zero, and a zero output mass multiplies its posterior divergence contribution by zero. The declaration zero_output_weighted_posterior_kl records that convention in a separate theorem. Nonnegativity and finite-sum zero detection also show that p-output mass vanishes whenever q-output mass vanishes, so absolute continuity is preserved by the channel.

The proof writes out the common joint masses p(x)W(x,y) and q(x)W(x,y). Terms with p(x) = 0, W(x,y) = 0, or zero p-output mass are discharged before logarithms are split. On the remaining positive support, absolute continuity makes every denominator positive and Real.log_mul gives the input and output chain decompositions. Equating the two finite sums proves the identity. This is a direct general-support proof, not a specialization of the strict-positivity theorem classical_dpi_identity.

## References

- Truth anchor: `D5/S3/DivergenceSupport/ZeroSupportDPI.classical_dpi_identity_zero_support`
- Dependency: [D5/S3/Divergence/ClassicalDPI](../Divergence/ClassicalDPI.md)
