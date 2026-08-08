# The Grandmother Theorem

## Abstract

Absolutely continuous finite mass functions have nonnegative Kullback-Leibler divergence.

**Theorem 1.1 (Absolutely continuous finite masses have nonnegative KL divergence).**

$$\begin{gathered}\forall I\ [\operatorname{Fintype}(I)],\\\forall p, q: I\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum_{i}p(i)=1) \land \\((\forall i, 0\le q(i)) \land \sum_{i}q(i)=1) \land \\(\forall i, q(i)=0 \Rightarrow p(i)=0) \Rightarrow\\D(p\Vert q):=\sum_{i}p(i) \log(\frac{p(i)}{q(i)}) \geq 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be a finite alphabet and let p and q be nonnegative normalized real mass functions. The last hypothesis is discrete absolute continuity: every zero of q is a zero of p. Consequently the displayed finite sum is the standard boundary extension in which a zero p term contributes zero. The definition of D is exactly the klDivergence imported from ClassicalDPI; this document introduces no second divergence.

The Lean proof reuses Mathlib's nonnegativity theorem for klFun. Pointwise multiplication by q(i) rewrites q(i) klFun(p(i)/q(i)) as p(i) log(p(i)/q(i)) plus q(i) minus p(i). At q(i) equal to zero, absolute continuity also makes p(i) zero, so the identity holds at the boundary; elsewhere denominator cancellation proves it directly. Summation preserves nonnegativity, while normalization cancels the affine correction. Thus the remaining sum is precisely D(p||q).

$$
\begin{aligned}D(p\Vert q)&=\sum_{i}p(i)(-\log(\frac{q(i)}{p(i)}))\\&\geq -\log(\sum_{i}p(i)\frac{q(i)}{p(i)})\\&=-\log(\sum_{i:p(i)>0}q(i))\geq -\log(\sum_{i}q(i))=0.\end{aligned}
$$

Equivalently, apply Jensen's inequality for the convex function minus log on the support of p. The weighted argument has expectation equal to the q mass of that support, which is at most the total q mass one; monotonicity of minus log gives the final inequality. When p has full support, the support sum is exactly sum q(i), recovering the normalized identity E_p[q/p] equal to one verbatim. This is the grandmother mechanism: KL nonnegativity is the Jensen shadow of normalization. The linked Lean declaration records only nonnegativity; it does not add a separate equality characterization.

## References

- Truth anchor: `D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg`
- Dependency: [D5/S3/Divergence/ClassicalDPI](ClassicalDPI.md)
