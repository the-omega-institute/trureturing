# Strict Positivity of the Classical Data-Processing Defect

## Abstract

Posterior disequality makes the finite classical data-processing defect strictly positive.

**Theorem 1.1 (Posterior disequality makes the classical DPI defect positive).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Nonempty}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to \mathbb{R}, W: X\to Y\to \mathbb{R},\\((\forall x, 0<p(x)) \land \sum_{x}p(x)= 1) \Rightarrow\\((\forall x, 0<q(x)) \land \sum_{x}q(x)= 1) \Rightarrow\\((\forall x, y, 0<W(x, y)) \land (\forall x, \sum_{y}W(x, y)= 1)) \Rightarrow\\(\exists y: Y, \widehat{p}_{y}\neq\widehat{q}_{y}) \Rightarrow\\0<D(p\Vert\Vert q)-D(Wp\Vert\Vert Wq).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/StrictDpi.dpi_defect_pos_of_posteriors_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X and Y be finite alphabets, with X nonempty. Strict DPI assumes strict positivity of p and q and of the stochastic kernel W. This is the channel-side convention, deliberately different from StrictGibbs's nonnegative absolutely continuous convention, so the binders must not be copied between the two modules. All three objects are normalized in the corresponding mass or row direction.

The stricter convention is forced by the posterior formula: posterior W p y is a quotient by channelOutput W p y; the posterior is defined, and is positive, only when that denominator is positive. The same applies to q. StrictGibbs never divides, so discrete absolute continuity alone is enough to keep every logarithm meaningful.

This theorem composes D5/S3/Divergence/DpiDefect.dpi_defect_nonneg with D5/S3/Divergence/PetzClassical.dpi_defect_zero_iff_posteriors_eq; nothing is re-proved. The nonnegative defect cannot be zero when the stated posterior disequality contradicts PetzClassical's equality characterization.

The premise is not p ≠ q: it is ∃ y, posterior W p y ≠ posterior W q y. Distinct inputs are neither the hypothesis of this theorem nor claimed by it to be sufficient; this module says nothing about whether p ≠ q alone forces a strictly positive defect.

PetzClassical's output-positivity side condition is discharged from these hypotheses by a Finset.sum_pos' argument; it is not assumed. Strict positivity of p and W makes each summand nonnegative and supplies a positive witness because X is nonempty.

The honest limit is the full-support regime: the kernel and both inputs are strictly positive, so zero transition probabilities and zero-mass distributions remain outside this module. This scope is narrower than a boundary-aware channel theorem.

This completes the defect cluster opened by PetzClassical: the defect is zero if and only if the posteriors are equal, hence the defect is strictly positive exactly when they differ. The displayed theorem packages the disequality-to-positivity direction.

## References

- Truth anchor: `D5/S3/Divergence/StrictDpi.dpi_defect_pos_of_posteriors_ne`
- Dependency: [D5/S3/Divergence/DpiDefect](DpiDefect.md)
- Dependency: [D5/S3/Divergence/PetzClassical](PetzClassical.md)
