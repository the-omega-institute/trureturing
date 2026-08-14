# When the General-Support Data-Processing Defect Vanishes

## Abstract

Equality cases for the finite classical data-processing defect on general support.

The frozen ZeroSupportDefect module proved that the data-processing defect is nonnegative, but it did not characterize equality. The two results below supply exactly that missing case under the same hypotheses, so nonnegativity and vanishing now form a matched pair on general support.

Both results rest on the frozen general-support chain identity. It expresses the input divergence as the output divergence plus a finite output-weighted sum of posterior divergences. Every summand is nonnegative, and a finite sum of nonnegative real numbers vanishes exactly when every summand vanishes. The frozen KL equality characterization then identifies a zero posterior divergence with equality of the two posteriors wherever the output weight is positive.

Thus a channel loses no divergence exactly when it leaves the two posteriors indistinguishable at every output letter to which the input law p gives positive output mass.

This criterion is neither a recovery map nor a statement of Petz sufficiency. The module also does not assert that the criterion can be checked from the input laws and the channel without computing the posteriors.

Both displays are authored legally because the current statement projector has no pinned projectable fixture for either declaration. Document construction therefore records a ProjectionGap for each theorem.

**Theorem 1.1 (Zero defect is pointwise vanishing of weighted posterior divergence).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to \mathbb{R}, W: X\to Y\to \mathbb{R},\\((\forall x: X, 0\le p(x)) \land \sum_{x}p(x)=1) \Rightarrow\\((\forall x: X, 0\le q(x)) \land \sum_{x}q(x)=1) \Rightarrow\\(\forall x: X, q(x)=0 \Rightarrow p(x)=0) \Rightarrow\\((\forall x: X, y: Y, 0\le W(x, y)) \land (\forall x: X, \sum_{y}W(x, y)=1)) \Rightarrow\\D(p\Vert\Vert q) - D((Wp)\Vert\Vert (Wq)) = 0 \Leftrightarrow\\\forall y: Y, (Wp)(y) D(\widehat{p}_{y}\Vert\Vert \widehat{q}_{y}) = 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/ZeroSupportDefectEquality.dpi_defect_eq_zero_iff_weighted_posterior_kl_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first equivalence retains the weighted posterior terms themselves. After the chain identity rewrites the defect as their finite sum, nonnegativity makes equality of the sum equivalent to pointwise equality of every term with zero. This statement includes zero-output letters, whose weighted terms vanish by the frozen zero-output convention.

**Theorem 1.2 (Zero defect is zero output mass or equality of posteriors).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to \mathbb{R}, W: X\to Y\to \mathbb{R},\\((\forall x: X, 0\le p(x)) \land \sum_{x}p(x)=1) \Rightarrow\\((\forall x: X, 0\le q(x)) \land \sum_{x}q(x)=1) \Rightarrow\\(\forall x: X, q(x)=0 \Rightarrow p(x)=0) \Rightarrow\\((\forall x: X, y: Y, 0\le W(x, y)) \land (\forall x: X, \sum_{y}W(x, y)=1)) \Rightarrow\\D(p\Vert\Vert q) - D((Wp)\Vert\Vert (Wq)) = 0 \Leftrightarrow\\\forall y: Y, (Wp)(y) = 0 \lor \widehat{p}_{y} = \widehat{q}_{y}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/ZeroSupportDefectEquality.dpi_defect_eq_zero_iff_zero_output_or_posteriors_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second equivalence resolves each weighted zero term. At a zero-output letter the term vanishes automatically. Otherwise output absolute continuity makes both relevant output masses positive, so the positive weight can be cancelled and the frozen KL equality theorem makes the two posterior mass functions equal. The converse applies the same alternatives letter by letter.

## References

- Truth anchor: `D5/S3/DivergenceSupport/ZeroSupportDefectEquality.dpi_defect_eq_zero_iff_weighted_posterior_kl_zero`
- Truth anchor: `D5/S3/DivergenceSupport/ZeroSupportDefectEquality.dpi_defect_eq_zero_iff_zero_output_or_posteriors_eq`
- Dependency: [D5/S3/Divergence/GibbsEquality](../Divergence/GibbsEquality.md)
- Dependency: [D5/S3/DivergenceSupport/ZeroSupportDefect](ZeroSupportDefect.md)
