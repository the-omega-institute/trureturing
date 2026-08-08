# The Classical Petz Equality Condition

## Abstract

Zero classical data-processing defect is equivalent to supportwise equality of posteriors.

**Theorem 1.1 (Zero DPI defect is supportwise posterior equality).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Nonempty}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to \mathbb{R}, W: X\to Y\to \mathbb{R},\\((\forall x: X, 0<p(x)) \land \sum_{x}p(x)=1) \Rightarrow\\((\forall x: X, 0<q(x)) \land \sum_{x}q(x)=1) \Rightarrow\\((\forall x: X, y: Y, 0<W(x, y)) \land (\forall x: X, \sum_{y}W(x, y)=1)) \Rightarrow\\D(p\Vert\Vert q)-D(Wp\Vert\Vert Wq)=0 \Leftrightarrow\\\forall y: Y, 0<(Wp)(y) \Rightarrow \widehat{p}_{y}=\widehat{q}_{y}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/PetzClassical.dpi_defect_zero_iff_posteriors_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X and Y be finite types, with X nonempty. Let p and q be strictly positive normalized real mass functions on X, and let W be a strictly positive row-stochastic channel from X to Y. The symbols D, Wp, and p-hat_y are exactly the divergence, channel output, and posterior defined in ClassicalDPI. The conclusion is stated on the support of Wp, even though the present full-support hypotheses make every output mass positive.

The classical data-processing identity rewrites the defect as the finite sum over y of (Wp)(y) times D(p-hat_y||q-hat_y). The Grandmother Theorem makes every posterior divergence nonnegative, so every weighted summand is nonnegative. If the defect is zero, the finite nonnegative-sum criterion makes each weighted summand zero. On the support of Wp, the positive weight can be cancelled, and Gibbs equality gives p-hat_y = q-hat_y. Conversely, supportwise posterior equality makes every summand vanish and hence makes the defect zero.

This declaration proves only the core equality characterization. Bayesian reverse recovery and the permutation-channel specialization are not part of this declaration; they require separate statements and proofs.

## References

- Truth anchor: `D5/S3/Divergence/PetzClassical.dpi_defect_zero_iff_posteriors_eq`
- Dependency: [D5/S3/Divergence/ClassicalDPI](ClassicalDPI.md)
- Dependency: [D5/S3/Divergence/GibbsEquality](GibbsEquality.md)
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](GrandmotherTheorem.md)
