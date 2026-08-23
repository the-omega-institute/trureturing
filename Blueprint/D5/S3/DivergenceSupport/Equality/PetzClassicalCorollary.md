# Posterior Equality, Recovery, and Permutation Channels

## Abstract

Zero data-processing defect is characterized by posterior agreement and Bayesian recovery, and it vanishes for permutation channels.

The three clauses are stated together: posterior equality on every positive output, exact recovery by the Bayesian reverse channel, and zero defect for every finite permutation channel.

**Theorem 1.1 (Zero defect, recovery, and permutation equality).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to \mathbb{R}, W: X\to Y\to \mathbb{R},\\((\forall x: X, 0\le p(x)) \land \sum_{x}p(x) = 1) \Rightarrow\\((\forall x: X, 0\le q(x)) \land \sum_{x}q(x) = 1) \Rightarrow\\(\forall x: X, q(x) = 0 \Rightarrow p(x) = 0) \Rightarrow\\((\forall x: X, y: Y, 0\le W(x, y)) \land (\forall x: X, \sum_{y}W(x, y) = 1)) \Rightarrow\\{}[(D(p\Vert\Vert q) - D((Wp)\Vert\Vert (Wq)) = 0 \Leftrightarrow \forall y, (Wp)(y) = 0 \lor \widehat{p}_{y} = \widehat{q}_{y}) \land\\(D(p\Vert\Vert q) - D((Wp)\Vert\Vert (Wq)) = 0 \Leftrightarrow \exists R: Y\to X\to \mathbb{R},\\(\forall y, x, R(y, x) = \begin{cases}q(x), &(Wq)(y) = 0\\\widehat{q}_{y}(x), &\text{otherwise}\end{cases}) \land\\(\forall y, x, 0\le R(y, x)) \land (\forall y, \sum_{x}R(y, x) = 1) \land\\(R(Wp)) = p \land (R(Wq)) = q) \land\\\forall e: X \equiv Y, D(p\Vert\Vert q) - D((P_{e}p)\Vert\Vert (P_{e}q)) = 0].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/Equality/PetzClassicalCorollary.zero_defect_equivalences_and_permutation_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The posterior and recovery equivalences are imported exact results. For a permutation channel, the output law is the input law reindexed by the inverse equivalence. Mathlib's finite-sum reindexing theorem then makes the two divergences equal.

## References

- Truth anchor: `D5/S3/DivergenceSupport/Equality/PetzClassicalCorollary.zero_defect_equivalences_and_permutation_channel`
- Dependency: [D5/S3/DivergenceSupport/Equality/PetzRecovery](PetzRecovery.md)
