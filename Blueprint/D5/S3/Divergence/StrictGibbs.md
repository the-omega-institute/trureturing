# Strict Positivity of Finite Classical KL Divergence

## Abstract

Distinct finite probability mass functions have strictly positive classical KL divergence.

**Theorem 1.1 (Distinct finite probability masses have positive KL divergence).**

$$\begin{gathered}\forall I\ [\operatorname{Fintype}(I)],\\\forall p, q: I\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum_{i}p(i)=1) \Rightarrow\\((\forall i, 0\le q(i)) \land \sum_{i}q(i)=1) \Rightarrow\\(\forall i, q(i)=0 \Rightarrow p(i)=0) \Rightarrow\\p\neq q \Rightarrow\\0<D(p\Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/StrictGibbs.kl_divergence_pos_of_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be a finite alphabet. Strict Gibbs assumes nonnegativity, normalization, and discrete absolute continuity; it does not assume strict positivity. This is deliberately different from the channel-side convention used by StrictDpi, so the binders must not be copied between the two modules.

The difference is forced by the formulas: StrictGibbs never divides, so discrete absolute continuity alone is enough to keep every logarithm meaningful. StrictDpi forms posteriors by quotienting by channelOutput W p y and therefore needs that denominator to be positive; the same applies to q.

This theorem composes D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg with D5/S3/Divergence/GibbsEquality.kl_divergence_eq_zero_iff; nothing is re-proved. The first result supplies the nonnegative lower bound, and the second rules out equality at zero when p and q are distinct.

It closes the gap that GrandmotherTheorem's own document names: GrandmotherTheorem's own document records only nonnegativity and adds no equality characterization. The new theorem records the strict consequence for distinct mass functions without reopening either proof.

The divergence here is the finite real-valued klDivergence of ClassicalDPI, not a measure-theoretic divergence. Its domain is a finite type and its values are real numbers; no measure-valued or ENNReal bridge is claimed.

## References

- Truth anchor: `D5/S3/Divergence/StrictGibbs.kl_divergence_pos_of_ne`
- Dependency: [D5/S3/Divergence/GibbsEquality](GibbsEquality.md)
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](GrandmotherTheorem.md)
