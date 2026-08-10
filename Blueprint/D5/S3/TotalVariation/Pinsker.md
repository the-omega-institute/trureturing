# Finite Total Variation and Pinsker's Inequality

## Abstract

Finite total variation is pinned by an equal-mass identity and bounded by relative entropy in nats.

**Definition 1.1 (Finite total variation is half the L1 distance).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\\operatorname{TV}(p, q):=\frac{1}{2}\sum_{i}\Vert p(i)-q(i) \Vert.\end{gathered}$$

*Formalization.* `D5/S3/TotalVariation/Pinsker.totalVariation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite real mass functions p and q, totalVariation is one half of the sum of the absolute coordinate differences. It uses the probability-theory normalization in which disjoint unit point masses have distance one.

Pinsker's inequality cannot by itself certify this definition. The inequality 2 TV(p,q)^2 <= D(p||q) would remain valid if the factor one half were corrupted in the safe direction, or if TV were replaced by any uniformly smaller quantity. The normalization and the absolute-value structure are therefore pinned by an identity, not by the later inequality.

**Theorem 1.2 (Equal-mass total variation is positive excess).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\\sum_{i}p(i)=\sum_{i}q(i) \Rightarrow\\\operatorname{TV}(p, q)=\sum_{i: q(i)\le p(i)}(p(i)-q(i)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Pinsker.total_variation_eq_sum_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This identity is the methodological pin for the definition. Equal total mass makes the signed differences sum to zero, so the positive part on the dominance set q(i) <= p(i) balances the negative part on its complement. Consequently, half the absolute sum is exactly the positive excess displayed above.

The hypothesis is minimal in the precise sense expressed by the Lean signature: only equality of total mass is assumed. Neither p nor q is required to be nonnegative, and their common mass need not be one.

A concrete Bool witness shows that the pin is substantive. For two disjoint unit point masses, the raw L1 sum is 2 while the positive excess is 1. A proposed normalization constant c must therefore satisfy 2c = 1, hence c = 1/2. Dropping the absolute values produces the signed total 0, while reversing the dominance set produces the negative excess -1; both corruptions fail the identity. This witness was compiled independently of the formal proof.

**Theorem 1.3 (Binary Pinsker carries the analytic content).**

$$\begin{gathered}\forall a, b\in[0, 1],\\(b=0 \Rightarrow a=0) \land (1-b=0 \Rightarrow 1-a=0) \Rightarrow\\2(a-b)^{2}\le a\log(\frac{a}{b})+(1-a)\log(\frac{1-a}{1-b}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Pinsker.binary_pinsker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This two-point scalar theorem is where the genuine analytic content of Pinsker's inequality resides. The proof treats the endpoint cases first and, on the open unit interval, proves convexity of the divergence deficit after subtracting 2(a-b)^2. Its first derivative vanishes at b, so convexity yields the stated lower bound.

The two implication hypotheses are discrete absolute continuity at both endpoints. The condition b = 0 implies a = 0 controls the first atom, while 1-b = 0 implies 1-a = 0 controls the complementary atom. Both are required because a two-point reference law can degenerate at either end.

**Theorem 1.4 (Zero-support data processing is an identity corollary).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to \mathbb{R}, W: X\to Y\to \mathbb{R},\\((\forall x, 0\le p(x)) \land \sum_{x}p(x)=1) \land\\((\forall x, 0\le q(x)) \land \sum_{x}q(x)=1) \land\\(\forall x, q(x)=0 \Rightarrow p(x)=0) \land\\((\forall x, y, 0\le W(x, y)) \land (\forall x, \sum_{y}W(x, y)=1)) \Rightarrow\\D(Wp\Vert\Vert Wq)\le D(p\Vert\Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Pinsker.kl_divergence_channel_le_zero_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem is not an independent reproof of data processing. It is derived by rewriting with the already-frozen classical_dpi_identity_zero_support from D5/S3/DivergenceSupport and then proving that the residual sum of output-weighted posterior divergences is nonnegative. That identity was contributed separately.

The new content is precisely that residual nonnegativity under the repository's zero-support convention. The DivergenceSupport module established the identity and treated the degenerate case in which the output weight vanishes; it did not establish nonnegativity of the full residual. Here a positive output weight yields normalized nonnegative posteriors with inherited absolute continuity, to which the frozen Gibbs inequality applies.

This provenance is required by the repository's one-source-of-truth discipline. A later inequality that follows from an earlier identity is presented as its corollary, not as a rival proof of the same structure.

Although this is a general divergence statement rather than a total-variation statement, it remains in this bucket because it currently has exactly one consumer: the assembly below. The repository lifts an abstraction when a second instance or demonstrated pressure appears, not in anticipation. A second consumer should therefore cause this lemma to be lifted to DivergenceSupport.

**Theorem 1.5 (Pinsker reduces through the dominance channel).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum_{i}p(i)=1) \land\\((\forall i, 0\le q(i)) \land \sum_{i}q(i)=1) \land\\(\forall i, q(i)=0 \Rightarrow p(i)=0) \Rightarrow\\2\operatorname{TV}(p, q)^{2}\le D(p\Vert\Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Pinsker.pinsker_inequality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof has three layers. First, binary_pinsker supplies the genuine analytic estimate on two points. Second, data processing sends p and q through the deterministic channel i maps to the truth value of q(i) <= p(i), reducing the finite alphabet to Bool. Third, the assembly identifies the two output masses, applies the binary estimate, and returns through the data-processing inequality.

If a and b denote the p- and q-masses of the dominance set, the pinning identity gives TV(p,q) = a-b. The Bool output divergence is exactly the binary expression, and zero-support data processing bounds it above by D(p||q). Thus the channel layer performs the reduction, while the scalar layer carries the analytic work.

The absolute-continuity convention is q(i) = 0 implies p(i) = 0, exactly as in the frozen divergence modules. It is preserved by the channel and induces both endpoint implications required by binary_pinsker.

This document opens the TotalVariation bucket at stratum S3. The bucket is split from D5/S3/Entropy, which had reached its twelve-file capacity. All logarithms are natural, so the divergence and the bound are in nats.

No reverse bound of Bretagnolle-Huber type is claimed. The module gives no continuous or measure-theoretic analogue and no analysis of sharpness or equality cases.

## References

- Truth anchor: `D5/S3/TotalVariation/Pinsker.binary_pinsker`
- Truth anchor: `D5/S3/TotalVariation/Pinsker.kl_divergence_channel_le_zero_support`
- Truth anchor: `D5/S3/TotalVariation/Pinsker.pinsker_inequality`
- Truth anchor: `D5/S3/TotalVariation/Pinsker.totalVariation`
- Truth anchor: `D5/S3/TotalVariation/Pinsker.total_variation_eq_sum_positive`
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](../Divergence/GrandmotherTheorem.md)
- Dependency: [D5/S3/DivergenceSupport/ZeroSupportDPI](../DivergenceSupport/ZeroSupportDPI.md)
