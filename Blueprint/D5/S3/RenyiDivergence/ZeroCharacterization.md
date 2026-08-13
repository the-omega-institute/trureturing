# Zero Characterization of Finite Renyi Divergence

## Abstract

Finite Renyi divergence is nonnegative above order one and vanishes exactly when the two normalized laws coincide, with deliberately different support hypotheses below and above one.

**Theorem 1.1 (Finite Renyi divergence is nonnegative above one under absolute continuity).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall \alpha \in \mathbb{R}, \forall p, q: \iota\to \mathbb{R},\\(1< \alpha \land (\forall i, 0\le p(i)) \land \sum _{i} p(i)= 1 \land \\(\forall i, 0\le q(i)) \land \sum _{i} q(i)= 1 \land \\(\forall i, q(i)= 0 \Rightarrow p(i)= 0)) \Rightarrow\\0\le D_{\alpha }(p\Vert \Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/ZeroCharacterization.renyi_divergence_nonneg_of_one_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen Basic module proved zero self-divergence at every real order, but its nonnegativity theorem covered only 0 < alpha < 1. This declaration supplies the missing super-unit half under discrete absolute continuity: every zero coordinate of q is also a zero coordinate of p.

Above one the proof is a composition of frozen results. Kullback--Leibler divergence is nonnegative, and the frozen comparison gives KL(p || q) <= D_alpha(p || q); transitivity therefore yields the claimed lower bound.

Absolute continuity is load-bearing rather than decorative. The preceding wave already compiled the order-two witness p = (1/2, 1/2), q = (1, 0), whose divergence is -2 log 2 because the repository's totalization sends a zero base with a negative exponent to zero rather than infinity. This declaration does not repeat that witness; it supplies the hypothesis that excludes its support boundary.

The authored display is legal because no pinned projectable statement fixture exists for this declaration; construction records the resulting ProjectionGap.

**Theorem 1.2 (Below one, zero Renyi divergence characterizes equality under common positive support).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall \alpha \in \mathbb{R}, \forall p, q: \iota\to \mathbb{R},\\(0< \alpha \land \alpha< 1 \land (\forall i, 0\le p(i)) \land \sum _{i} p(i)= 1 \land \\(\forall i, 0\le q(i)) \land \sum _{i} q(i)= 1 \land \\(\exists i, 0< p(i) \land 0< q(i))) \Rightarrow\\D_{\alpha }(p\Vert \Vert q)= 0 \Leftrightarrow p= q.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/ZeroCharacterization.renyi_divergence_eq_zero_iff_of_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bucket previously had no converse to zero self-divergence: nowhere did a vanishing Renyi divergence force the two laws to coincide. Below one this declaration supplies that converse under the existence of one coordinate where both p and q are strictly positive.

This side requires a genuine equality argument because the frozen KL comparison points the wrong way, D_alpha(p || q) <= KL(p || q), and hence a zero Renyi divergence gives no KL upper bound. Vanishing first forces the positive power sum to equal one. Weighted arithmetic--geometric mean bounds each summand by alpha p_i + (1 - alpha) q_i, whose normalized finite sum is also one. Equality of these two finite sums forces equality at every coordinate, and mathlib's weighted AM--GM equality condition Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos then gives p_i = q_i.

Common positive support is deliberately weaker than absolute continuity. Only one shared positive coordinate is needed to keep the power sum strictly positive and recover it from its logarithm; no implication from every zero of q to a zero of p is assumed. Consequently this below-one statement is stronger in its support generality than the above-one result.

The authored display is legal because no pinned projectable statement fixture exists for this declaration; construction records the resulting ProjectionGap.

**Theorem 1.3 (Above one, zero Renyi divergence characterizes equality under absolute continuity).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall \alpha \in \mathbb{R}, \forall p, q: \iota\to \mathbb{R},\\(1< \alpha \land (\forall i, 0\le p(i)) \land \sum _{i} p(i)= 1 \land \\(\forall i, 0\le q(i)) \land \sum _{i} q(i)= 1 \land \\(\forall i, q(i)= 0 \Rightarrow p(i)= 0)) \Rightarrow\\D_{\alpha }(p\Vert \Vert q)= 0 \Leftrightarrow p= q.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/ZeroCharacterization.renyi_divergence_eq_zero_iff_of_one_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above one the equality characterization is substantially cheaper than its below-one counterpart. Nonnegativity gives 0 <= KL(p || q), while the frozen super-unit comparison gives KL(p || q) <= D_alpha(p || q). If the Renyi divergence vanishes, these inequalities squeeze KL to zero, and the frozen kl_divergence_eq_zero_iff theorem yields p = q. The reverse implication is the already frozen self-divergence theorem.

The proof uses absolute continuity twice through the frozen KL material: it supports KL nonnegativity and converts positivity of p into positivity of q where the order comparison needs it. The weaker common-positive-support premise from the below-one theorem cannot replace this condition.

Thus the two sides do not carry identical hypotheses or proof costs. Above one is a composition of frozen KL results under the stronger support law; below one is a coordinatewise AM--GM equality proof under the weaker shared positivity assumption.

The authored display is legal because no pinned projectable statement fixture exists for this declaration; construction records the resulting ProjectionGap.

**Theorem 1.4 (At positive orders other than one, zero Renyi divergence characterizes equality under absolute continuity).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall \alpha \in \mathbb{R}, \forall p, q: \iota\to \mathbb{R},\\(0< \alpha \land \alpha\neq 1 \land (\forall i, 0\le p(i)) \land \sum _{i} p(i)= 1 \land \\(\forall i, 0\le q(i)) \land \sum _{i} q(i)= 1 \land \\(\forall i, q(i)= 0 \Rightarrow p(i)= 0)) \Rightarrow\\D_{\alpha }(p\Vert \Vert q)= 0 \Leftrightarrow p= q.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/ZeroCharacterization.renyi_divergence_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the unified entry point for every positive order other than one. The exclusion is necessary because the literal totalized definition has value zero at order one for every pair. Together with the preceding nonnegativity result, it completes the missing above-one sign statement and the converse to zero self-divergence on both sides of one.

The unified statement deliberately pays the stronger absolute-continuity hypothesis in order to use one condition on both branches. Under normalization, absolute continuity implies common positive support: some coordinate has p_i > 0, and the contrapositive of absolute continuity makes q_i nonzero there, hence positive by nonnegativity. The converse implication fails in general, so this combined theorem does not erase the greater support generality of the dedicated below-one result.

When alpha < 1, the derived common positive coordinate feeds the weighted AM--GM characterization. When alpha > 1, the theorem invokes the KL squeeze. The case split therefore unifies the conclusion without pretending that the two proof mechanisms or their minimal hypotheses are the same.

The authored display is legal because no pinned projectable statement fixture exists for this declaration; construction records the resulting ProjectionGap.

## References

- Truth anchor: `D5/S3/RenyiDivergence/ZeroCharacterization.renyi_divergence_eq_zero_iff`
- Truth anchor: `D5/S3/RenyiDivergence/ZeroCharacterization.renyi_divergence_eq_zero_iff_of_lt_one`
- Truth anchor: `D5/S3/RenyiDivergence/ZeroCharacterization.renyi_divergence_eq_zero_iff_of_one_lt`
- Truth anchor: `D5/S3/RenyiDivergence/ZeroCharacterization.renyi_divergence_nonneg_of_one_lt`
- Dependency: [D5/S3/Divergence/GibbsEquality](../Divergence/GibbsEquality.md)
- Dependency: [D5/S3/RenyiDivergence/OrderLimits](OrderLimits.md)
