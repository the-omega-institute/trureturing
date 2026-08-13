# Finite Order Comparisons for Renyi Divergence

## Abstract

Finite, limit-free comparisons of Renyi divergence with its supremum-ratio ceiling and KL order member.

**Theorem 1.1 (Renyi divergence is bounded by the logarithmic supremum ratio).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)] [\operatorname{Nonempty}(\iota)],\\\forall \alpha \in \mathbb{R}, \forall p, q: \iota\to \mathbb{R},\\1< \alpha,\\((\forall i, 0\le p(i)) \land \sum _{i} p(i)=1) \land (\forall i, 0< p(i) \Rightarrow 0< q(i)))\Rightarrow\\D_{\alpha }(p\Vert \Vert q)\le \log (\operatorname{sup}_{i}(p(i)/q(i)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/OrderLimits.renyi_divergence_le_log_sup_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For alpha > 1, the finite Renyi divergence is at most the logarithm of the largest likelihood ratio p(i)/q(i). This is the finite, limit-free content of the phrase alpha -> infinity: it gives a usable supremum-ratio ceiling without asserting that any topological limit exists.

The proof rewrites the power sum as the p-weighted moment of the likelihood ratio, bounds every ratio by its finite supremum, and then uses monotonicity of real powers and logarithms. Normalized nonnegative p supplies a positive support coordinate; the hypothesis on q makes the relevant ratios positive.

The supremum is a Finset supremum over the finite index type, not a newly named max-divergence. The theorem therefore remains entirely inside the existing totalized finite formula and introduces no additional object or variational characterization.

**Theorem 1.2 (The Renyi logarithmic moment dominates KL).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)),\\\forall \alpha \in \mathbb{R}, 0< \alpha,\\\forall p, q: \iota\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum _{i} p(i)=1) \land (\forall i, 0< p(i) \Rightarrow 0< q(i))\Rightarrow\\(\alpha-1) * \operatorname{klDivergence}(p\Vert \Vert q)\le \log (\sum _{i} p(i)^{\alpha } q(i)^{1-\alpha}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/OrderLimits.renyi_log_moment_ge_kl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This logarithmic moment inequality is the Jensen step underlying both comparisons with Kullback--Leibler divergence. It relates the finite power sum to KL before any division by alpha - 1, so the sign of that denominator can be handled explicitly in the two order ranges.

On the positive support of p, the likelihood ratio is positive by the stated reference-mass condition. Concavity of the logarithm with p as the normalized weight yields (alpha - 1) * KL <= log of the power sum. Coordinates outside the support contribute zero and are removed by the finite-support rewrite.

The result is a structural inequality, not an order-one identification. In particular, it does not turn Lean's totalized alpha = 1 value into KL.

**Theorem 1.3 (Below one, Renyi divergence is at most KL).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)),\\\forall \alpha \in \mathbb{R},\\\forall p, q: \iota\to \mathbb{R},\\(0< \alpha \land \alpha< 1) \Rightarrow\\((\forall i, 0\le p(i)) \land \sum _{i} p(i)=1) \land (\forall i, 0< p(i) \Rightarrow 0< q(i))\Rightarrow\\D_{\alpha }(p\Vert \Vert q)\le \operatorname{klDivergence}(p, q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/OrderLimits.renyi_divergence_le_kl_of_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0 < alpha < 1, the finite Renyi divergence is at most KL divergence under the same nonnegative normalized p and positive-on-p-support q hypotheses. This is one half of the finite comparison around order one.

Jensen first gives (alpha - 1) * KL <= the logarithmic power sum. Because alpha - 1 is negative below one, dividing by it reverses the inequality. That sign flip is why the sub-one statement is a separate theorem rather than an unqualified symmetric slogan.

The theorem says nothing about a topological limit as alpha approaches one; it is a pointwise finite inequality for each admissible alpha.

**Theorem 1.4 (Above one, KL is at most Renyi divergence).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)),\\\forall \alpha \in \mathbb{R},\\\forall p, q: \iota\to \mathbb{R},\\1< \alpha \Rightarrow\\((\forall i, 0\le p(i)) \land \sum _{i} p(i)=1) \land (\forall i, 0< p(i) \Rightarrow 0< q(i))\Rightarrow\\\operatorname{klDivergence}(p, q)\le D_{\alpha }(p\Vert \Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/OrderLimits.kl_le_renyi_divergence_of_one_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For alpha > 1, KL divergence is at most the finite Renyi divergence at order alpha. It is the super-one counterpart to the preceding comparison and uses exactly the same finite logarithmic moment inequality.

Here alpha - 1 is positive, so division preserves the Jensen direction. The single denominator sign change explains the split into below-one and above-one theorems: Jensen supplies the common engine, while order determines the final inequality direction.

This is a comparison with the KL expression as a finite order member. It does not identify the totalized order-one value of Renyi divergence with KL and does not establish convergence to it.

**Theorem 1.5 (The half-order Renyi divergence is at most KL).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)),\\\forall p, q: \iota\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum _{i} p(i)=1) \land (\forall i, 0< p(i) \Rightarrow 0< q(i))\Rightarrow\\-2 * \log (\operatorname{bhattacharyya}(p, q))\le \operatorname{klDivergence}(p, q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/OrderLimits.renyi_divergence_one_half_le_kl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At alpha = 1/2, the below-one comparison specializes to the frozen Bhattacharyya expression: minus twice the logarithm of the Bhattacharyya coefficient is at most KL divergence. This records consistency with the already established half-order result rather than introducing a new notion.

The specialization keeps the same support assumptions as the general below-one theorem. Positive q on the positive support of p makes the logarithmic moment argument finite under the repository's totalized real operations.

The four narrative points are deliberate. The bucket previously had order monotonicity, power and product additivity, data processing, the half-order case, nonnegativity, and self-zero, but nothing relating the family to its limiting members; that gap was found by reading the existing declaration list, not by guessing from this title.

The results here are stated without limits deliberately. Alpha -> infinity is represented by a finite supremum-ratio ceiling, and alpha -> 1 by two-sided comparison with KL. There is no topology, no tendsto statement, and nothing is named as a limit, because no limit is proved.

What is not proved is equally important: no topological limit at infinity or at one, no named max-divergence, no variational formula, and no identification of the totalized order-one value with KL. That last step can look obvious, but it requires its own proof and is intentionally absent from the Lean module.

## References

- Truth anchor: `D5/S3/RenyiDivergence/OrderLimits.kl_le_renyi_divergence_of_one_lt`
- Truth anchor: `D5/S3/RenyiDivergence/OrderLimits.renyi_divergence_le_kl_of_lt_one`
- Truth anchor: `D5/S3/RenyiDivergence/OrderLimits.renyi_divergence_le_log_sup_ratio`
- Truth anchor: `D5/S3/RenyiDivergence/OrderLimits.renyi_divergence_one_half_le_kl`
- Truth anchor: `D5/S3/RenyiDivergence/OrderLimits.renyi_log_moment_ge_kl`
- Dependency: [D5/S3/RenyiDivergence/Monotone](Monotone.md)
