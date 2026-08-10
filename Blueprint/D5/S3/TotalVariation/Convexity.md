# Joint Convexity of Total Variation and Squared Hellinger Distance

## Abstract

Total variation is jointly convex without mass hypotheses, while squared Hellinger distance is jointly convex on the nonnegative quadrant.

**Theorem 1.1 (Total variation is jointly convex for arbitrary real functions).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p_{1}, p_{2}, q_{1}, q_{2}: \iota\to \mathbb{R}, t\in \mathbb{R},\\(0\le t \land t\le 1) \Rightarrow \\\operatorname{TV}(t p_{1}+(1-t) p_{2}, t q_{1}+(1-t) q_{2})\le \\t \operatorname{TV}(p_{1}, q_{1})+(1-t) \operatorname{TV}(p_{2}, q_{2}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Convexity.total_variation_joint_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The repository already established joint convexity for Kullback--Leibler divergence. The present total-variation theorem and the squared-Hellinger theorem below complete the corresponding picture for the statistical distances developed here: mixing two pairs of laws cannot leave their mixed separation above the weighted average of the two endpoint separations.

The three joint-convexity statements expose a precise hierarchy of hypotheses. Finite Kullback--Leibler divergence, measured in nats, requires pointwise nonnegativity and discrete absolute continuity. Its definition contains both division and the natural logarithm. In Lean's totalized arithmetic, positive source mass over zero reference mass would be flattened by division by zero and the ensuing logarithm at zero; the support condition excludes exactly this false finite-cost case.

Total variation contains neither operation. It uses only coordinatewise absolute values and a finite sum, so the theorem assumes nothing at all about the four mass functions: they may be arbitrary real-valued functions. The sole hypothesis is 0 <= t <= 1, and it enters only to replace |t| by t and |1-t| by 1-t in the absolute-value triangle inequality. The caller separately verified this advertised generality by applying the theorem to functions taking negative values.

Squared Hellinger distance likewise contains no division and no logarithm, so it pays no support condition. It does, however, use square roots. The squared square-root gap is jointly convex only on the nonnegative quadrant, and this geometric step alone forces pointwise nonnegativity of all four functions. Thus every hypothesis in the three results is charged to a specific operation in the corresponding definition: absolute value costs only nonnegative mixing weights, square root costs the nonnegative quadrant, and division with logarithm also costs discrete absolute continuity.

**Theorem 1.2 (The squared square-root gap is jointly convex under mixing).**

$$\begin{gathered}\forall a_{1}, a_{2}, b_{1}, b_{2}, t\in \mathbb{R},\\(0\le t \land t\le 1) \land\\(0\le a_{1} \land 0\le a_{2} \land 0\le b_{1} \land 0\le b_{2}) \Rightarrow\\(\sqrt {t a_{1}+(1-t) a_{2}}-\sqrt {t b_{1}+(1-t) b_{2}})^{2}\le \\t (\sqrt {a_{1}}-\sqrt {b_{1}})^{2}+(1-t) (\sqrt {a_{2}}-\sqrt {b_{2}})^{2}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Convexity.sq_sqrt_mix_sub_sqrt_mix_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The named scalar lemma sq_sqrt_mix_sub_sqrt_mix_le carries the Hellinger half of the module. It compares the squared square-root gap of two mixtures with the corresponding mixture of squared endpoint gaps. The finite-dimensional theorem below is obtained by applying this result coordinatewise and summing.

The pinned mathlib supplies the one-variable theorem Real.strictConcaveOn_sqrt and the finite Cauchy--Schwarz inequality Real.sum_sqrt_mul_sqrt_le, but its searched API contains no concavity theorem for the two-variable geometric mean (a,b) |-> sqrt(a b). The missing two-variable statement is the actual scalar content needed here, so it is proved in this module rather than imported.

The proof specializes the finite Cauchy--Schwarz inequality to the two mixing components, obtaining concavity of the geometric-mean cross term. After expanding each squared square-root difference, linear terms agree and that cross-term inequality gives the result. Naming the lemma as a standalone reusable theorem records the unavailable library fact and keeps it from being buried inside the finite-sum convexity proof.

**Theorem 1.3 (Squared Hellinger distance is jointly convex on the nonnegative quadrant).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p_{1}, p_{2}, q_{1}, q_{2}: \iota\to \mathbb{R}, t\in \mathbb{R},\\(0\le t \land t\le 1) \land\\(\forall i, 0\le p_{1}(i) \land 0\le p_{2}(i) \land 0\le q_{1}(i) \land 0\le q_{2}(i)) \Rightarrow\\H^{2}(t p_{1}+(1-t) p_{2}, t q_{1}+(1-t) q_{2})\le \\t H^{2}(p_{1}, q_{1})+(1-t) H^{2}(p_{2}, q_{2}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Convexity.hellinger_sq_joint_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the scalar lemma at each coordinate and summing proves joint convexity of squared Hellinger distance for arbitrary finite pointwise-nonnegative mass functions. Neither endpoint pair is required to have unit total mass, and neither pair is subject to a support condition. The proof uses pointwise nonnegativity only when invoking the scalar square-root result.

Neither convexity inequality is secretly an equality. On Unit with t = 1/2, take (p1,q1) = (1,0) and (p2,q2) = (0,1). The endpoint pairs are opposite, while both mixtures equal the constant one half; hence the mixture distance is zero. The weighted endpoint distance is one half for total variation and one for squared Hellinger distance. In this witness, mixing destroys all separation.

These strict witnesses are compiled in the formal module. For each full joint-convexity statement, the additional checks that neither rfl nor simp closes the goal are themselves compiled fail_if_success obligations, rather than informal reports about tactic behavior.

No strict-convexity theorem or characterization of the equality cases is claimed. The module does not separately state convexity in one argument with the other fixed, and it provides no measure-theoretic analogue. It also introduces no normalization assumptions beyond those absent from the displayed declarations.

## References

- Truth anchor: `D5/S3/TotalVariation/Convexity.hellinger_sq_joint_convex`
- Truth anchor: `D5/S3/TotalVariation/Convexity.sq_sqrt_mix_sub_sqrt_mix_le`
- Truth anchor: `D5/S3/TotalVariation/Convexity.total_variation_joint_convex`
- Dependency: [D5/S3/TotalVariation/Hellinger](Hellinger.md)
