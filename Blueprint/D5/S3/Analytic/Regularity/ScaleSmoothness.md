# Smoothness Across Normed-Space Grades

## Abstract

A derivative relation across a scale of real normed spaces gives smooth paths on a closed interval.

**Theorem 1.1 (Smoothness from derivatives at a shifted grade).**

$$\begin{aligned}\forall E : \mathbb{N} \to Type, [\forall m : \mathbb{N}, \operatorname{NormedAddCommGroup}(\operatorname{E}(m))],\\{}[\forall m : \mathbb{N}, \operatorname{NormedSpace}(\mathbb{R}, \operatorname{E}(m))],\\\forall r : \mathbb{N}, \forall T : \mathbb{R}, 0<T \Rightarrow\\\forall u : \prod_{m\in\mathbb{N}}(\mathbb{R} \to \operatorname{E}(m)), \forall F : \prod_{m\in\mathbb{N}}(\operatorname{E}(m+r) \to \operatorname{E}(m)), \\(\forall m : \mathbb{N}, \operatorname{ContDiff}(\mathbb{R}, \infty, \operatorname{F}(m))) \Rightarrow\\(\forall m : \mathbb{N}, \forall t : \mathbb{R}, t\in[0,T] \Rightarrow \operatorname{HasDerivWithinAt}(\operatorname{u}(m), \operatorname{F}(m)(\operatorname{u}(m+r)(t)), [0,T], t)) \Rightarrow\\\forall m : \mathbb{N}, \operatorname{ContDiffOn}(\mathbb{R}, \infty, \operatorname{u}(m), [0,T]).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Regularity/ScaleSmoothness.cont_diff_on_scale_of_has_deriv_within_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be any family of types indexed by the natural numbers. For every grade m, give E(m) a normed additive commutative group structure and a compatible real normed vector space structure. Let r be any natural number, including zero, and let T be any positive real number. For every m, choose a path u(m) from the real line to E(m) and a map F(m) from E(m+r) to E(m). The products in the formula denote these families of functions, with the indicated domain and codomain at each grade.

Assume F(m) is infinitely continuously differentiable over the reals for every natural grade m. Assume also that for every natural m and every real t in the closed interval [0,T], the derivative of u(m) within [0,T] exists and equals F(m)(u(m+r)(t)). Then u(m) is infinitely continuously differentiable within [0,T] for every natural m. Both the derivative hypothesis and the conclusion include t=0 and t=T; smoothness here is relative to the closed interval.

The proof establishes each finite differentiability order simultaneously at all grades. At order zero, the derivative hypothesis gives continuity of each path on [0,T]. For the successor step, suppose every path has order n. In particular, u(m+r) has order n. Composing it with the smooth map F(m) gives an order n function into E(m). Since T is positive, derivatives within [0,T] are unique, so this composition equals the derivative within [0,T] of u(m). The successor criterion for continuous differentiability therefore gives order n+1 at grade m. This holds for all m, closing the induction. Having every finite order yields infinite continuous differentiability at each grade.

No completeness or finite-dimensionality of the spaces is required. Continuity of the paths follows from the derivative hypothesis. The family needs no inclusions or norm comparisons between different grades: the maps F(m) provide the stated relations between them.

## References

- Truth anchor: `D5/S3/Analytic/Regularity/ScaleSmoothness.cont_diff_on_scale_of_has_deriv_within_at`
