# Shadowing of Mittag-Leffler Inverse Limits

## Abstract

Finite open cover shadowing passes to arbitrary directed compact Hausdorff limits with stabilized bonding images.

A pseudo-orbit x has each pair f(x(n)), x(n+1) in one member of a control cover. A point z traces it when f iterated n times at z and x(n) share a member of the output cover for every natural n, including zero. Shadowing quantifies over every finite open output cover and all pseudo-orbits.

The stages form a small nonempty cofiltered thin category. In particular, the opposite of any nonempty directed preorder is allowed. Every stage is compact Hausdorff. Bonding maps are continuous and satisfy the functor laws; the continuous stage dynamics form a natural endomorphism. There is no metric, countable cofinal family, invertibility, or onto-map hypothesis.

**Theorem 1.1 (Projection images are intersections of incoming images).**

$$\forall (u: \operatorname{Universe}), \forall (v: \operatorname{Universe}), \forall (J: \operatorname{Type}_u), [\operatorname{SmallCategory}(J)], \forall (F: \operatorname{Functor}(J, \operatorname{TopCat}^{\operatorname{max}(u, v)})), [\operatorname{IsCofiltered}(J)], [\operatorname{Quiver}.\operatorname{IsThin}(J)], [\forall (j: J), \operatorname{Nonempty}(F.\operatorname{obj}(j))], [\forall (j: J), \operatorname{CompactSpace}(F.\operatorname{obj}(j))], [\forall (j: J), \operatorname{T2Space}(F.\operatorname{obj}(j))], \forall (i: J), \operatorname{range}(\operatorname{TopCat}.\operatorname{limitCone}(F).\pi.\operatorname{app}(i)) = \operatorname{Functor}.\operatorname{comp}(F, \operatorname{forget}(\operatorname{TopCat})).\operatorname{eventualRange}(i)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit.compact_projection_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonempty stages, S(i) is the intersection of all incoming bonding images. Fix a in S(i). Impose every compatibility equation and the fiber condition x(i)=a in the compact product. A finite collection is realized by taking a preimage of a at a common finer stage and mapping it to every mentioned coordinate. Compactness supplies a full compatible thread. Conversely, every thread lies in every incoming image.

**Theorem 1.2 (Every finite cover is observed at one stage).**

$$\forall (u: \operatorname{Universe}), \forall (v: \operatorname{Universe}), \forall (J: \operatorname{Type}_u), [\operatorname{SmallCategory}(J)], \forall (F: \operatorname{Functor}(J, \operatorname{TopCat}^{\operatorname{max}(u, v)})), [\operatorname{IsCofiltered}(J)], [\forall (j: J), \operatorname{CompactSpace}(F.\operatorname{obj}(j))], [\forall (j: J), \operatorname{T2Space}(F.\operatorname{obj}(j))], \forall (C: \operatorname{Finset}(\operatorname{Opens}(\operatorname{TopCat}.\operatorname{limitCone}(F).\operatorname{pt}))), \operatorname{IsOpenCover}((\lambda (U: C) \mapsto U.\operatorname{val})) \implies \exists (i: J), \exists (V: \operatorname{Finset}(\operatorname{Opens}(F.\operatorname{obj}(i)))), (\forall (a: F.\operatorname{obj}(i)), a \in \operatorname{range}(\operatorname{TopCat}.\operatorname{limitCone}(F).\pi.\operatorname{app}(i)) \implies \exists (U: \operatorname{Opens}(F.\operatorname{obj}(i))), U \in V \land a \in U) \land (\forall (U: \operatorname{Opens}(F.\operatorname{obj}(i))), U \in V \implies \exists (W: \operatorname{Opens}(\operatorname{TopCat}.\operatorname{limitCone}(F).\operatorname{pt})), W \in C \land \operatorname{TopCat}.\operatorname{limitCone}(F).\pi.\operatorname{app}(i)^{-1}(U: \operatorname{Set}(F.\operatorname{obj}(i))) \subseteq (W: \operatorname{Set}(\operatorname{TopCat}.\operatorname{limitCone}(F).\operatorname{pt})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit.finite_cover_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here C is any finite open cover of the limit L, and union(V) is the union of the finite family V of stage opens. Single-coordinate inverse images of stage opens form a basis of the cofiltered limit. Choose such a neighborhood inside a cover member at each point, take a finite subcover, and move their finitely many stage indices to a common finer stage i. The resulting finite family V covers the actual projection image, and each pulled-back open lies in an original cover member. The projection need not be onto its stage.

**Theorem 1.3 (Mittag-Leffler inverse limits preserve shadowing).**

$$\forall (u: \operatorname{Universe}), \forall (v: \operatorname{Universe}), \forall (J: \operatorname{Type}_u), [\operatorname{SmallCategory}(J)], \forall (F: \operatorname{Functor}(J, \operatorname{TopCat}^{\operatorname{max}(u, v)})), [\operatorname{IsCofiltered}(J)], [\operatorname{Quiver}.\operatorname{IsThin}(J)], [\forall (j: J), \operatorname{CompactSpace}(F.\operatorname{obj}(j))], [\forall (j: J), \operatorname{T2Space}(F.\operatorname{obj}(j))], \forall (d: \operatorname{NatTrans}(F, F)), \operatorname{Functor}.\operatorname{comp}(F, \operatorname{forget}(\operatorname{TopCat})).\operatorname{IsMittagLeffler} \implies (\forall (j: J), \operatorname{HasShadowing}(d.\operatorname{app}(j))) \implies \operatorname{HasShadowing}(\operatorname{limitDynamics}(F, d))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit.shadowing_inverse_limit_of_mittag_leffler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chris Good and Jonathan Meddaugh (2020). *Shifts of finite type as fundamental objects in the theory of shadowing*. DOI: [10.1007/s00222-019-00936-8](https://doi.org/10.1007/s00222-019-00936-8). URL: <https://doi.org/10.1007/s00222-019-00936-8>.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

Assume every stage dynamics has finite-cover shadowing and the bonding images satisfy Mittag-Leffler stabilization: for each i some k above i has the same image in i as every stage above k. Then the coordinatewise dynamics on the full compatible-thread limit has finite-cover shadowing.

Descend an output cover to i, then choose an image-stabilizing bond k to i. Pulling the descended opens back covers the entire original stage k. Shadow the projected pseudo-orbit there. Its shadowing point b need not lift at k. Its image at i belongs to S(i), so the projection-image theorem lifts that coarse point to a full thread z. Naturality at every iterate transfers tracing back to the output cover. No assertion about shadowing restricted to eventual images is needed.

If a stage is empty, the limit is empty and every pseudo-orbit condition is vacuous. Thus the preservation theorem includes empty stages without an extra nonemptiness hypothesis.

This formalizes the inverse-limit preservation theorem of Good and Meddaugh, Inventiones mathematicae 220 (2020), Theorem 8, pp.722-723. Their final Definitions 2-4 allow nonsurjective continuous bonding maps and impose Mittag-Leffler stabilization over arbitrary directed indices. The Lean proof implements the coarse-image lifting argument on a cofiltered thin category, and includes the vacuous empty-stage case. This is attributed known-background infrastructure.

Peng's Question 5.1 asks for a zero-dimensional shadowing extension of every compact Hausdorff shadowing system. This preservation theorem does not construct its coherent all-face symbolic diagram. Simultaneous lifts, sound decoding, and coding of every original orbit remain necessary for that route.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit.compact_projection_image`
- Truth anchor: `D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit.finite_cover_descent`
- Truth anchor: `D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit.shadowing_inverse_limit_of_mittag_leffler`
