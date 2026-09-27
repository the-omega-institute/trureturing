# Two-Moment Support Hole

## Abstract

Moving probability atoms determine the exact price of excluding a support interval from a noisy two-moment model.

**Definition 1.1 (Actual finite probability pairs).**

$$M_{H}(a,b,\varepsilon) = \{w \mid 0 \le w \land \exists n,m \in \mathbb{N}, z,u: \operatorname{Fin}\left(n\right) \to \mathbb{R}, y,v: \operatorname{Fin}\left(m\right) \to \mathbb{R}, (\forall i, a \le \operatorname{z}\left(i\right) \land \operatorname{z}\left(i\right) < 1 \land \neg(\operatorname{z}\left(i\right) \in H)) \land (\forall j, \operatorname{y}\left(j\right) \in [a, b]) \land (\forall i, 0 \le \operatorname{u}\left(i\right)) \land (\forall j, 0 \le \operatorname{v}\left(j\right)) \land w+\sum_{i} \operatorname{u}\left(i\right) = 1 \land \sum_{j} \operatorname{v}\left(j\right) = 1 \land \lvert w+\operatorname{Prony}\left(z, u, 1\right)-\operatorname{Prony}\left(y, v, 1\right) \rvert \le \varepsilon \land \lvert w+\operatorname{Prony}\left(z, u, 2\right)-\operatorname{Prony}\left(y, v, 2\right) \rvert \le \varepsilon \}$$

*Formalization.* `D5/S3/Analytic/TwoMomentSupportHole.twoMomentMassSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The designated atom is at one. Residual nodes lie in [a,1), outside the specified hole, and comparison nodes lie in [a,b]. Both measures have nonnegative weights and total mass one. The first two actual Prony moments differ by at most epsilon. Arbitrary finite cardinalities are allowed, and the exclusion of one from residual nodes makes w the actual endpoint mass.

**Theorem 1.2 (Attained maxima and exact support-loss law).**

$$\forall a,b,l,r,t \in \mathbb{R}, (0 \le a \land a < b \land b < 1 \land a \le l \land l < r \land r \le b \land l \le t \land t \le r \land 2t \le a+b \land l+r \le a+b) \longrightarrow \text{let } \varepsilon := \frac{(1-b)(b-t)}{2+t}; c := \frac{(1-b)(2+b)}{2+t}; w_{c} := 1-\frac{c}{1-t}; w_{h} := \frac{(b-l)(b-r)+\varepsilon(1+l+r)}{(1-l)(1-r)}; \operatorname{IsGreatest}\left(M_{\emptyset}(a,b,\varepsilon), w_{c}\right) \land \operatorname{IsGreatest}\left(M_{(l,r)}(a,b,\varepsilon), w_{h}\right) \land w_{c}-w_{h} = \frac{(1-w_{c})(t-l)(r-t)}{(1-l)(1-r)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/TwoMomentSupportHole.two_moment_support_hole_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the stated continuous geometric parameters, epsilon=(1-b)(b-t)/(2+t) yields a moving residual atom at t in the unrestricted optimizer. Excluding (l,r) replaces it by explicit nonnegative masses at l and r. Both optimizers are normalized and saturate the actual first two moment errors. Quadratic certificates bound all competing finite laws and yield two IsGreatest conclusions. Their exact difference is (1-wc)(t-l)(r-t)/((1-l)(1-r)), including boundary zero loss. The complete all-noise curve, fixed-grid consequence and optimal transformed grid have ordinary proofs in the theory; this declaration formalizes the general moving-support and hole comparison.

## References

- Truth anchor: `D5/S3/Analytic/TwoMomentSupportHole.twoMomentMassSet`
- Truth anchor: `D5/S3/Analytic/TwoMomentSupportHole.two_moment_support_hole_sharp`
- Dependency: [D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction](GoldenTomography/FinitePronyHankelReconstruction.md)
