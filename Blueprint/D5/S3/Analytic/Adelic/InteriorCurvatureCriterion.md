# Interior Curvature Criterion

## Abstract

The source Riesz-curvature measure has no interior atom exactly when every canonical nontrivial zeta zero lies on the critical line.

**Theorem 1.1 (Interior curvature vanishes exactly under the zeta criterion).**

$$\begin{aligned}Zplus := \left\{\operatorname{IsNontrivialZero}\left(s\right) \land \frac{1}{2} < \operatorname{re}\left(s\right) \mid s \in \operatorname{Complex}\left(\right)\right\}\\z := (rho: \operatorname{Subtype}\left(Zplus\right) \mapsto -\operatorname{im}\left(\operatorname{val}\left(rho\right)\right) + i \cdot (\operatorname{re}\left(\operatorname{val}\left(rho\right)\right) - \frac{1}{2}))\\curvatureInt := \operatorname{measureSum}\left((rho: \operatorname{Subtype}\left(Zplus\right) \mapsto \operatorname{ofReal}\left(2 \cdot pi\right) \cdot \operatorname{toENNReal}\left(\operatorname{zeroMult}\left(\operatorname{val}\left(rho\right)\right)\right) \cdot \operatorname{dirac}\left(\operatorname{z}\left(rho\right)\right))\right)\\\left(\forall s \in \operatorname{Complex}\left(\right),\; \operatorname{IsNontrivialZero}\left(s\right) \Rightarrow \operatorname{re}\left(s\right) = \frac{1}{2}\right) \Leftrightarrow curvatureInt = 0.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/InteriorCurvatureCriterion.interior_curvature_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The right off-line carrier is cut directly from the canonical IsNontrivialZero predicate. Each zero is sent to the source upper-half-plane point with real coordinate minus its ordinate and imaginary coordinate its displacement from one half.

The interior curvature is the Measure.sum of Dirac masses with the source coefficient two pi times the analytic multiplicity. Its vanishing is proved from positivity of every indexed atom, not installed as a definition.

Reflection of a hypothetical left off-line zero produces a right off-line zero, completing the converse implication.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/InteriorCurvatureCriterion.interior_curvature_criterion`
