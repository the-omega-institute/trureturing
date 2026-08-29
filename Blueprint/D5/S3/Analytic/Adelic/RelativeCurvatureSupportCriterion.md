# Relative Curvature Support Criterion

## Abstract

The multiplicity-weighted curvature measure of the canonical nontrivial zeta zeros is supported on the critical line exactly when every such zero is critical.

**Theorem 1.1 (Relative curvature is critical exactly under the zeta criterion).**

$$\begin{aligned}Z := \left\{\operatorname{IsNontrivialZero}\left(s\right) \mid s \in \operatorname{Complex}\left(\right)\right\}\\curvature := \operatorname{measureSum}\left((rho: \operatorname{Subtype}\left(Z\right) \mapsto \operatorname{toENNReal}\left(\operatorname{zeroMult}\left(\operatorname{val}\left(rho\right)\right)\right) \cdot \operatorname{dirac}\left(\operatorname{val}\left(rho\right)\right))\right)\\S := \left\{0 < \operatorname{re}\left(s\right) \land \operatorname{re}\left(s\right) < 1 \mid s \in \operatorname{Complex}\left(\right)\right\}\\L := \left\{\operatorname{re}\left(s\right) = \frac{1}{2} \mid s \in \operatorname{Complex}\left(\right)\right\}\\\left(\forall s \in \operatorname{Complex}\left(\right),\; \operatorname{IsNontrivialZero}\left(s\right) \Rightarrow \operatorname{mem}\left(s, L\right)\right) \Leftrightarrow \operatorname{inter}\left(\operatorname{support}\left(curvature\right), S\right) \subseteq L.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/RelativeCurvatureSupportCriterion.relative_curvature_support_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero carrier is the repository's canonical IsNontrivialZero set. Relative curvature is constructed as the Measure.sum of Dirac masses weighted by the canonical analytic multiplicity zeroMult; its support is not installed by definition.

The local proof identifies this carrier with the closed zero locus of the entire xiReading and proves from the measure API that every positive weighted atom, and only such an atom, lies in the support.

Since IsNontrivialZero already records the open critical-strip bounds, the resulting support inclusion is equivalent to the universal critical-line assertion.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/RelativeCurvatureSupportCriterion.relative_curvature_support_criterion`
- Dependency: [D5/S3/Zeros/CompletedZeta](../../Zeros/CompletedZeta.md)
