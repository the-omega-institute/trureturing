# Varying-Marginal Green-Class Measure

## Abstract

Varying probability marginals give exact green-class product mass and critical Hausdorff measure comparisons.

**Theorem 1.1 (A green class has the product of its pinned marginal masses).**

$$\mu_{\infty}(G(S, t)) = \prod_{i \in S} \mu_{i}(\{{t_{i}}\})$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure.varying_greenClass_measure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let mu_i be probability measures on a common measurable alphabet whose singletons are measurable. The green class G(S,t) is the finite cylinder that pins coordinate i to t_i for each i in S.

Mathlib's infinitePi_pi theorem evaluates this cylinder directly. Its measure is the finite product over i in S of the singleton masses mu_i({t_i}); no uniformity or finiteness assumption on the alphabet is needed for this identity.

**Theorem 1.2 (Green-class mass is positive exactly when every pinned mass is positive).**

$$0 < \mu_{\infty}(G(S, t)) \iff \forall i \in S, 0 < \mu_{i}(\{{t_{i}}\})$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure.varying_greenClass_measure_pos_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting the exact cylinder formula reduces positivity to positivity of a finite product in the extended nonnegative reals.

CanonicallyOrderedAdd.prod_pos states that such a finite product is strictly positive exactly when every factor indexed by S is strictly positive, including the empty-support case.

**Theorem 1.3 (Upper marginal bounds place varying mass below critical Hausdorff measure).**

$$\mu_{\infty}(G(S, t)) \leq \mu_{H}^{d}(G(S, t))$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure.varying_greenClass_measure_le_hausdorffMeasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n = card O and d = namingDim O. If every pinned singleton mass is at most n^(-1), finite-product monotonicity bounds the varying cylinder mass by n^(-|S|).

The uniform green-class formula identifies n^(-|S|) with uniform string measure of G(S,t), and the frozen critical-measure equality identifies that value with the Hausdorff measure at exponent d.

**Theorem 1.4 (Lower marginal bounds place critical Hausdorff measure below varying mass).**

$$\mu_{H}^{d}(G(S, t)) \leq \mu_{\infty}(G(S, t))$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure.hausdorffMeasure_le_varying_greenClass_measure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every pinned singleton mass is at least n^(-1), finite-product monotonicity places n^(-|S|) below the varying cylinder mass.

Rewriting the critical Hausdorff measure of G(S,t) as uniform string measure, then applying the uniform cylinder value, supplies exactly that lower product.

## References

- Truth anchor: `D5/S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure.hausdorffMeasure_le_varying_greenClass_measure`
- Truth anchor: `D5/S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure.varying_greenClass_measure`
- Truth anchor: `D5/S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure.varying_greenClass_measure_le_hausdorffMeasure`
- Truth anchor: `D5/S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure.varying_greenClass_measure_pos_iff`
- Dependency: [D5/S0/Asymptotics/MetricGeometry/GreenClassHausdorffDimension](GreenClassHausdorffDimension.md)
