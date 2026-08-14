# Hausdorff Dimension of the Naming Space and Its Green Classes

## Abstract

The PiNat naming space and every finite-support green class have dimension log base two of the alphabet size.

**Theorem 1.1 (String measure satisfies the critical mass-distribution bound).**

$$\mu(s) \leq \operatorname{ediam}(s)^{d}$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/MetricGeometry/GreenClassHausdorffDimension.stringMeasure_le_ediam_rpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n = card O and d = logb 2 n. For a non-subsingleton set s of infinite strings, choose the least coordinate m at which some two members differ. Minimality makes every string in s agree with one fixed member on the prefix range m, so s lies in a prefix green class of string measure n^(-m).

The two witnesses that differ at coordinate m have PiNat distance (1/2)^m. Hence the extended diameter of s is at least that scale. The identity ((1/2)^m)^d = n^(-m), obtained from 2^d = n, turns cylinder measure monotonicity into mu(s) <= ediam(s)^d.

If s is subsingleton, it is contained in one point. That point lies in every prefix cylinder, whose masses n^(-m) tend to zero because n > 1; therefore its string measure, and hence the measure of s, is zero.

**Theorem 1.2 (Critical Hausdorff measure equals uniform string measure).**

$$\mu_{H}^{d} = \mu$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/MetricGeometry/GreenClassHausdorffDimension.hausdorffMeasure_eq_stringMeasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mass-distribution bound gives stringMeasure O <= mu_H[d] through Mathlib's le_hausdorffMeasure theorem.

For the reverse normalization, cover the full naming space at level m by all prefix cylinders indexed by Fin m -> O. Every cylinder has extended diameter (1/2)^m, while there are n^m cylinders. Their d-dimensional costs sum exactly to n^m n^(-m) = 1, and the maximum diameter tends to zero.

The finite-cover liminf bound therefore gives mu_H[d](univ) <= 1. The lower measure inequality gives the opposite bound because string measure is a probability measure. Thus critical Hausdorff measure is also a probability measure, and equality follows from order plus equal total mass.

**Theorem 1.3 (The full naming space has dimension log base two of the alphabet size).**

$$\operatorname{dimH}(X) = \operatorname{logb}(2, \operatorname{card}(O))$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/MetricGeometry/GreenClassHausdorffDimension.dimH_univ_eq_namingDim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nontriviality gives n >= 2, so d = logb 2 n is nonnegative and can be passed to the Hausdorff-dimension API as a nonnegative real.

At exponent d the Hausdorff measure of the full space equals the string measure of the full space, namely one. It is therefore both nonzero and finite. Mathlib's critical-measure characterization identifies the Hausdorff dimension with d.

**Theorem 1.4 (Every finite-support green class has full naming-space dimension).**

$$\operatorname{dimH}(G(S, t)) = \operatorname{logb}(2, \operatorname{card}(O))$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/MetricGeometry/GreenClassHausdorffDimension.dimH_greenClass_eq_namingDim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the critical exponent, the Hausdorff measure of G(S,t) is its string measure. The finite-cylinder formula makes this value strictly positive, while probability of the ambient string measure makes it finite. The same critical-measure characterization therefore gives dimH G(S,t) = logb 2 (card O).

Pinning finitely many coordinates changes the critical measure by a positive factor but does not reduce dimension. The varying-marginal generalization to nonuniform coordinate laws remains uncovered.

## References

- Truth anchor: `D5/S0/Asymptotics/MetricGeometry/GreenClassHausdorffDimension.dimH_greenClass_eq_namingDim`
- Truth anchor: `D5/S0/Asymptotics/MetricGeometry/GreenClassHausdorffDimension.dimH_univ_eq_namingDim`
- Truth anchor: `D5/S0/Asymptotics/MetricGeometry/GreenClassHausdorffDimension.hausdorffMeasure_eq_stringMeasure`
- Truth anchor: `D5/S0/Asymptotics/MetricGeometry/GreenClassHausdorffDimension.stringMeasure_le_ediam_rpow`
- Dependency: [D5/S0/Asymptotics/MetricGeometry/GreenClassDiameter](GreenClassDiameter.md)
