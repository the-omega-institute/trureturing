# Cross exponent joint moments

## Abstract

Under the variance and joint fourth-moment hypotheses, separated exponents have vanishing cross moments and a strictly positive limiting covariance of their squares when neither profile vanishes almost everywhere.

**Theorem 1.1 (Vanishing first cross moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentJointMoments.jointZ_first_moment_tendsto_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CrossExponentJointMoments.jointZ_first_moment_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be locally bounded and Borel measurable, with variance-band asymptotics on bands 0<alpha1<a<beta1<1 and 0<alpha2<b<beta2<1, and assume a<b. For any two integrable profiles, the dyadic expectation of the normalized product of their profile responses tends to zero. The proof uses the three-scale power saving for the profile cross integral and the exact product of the two normalization scales.

**Theorem 1.2 (Vanishing universal cross kernel).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentJointMoments.cross_exponent_kernel_integral_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CrossExponentJointMoments.cross_exponent_kernel_integral_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be locally bounded and Borel measurable, with variance-band asymptotics on bands 0<alpha1<a<beta1<1 and 0<alpha2<b<beta2<1, and assume a<b. Suppose that for every (s,t) in the closed unit square, the dyadic expectation of U_X^{r_a+r_b} B_{a,X}(s) B_{b,X}(t) tends to M(s,t), where U_X=x/X and r_a=(1-a)/2, r_b=(1-b)/2. Then the integral of g1(s)g2(t)M(s,t) over the unit square is zero for every pair of real integrable profiles. Joint moment transfer identifies this integral with the vanishing first cross moment, and uniqueness of limits gives the conclusion.

**Theorem 1.3 (Positive correlation of mixed squares).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentJointMoments.cross_exponent_squares_positive_correlation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CrossExponentJointMoments.cross_exponent_squares_positive_correlation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be locally bounded and Borel measurable, with variance-band asymptotics and fourth-moment band bounds on bands 0<alpha1<a<beta1<1 and 0<alpha2<b<beta2<1, and assume a<b. For integrable profiles and a Brownian joint fourth-moment interface with bounded measurable cross kernel, the dyadic expectation of the normalized product tends to zero and the mixed square moment tends to the product of the two energies multiplied by the summed macroscopic moment and the two kappa factors. Subtracting the separate second-moment limits yields the covariance constant. Under these hypotheses, the strict macroscopic moment inequality and positivity of both profile energies make this covariance strictly positive whenever neither profile vanishes almost everywhere.

These are conditional results on abstract interfaces. Nothing here establishes the required interfaces or their conclusions for E = psi - id. The almost-everywhere vanishing of the kernel, Corollary 495.4, and Proposition 495.5 are not formalized here.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentJointMoments.cross_exponent_kernel_integral_zero`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentJointMoments.cross_exponent_squares_positive_correlation`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentJointMoments.jointZ_first_moment_tendsto_zero`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/CrossExponentOrthogonality](CrossExponentOrthogonality.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthMomentKurtosis](FourthMomentKurtosis.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/JointBrownianKernel](JointBrownianKernel.md)
