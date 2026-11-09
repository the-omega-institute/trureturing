# Dyadic normalization

## Abstract

Fixed-scale mixed moments with homogeneous kernels give dyadic moment interfaces.

Write h=X^theta, u=x/X, and B(s,x)=D_(s*x^theta)(x)/sqrt(x^theta*log(x)). The local fourth-energy estimate controls the fixed-scale normalized increments D_(h*b(u))(x)/sqrt(h*log(X)).

**Theorem 1.1 (Uniform logarithmic correction).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentDyadicTransfer.logarithmic_correction_eventually`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentDyadicTransfer.logarithmic_correction_eventually` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k and eta>0, all sufficiently large X satisfy |sqrt(log(X)/log(x))^k-1|<eta throughout [X,2X]. This also controls the product of k identical logarithmic corrections. The correction λ = √(log X / log x) lies in [0,1], with |λ − 1| ≤ log 2 / log X.

**Theorem 1.2 (Exact change of normalization).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentDyadicTransfer.dyadicB_eq_movingB`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentDyadicTransfer.dyadicB_eq_movingB` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<theta<1, X>1 and x in [X,2X], put u=x/X and lambda=sqrt(log(X)/log(x)). Then B(s,x)=lambda*u^(-theta/2)*movingB(s*u^theta,X,x). The two increments have exactly the same length, and the positive square roots give the displayed normalization.

**Theorem 1.3 (Uniform dyadic fourth moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentDyadicTransfer.dyadic_fourth_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentDyadicTransfer.dyadic_fourth_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be locally bounded and Borel measurable, let 0<alpha<theta<beta<1, and assume the local fourth-energy estimate with constant C. For every sufficiently large X, uniformly in s in [0,1], the dyadic probability integral of |B_X(s)|^4 is at most fourthK(C,2)=5248*C/log(2). The length b(u)=s*u^theta has size at most two and derivative at most one. In the exact normalization identity both the logarithmic factor and u^(-theta/2) are at most one, so the moving fourth-moment bound applies.

**Theorem 1.4 (The homogeneous dyadic moment interface).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentDyadicTransfer.fixed_scale_dyadic_interface`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentDyadicTransfer.fixed_scale_dyadic_interface` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the local fourth-energy estimate, 0<alpha<theta<beta<1, a positive integer k<=4, and the interval-weighted fixed-scale mixed-moment limit with continuous kernel W. Suppose W(s*u^theta)=u^(k*theta/2)*W(s) for s in the unit cube and u in [1,2]; degree k/2 homogeneity for nonnegative dilations implies this condition. Then MomentInterface holds with kernel dyadicMacroMoment(k*r)*W, where r=(1-theta)/2. Apply moving_mixed_moments_tendsto to b_i(u)=s_i*u^theta and w(u)=u^(k*r-k*theta/2). The uniformly vanishing logarithmic correction multiplies a product with bounded absolute expectation, by the fourth-moment product bound. Homogeneity leaves the macroscopic integral of u^(k*r). The uniform fourth bound also bounds every absolute moment of order k<=4.

For k=3 specialize the general continuous kernel to W₃(s)=0. Its homogeneity identity holds since both sides vanish, and the resulting moment interface has zero kernel. For k=4 specialize to W₄(s)=κ²·brownianW4(s), where κ=1−theta. The Brownian pairing kernel scales quadratically, and dyadicMacroMoment(4*r)=dyadicMomentConstant(theta), giving the limit dyadicMomentConstant(theta)*kappa(theta)^2*brownianW4(s), precisely the fourth mixed-moment hypothesis used by fixed_dyadic_positive_excess_kurtosis. Together with the cumulative second-order variance asymptotic and the uniform fixed-length fourth asymptotic, asymptotic_implies_band and asymptotic_implies_local supply the remaining fourth-energy bounds. Thus the existing kurtosis theorem gives the explicit second and fourth profile moments and the strictly positive excess for a nonzero profile. These implications are conditional; the fixed-length mixed-moment and asymptotic hypotheses for the prime-counting error are not proved here.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentDyadicTransfer.dyadicB_eq_movingB`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentDyadicTransfer.dyadic_fourth_uniform`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentDyadicTransfer.fixed_scale_dyadic_interface`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentDyadicTransfer.logarithmic_correction_eventually`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel](../BrownianFourthKernel.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments](../DyadicMacroMoments.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface](../FirstOrderInterface.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentMovingTransfer](FourthMomentMovingTransfer.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MomentTransferWeights](../MomentTransferWeights.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface](../SecondOrderInterface.md)
