# Fixed dyadic positive excess kurtosis

## Abstract

The fourth Brownian interface determines two dyadic moment limits and positive excess kurtosis.

Let E be a real locally bounded Borel measurable function, let 0<alpha<theta<beta<1, and let g be a real measurable integrable profile on the unit interval. Assume the cumulative variance asymptotic and fourth-moment bound throughout the exponent band. Write kappa=1-theta, Q(g)=integral g(s)g(t)min(s,t) ds dt, and Z_X(x)=profileResponse(E,theta,g,x)/sqrt(X^kappa log(X)). Expectations use dx/(x log(2)) on [X,2X].

**Theorem 1.1 (Normalized second profile moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentKurtosis.dyadicZ_second_moment_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthMomentKurtosis.dyadicZ_second_moment_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For locally bounded Borel measurable E, a valid exponent band 0<alpha<theta<beta<1 with the cumulative variance asymptotic, and a measurable integrable real profile g, E[Z_X^2] tends to (2^(1-theta)-1)*Q(g)/log(2). Apply moment transfer at order two to the variance-band interface with kernel kappa*dyadicMacroMoment(kappa)*min(s,t). Its profile-weighted integral is kappa*dyadicMacroMoment(kappa)*Q(g), since the Brownian pair kernel integrates to Q(g). The formula dyadicMacroMoment(kappa)=(2^kappa-1)/(kappa*log(2)) gives the stated limit.

**Theorem 1.2 (Second and fourth moments with strict excess kurtosis).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentKurtosis.fixed_dyadic_positive_excess_kurtosis`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthMomentKurtosis.fixed_dyadic_positive_excess_kurtosis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume for every four unit-interval parameters that the mixed normalized increment moment with position factor (x/X)^(2*kappa) tends to c4*kappa^2 times the sum of the three Brownian covariance pairings, where c4=(2^(2*kappa)-1)/(2*kappa*log(2)). Then E[Z_X^2] tends to L2=(2^kappa-1)*Q(g)/log(2), and E[Z_X^4] tends to L4=3*kappa*(2^(2*kappa)-1)*Q(g)^2/(2*log(2)). If g is not almost everywhere zero, 3*L2^2<L4.

The normalized second-moment theorem gives L2. The fourth-moment band bound supplies the uniform absolute-moment part of the fourth moment interface; the Brownian pairing function is measurable and the assumed mixed-moment limits supply its remaining part. Applying the general moment-transfer theorem with k=4 and the Brownian pairing integral gives L4. Positivity of Q(g) and the strict dyadic kurtosis ratio inequality give 3*L2^2<L4.

This conclusion is conditional on the fourth-order Brownian interface. It does not establish that interface for the Chebyshev error or assert convergence in distribution.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentKurtosis.dyadicZ_second_moment_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentKurtosis.fixed_dyadic_positive_excess_kurtosis`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel](BrownianFourthKernel.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthMomentInterfaceBridge](FourthMomentInterfaceBridge.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MomentTransfer](MomentTransfer.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/ProfileQuadraticForm](ProfileQuadraticForm.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface](SecondOrderInterface.md)
