# The same original source and its complete theta transform

## Abstract

Original-source mean-zero moments and actual Gamma-profile L1 and L2 domains.

**Theorem 1.1 (Both actual Laplace moments, both L1 domains and the product estimate).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanZeroTrace.actual_h6_mean_zero_physical_moment_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanZeroTrace.actual_h6_mean_zero_physical_moment_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original function F:R->C satisfying originalPhysicalH6 F, retain the literal complete theta transform fullTheta F and its actualGammaProfile F. Define B_F(t)=actualGammaProfile F(t)-(3/2)*rightExponentialTail(5/4,actualGammaProfile F)(t), and the actual even profile by B_F(2*abs(r)). The additional hypothesis is exactly that this even profile has zero integral over the whole real line. No endpoint trace is assumed to vanish.

Let L0 be the integral over t>0 of exp(-5*t/4)*actualGammaProfile F(t), let Lt be the integral over t>0 of t*exp(-5*t/4)*actualGammaProfile F(t), and let D be the integral over x>pi of ((x/pi)^6-1)*norm(fullTheta F(x))^2. Both complex integrands defining L0 and Lt are L1 on t>0. The three bounds are norm(L0)^2 <= (3/1000)*pi^(7/2)*D, norm(Lt)^2 <= (3/160)*pi^(7/2)*D, and norm(L0)*norm(Lt) <= (3/400)*pi^(7/2)*D. All five conclusions hold for each original F under its H6 and actual mean-zero hypotheses.

The physical coordinate identities compute the actual profile mass and endpoint tail. The even-profile mass identity converts mean zero into 5*L0 = integral((x^(5/4)-pi^(5/4))*fullTheta F(x),x>pi), retaining the endpoint trace. A logarithmic change of variables identifies Lt with pi^(5/4) times the physical log moment. The original H6 condition supplies H6 for fullTheta F; applying actual_h6_weighted_physical_moments to that transform gives the two squared estimates, whose product gives the final bound.

The theorem actual_h6_mean_zero_positive_fullTheta_excess_all_gamma_domains in ActualSuzukiFiniteMeanZeroWitness constructs one source satisfying H6, actual even-B mean zero, every real constant-shift Gamma form domain, the complete same-input HasSum, positive original excess and positive fullTheta excess. The HasSum identifies fullTheta with that source on x>=pi. This construction supplies a nontrivial mean-zero example; the moment law itself quantifies over every original F with its stated hypotheses and assumes no realization theorem.

This is a quantitative dependency for the stronger original-F Gamma lower comparison. That comparison keeps its original source F, actual mean-zero hypothesis and separately required Gamma form domain. This moment law does not derive that domain from H6, does not replace original excess by transformed excess in the comparison, and does not settle RH. No literature novelty is claimed for this synthesis.

**Theorem 1.2 (Actual positive-half-line profile L1 and L2 from the original H6 source).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanZeroTrace.actual_h6_gamma_profile_l1_l2`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanZeroTrace.actual_h6_gamma_profile_l1_l2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original F:R->C satisfying originalPhysicalH6 F, the actualGammaProfile F is IntegrableOn on Ioi 0 and belongs to MemLp 2 for volume restricted to Ioi 0. Both domain conclusions belong to the same full law. This law has no mean-zero premise and no assumed convergence or desired domain conclusion.

The L1 clause follows from the physical coordinate identities. For L2, H6 for fullTheta F makes x^(7/2)*norm(fullTheta F(x))^2 integrable on x>pi by domination with its sixth moment, since pi>1. The substitution x=pi*exp(t), with its Jacobian and the exponent 9/4 in actualGammaProfile, gives the square-norm integral on t>0. The MemLp conclusion follows from integrability of that square norm.

Profile L1/L2 does not assert integrability of the additional Gamma-weighted Fourier form. The stronger original-F comparison still needs its originalGammaFormDomain hypothesis. The all-shift domains of the explicit mean-zero construction do not supply that hypothesis for arbitrary H6 sources.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanZeroTrace.actual_h6_gamma_profile_l1_l2`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanZeroTrace.actual_h6_mean_zero_physical_moment_bounds`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiThetaExcess](ActualSuzukiThetaExcess.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiWeightedPhysicalMoments](ActualSuzukiWeightedPhysicalMoments.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailL1Mass](RightExponentialTailL1Mass.md)
