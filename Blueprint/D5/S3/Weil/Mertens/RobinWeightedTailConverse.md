# Robin Weighted Tail Converse

## Abstract

Negative excursions of the exact Robin weighted tail and the converse to its lower bound.

**Theorem 1.1 (Negative excursions forced by a right half-strip zero).**

Lean statement: `D5/S3/Weil/Mertens/RobinWeightedTailConverse.normalized_weighted_tail_negative_peaks`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/RobinWeightedTailConverse.normalized_weighted_tail_negative_peaks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be a zero of Riemann zeta with 1/2 < beta = Re(rho) < 1. Its analytic multiplicity m is positive. Write D(x) = sqrt(x) log(x) and Jpsi(x) = weightedTail(psiErrorKernel, x) for the exact weighted tail. For every 0 <= c < m/(norm(rho) norm(rho-1)) and every real T, some u > max(T, log(2)) satisfies c < -exp((1/2-beta)u) D(exp(u)) Jpsi(exp(u)).

CriticalThetaTailPeak supplies arbitrarily late positive peaks of the actual signed theta tail at the full coefficient from the pole at rho-1. The tail substitution gives f(u) = S(exp(u)) - Jpsi(exp(u)), where S is the activation-weighted integral of psi-theta. The prime-power comparison with sqrt(t) and the bound A(x) <= 2/D(x) give a uniform upper bound on D(x) S(x) for x >= 2. At beta > 1/2 the scaled upper bound tends to zero. Taking a theta peak at an intermediate coefficient leaves enough room for this error.

**Theorem 1.2 (An eventual constant lower bound implies the Riemann hypothesis).**

Lean statement: `D5/S3/Weil/Mertens/RobinWeightedTailConverse.rh_of_eventually_normalized_weighted_tail_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/RobinWeightedTailConverse.rh_of_eventually_normalized_weighted_tail_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose there is a real C with -C <= D(x) weightedTail(psiErrorKernel, x) for all sufficiently large real x. A zero in the open right half-strip would force a negative excursion at half its positive coefficient, while the eventual bound at x = exp(u) bounds the negative excursion above by C exp((1/2-beta)u), which tends to zero. RightHalfStripRiemannReduction then gives the Riemann hypothesis from exclusion of these zeros.

## References

- Truth anchor: `D5/S3/Weil/Mertens/RobinWeightedTailConverse.normalized_weighted_tail_negative_peaks`
- Truth anchor: `D5/S3/Weil/Mertens/RobinWeightedTailConverse.rh_of_eventually_normalized_weighted_tail_lower`
- Dependency: [D5/S3/Arith/Robin/Analytic/RHSharpArithmeticEnvelope](../../Arith/Robin/Analytic/RHSharpArithmeticEnvelope.md)
- Dependency: [D5/S3/Weil/Mertens/CriticalThetaTailPeak](CriticalThetaTailPeak.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../ZetaBridge/RightHalfStripRiemannReduction.md)
