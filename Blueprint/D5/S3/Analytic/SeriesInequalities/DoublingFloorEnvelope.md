# Doubling Floor Envelope

## Abstract

Fixed doubling floors have matching near-critical numerical profiles and an exact series criterion.

**Theorem 1.1 (A two-sided bound for the complete numerical supremum).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/DoublingFloorEnvelope.raw_profile_two_sided`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/DoublingFloorEnvelope.raw_profile_two_sided` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0, 0<c<=1, N>=1 and b>1, define P(eta,u) as the supremum over all natural k of ENNReal.ofReal((N b^k)^(-u) eta(k)^(-a+u)). Let g>=1 be a finite real-valued nondecreasing function on [2,infinity) with g(2t)<=D g(t), D>=1, and put omega(k)=1/((k+2) g(k+2)^(1/a)).

There are positive constants c1 and C1 such that, for every 0<u<=1/2, ENNReal.ofReal(c1 u^(-a) g(1/u))<=P(c omega,u)<=ENNReal.ofReal(C1 u^(-a) g(1/u)). The constants precede u and every layer k. Summability of omega is not required.

Set T=1/u. Monotonicity controls layers with k+2<=T, and cross-scale doubling plus exponential damping controls all remaining layers. The moving layer k=floor(T) gives the lower bound. The power envelope for g controls the retained correction (c omega(k))^u; the proof does not replace it by a constant without an estimate.

**Theorem 1.2 (One prescribed-ratio floor matches throughout an interval).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/DoublingFloorEnvelope.prescribed_ratio_matching_profile`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/DoublingFloorEnvelope.prescribed_ratio_matching_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the same growth and grid hypotheses, and prescribe R>1 and K>0. If omega is summable, there exists one eta with positive entries at most one, nonincreasing and summable, total mass at most K and eta(k)<=R eta(k+1). There are positive c1, C1 and epsilon such that its complete profile lies between the corresponding multiples of u^(-a) g(1/u) for every 0<u<=epsilon.

The rational smoothing construction gives one eta uniformly comparable to a scaled omega. Raising both sides to -a+u transfers the raw profile comparison on 0<u<=min(1/2,a). Eta and all comparison constants are fixed before u varies.

**Theorem 1.3 (The profile bound forces summability of the original floor).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/DoublingFloorEnvelope.summable_floor_of_profile_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/DoublingFloorEnvelope.summable_floor_of_profile_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let eta be any positive summable real sequence; eta need not itself double or be nonincreasing. Under the same growth and grid hypotheses, suppose positive C and epsilon bound P(eta,u)<=ENNReal.ofReal(C u^(-a) g(1/u)) for every 0<u<=epsilon. Then omega is summable.

Evaluate the bound at u=1/(k+2). Retain the exponent a-1/(k+2) when solving for eta(k). The doubling power envelope bounds the logarithmic correction and yields one positive c and a natural L such that c omega(k)<=eta(k) for every k>=L. Summability then follows by tail comparison; the two-term shift introduces no additional assumption.

**Theorem 1.4 (The fixed numerical growth criterion and matching construction).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/DoublingFloorEnvelope.fixed_floor_growth_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/DoublingFloorEnvelope.fixed_floor_growth_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define AdmissibleFloor(R,K,eta) by positive entries at most one, nonincreasing order, summability, total mass at most K and the adjacent ratio eta(k)<=R eta(k+1). Define the integral-test sequence to be zero at k=0,1 and 1/(k g(k)^(1/a)) at every k>=2.

For every a>0, N>=1, b>1, R>1 and K>0, and every finite nondecreasing g>=1 on [2,infinity) satisfying a doubling bound with D>=1, the integral-test sequence is summable if and only if some admissible eta has the uniform numerical profile upper bound for all sufficiently small positive u. When the series is summable, one admissible eta has matching positive lower and upper constants on the same interval.

The identity between the integral-test sequence shifted by two and omega connects the two summability conditions. The forward implication uses the fixed matching construction; the reverse implication uses eventual domination with the moving exponent retained.

The result is a numerical supremum criterion. No actual sampling strategy, task-moment comparison, beta restriction, noninteger sampling construction or common reference-expenditure bridge is supplied. Those relations require separate mathematical hypotheses and proofs.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/DoublingFloorEnvelope.fixed_floor_growth_criterion`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/DoublingFloorEnvelope.prescribed_ratio_matching_profile`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/DoublingFloorEnvelope.raw_profile_two_sided`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/DoublingFloorEnvelope.summable_floor_of_profile_bound`
- Dependency: [D5/S3/Analytic/SeriesInequalities/PrescribedRatioFloorSmoothing](PrescribedRatioFloorSmoothing.md)
