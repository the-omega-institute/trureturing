# The Normalized Xi Resolvent

## Abstract

The centered logarithmic derivative of the classical xi function is an absolutely convergent zero resolvent.

**Theorem 1.1 (The actual multiplicity-weighted zero sum).**

Lean statement: `D5/S3/Zeros/Resolvent/XiNormalizedResolvent.xi_reading_normalized_resolvent_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Resolvent/XiNormalizedResolvent.xi_reading_normalized_resolvent_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every exhaustive, injective enumeration Z of the nontrivial classical zeta zeros with their actual multiplicities, and every complex s at which xi is nonzero, the combined terms m times (1/(s-rho) + 1/rho) have sum xi'(s)/xi(s) minus xi'(0)/xi(0). The xi normalization has value one half at zero and one.

Scale xi to have value one at the origin. The finite divisor factorization uses the physical cutoff norm(rho) at most (22/25)R, transporting analytic multiplicities. On the strict disk of radius 83/100, Schwarz bounds the centered regular logarithmic derivative. The chain rule and centering produce two inverse-radius factors. The global log-linear xi estimate and the inequality 1 + log(r) at most 3 times r^(1/2) give the required three-halves bound locally. With B_R = 2 exp(C(1+R)^(3/2)), the physical remainder is bounded by (2 times 44795000 divided by (83/100)) times log(B_R) times norm(s) divided by R squared.

For norm(s) at most M and norm(rho) at least max(1,2M), the rational summand norm is bounded by 8M times the multiplicity divided by 1 + normSq((rho-1/2)/i). The actual inverse-square zero sum is summable. Physical cutoff exhaustion and the vanishing remainder identify the HasSum value. The identity includes both endpoints and assumes no Riemann hypothesis.

A complete application identifies the normalized square source F(z) = xi(1/2 + i sqrt(z))/xi(1/2) with its infinite genus-zero product on the whole complex plane. The center is nonzero by XiThetaTransform.source_theta_normalized. EntireEvenSquareDescent.entire_even_square_descent applies to the even function w maps to xi(1/2 + i w), so the displayed square-root formula defines an entire F and F(0) = 1. The parameter gamma satisfies rho = 1/2 + i gamma for every actual nontrivial zero; it can be complex, and no critical-line premise is used.

For each index with positive real part of gamma, use the factor 1 - z/gamma squared once for every element of Fin(m), where m is that zero's exact analytic multiplicity. Negative-height indices contribute the identity factor. Actual nonrealness of rho excludes zero height, and functional-equation reflection pairs positive and negative heights with equal gamma squared and equal multiplicity. The complete sum of m/norm(gamma) squared is summable: the protected weighted inverse-square sum controls all but the locally finite low-height set. The resulting product converges locally uniformly on every compact subset, retains the entire infinite zero family, is entire, and has value one at zero.

The square-source analytic order at gamma squared is exactly m for every actual source index, including off-line and repeated zeros. AlternatingZetaContinuation excludes real nontrivial zeta zeros, so gamma is nonzero. Squaring has derivative 2 gamma there, and the affine map w maps to 1/2 + i w has derivative i. Mathlib.analyticOrderAt_comp_of_deriv_ne_zero therefore transports the order through both maps. ScalarUnitDressing removes the nonzero center normalization and the nonvanishing completed-zeta scalar at the original zero. The existing completed-zeta order theorem then gives the exact actual multiplicity m; the two reflected representatives of a square each have that same order, rather than an added order 2m.

Evaluate the normalized xi resolvent at s plus = 1/2 + i w and s minus = 1/2 - i w. Subtracting these two HasSum identities cancels the centered constant. Reflection and the square-source chain rule give the complete all-index sum m/(w squared - gamma squared) equal to twice F'(w squared)/F(w squared). Transporting the positive-height indicator sum by the reflection permutation removes the duplicate factor two. Finite multiplicity fibers then identify the product's logarithmic derivative through Mathlib.logDeriv_tprod_eq_tsum.

Continuity provides a common nonzero neighborhood of the center for F and the product. The logarithmic derivatives agree there away from zero; continuity of their analytic derivatives also includes zero. Mathlib.logDeriv_eqOn_iff gives a constant ratio, the center values make that constant one, and the analytic identity principle extends the equality to all complex z. This is an application of the existing resolvent and analytic suppliers, with no new theorem declaration. The identification alone supplies neither the exterior coefficient-circle remainder, the joint extraction of a nonempty selected factor, node-sign control, nor a proof of the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Zeros/Resolvent/XiNormalizedResolvent.xi_reading_normalized_resolvent_hasSum`
- Dependency: [D5/S3/Analytic/Dilation/ScalarUnitDressing](../../Analytic/Dilation/ScalarUnitDressing.md)
- Dependency: [D5/S3/Analytic/Resolvent/XiGlobalGrowth](../../Analytic/Resolvent/XiGlobalGrowth.md)
- Dependency: [D5/S3/Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup](../../Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup.md)
- Dependency: [D5/S3/Zeros/Endpoints/XiEndpointValues](../Endpoints/XiEndpointValues.md)
