# The Normalized Xi Resolvent

## Abstract

The centered logarithmic derivative of the classical xi function is an absolutely convergent zero resolvent.

**Theorem 1.1 (The actual multiplicity-weighted zero sum).**

Lean statement: `D5/S3/Zeros/Resolvent/XiNormalizedResolvent.xi_reading_normalized_resolvent_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Resolvent/XiNormalizedResolvent.xi_reading_normalized_resolvent_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every exhaustive, injective enumeration Z of the nontrivial classical zeta zeros with their actual multiplicities, and every complex s at which xi is nonzero, the combined terms m times (1/(s-rho) + 1/rho) have sum xi'(s)/xi(s) minus xi'(0)/xi(0). The xi normalization has value one half at zero and one.

Scale xi to have value one at the origin. The finite divisor factorization uses the physical cutoff norm(rho) at most (22/25)R, transporting analytic multiplicities. On the strict disk of radius 83/100, Schwarz bounds the centered regular logarithmic derivative. The chain rule and centering produce two inverse-radius factors. With B_R = 2 exp(C(1+R)^(3/2)), the physical remainder is bounded by (2 times 44795000 divided by (83/100)) times log(B_R) times norm(s) divided by R squared.

For norm(s) at most M and norm(rho) at least max(1,2M), the rational summand norm is bounded by 8M times the multiplicity divided by 1 + normSq((rho-1/2)/i). The actual inverse-square zero sum is summable. Physical cutoff exhaustion and the vanishing remainder identify the HasSum value. The identity includes both endpoints and assumes no Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Zeros/Resolvent/XiNormalizedResolvent.xi_reading_normalized_resolvent_hasSum`
- Dependency: [D5/S3/Analytic/Dilation/ScalarUnitDressing](../../Analytic/Dilation/ScalarUnitDressing.md)
- Dependency: [D5/S3/Analytic/Resolvent/XiGlobalGrowth](../../Analytic/Resolvent/XiGlobalGrowth.md)
- Dependency: [D5/S3/Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup](../../Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup.md)
- Dependency: [D5/S3/Zeros/Endpoints/XiEndpointValues](../Endpoints/XiEndpointValues.md)
