# The left vertical integral

## Abstract

An oscillatory estimate on the left edge of the finite Landau rectangle.

**Theorem 1.1 (Uniform bound on the left edge).**

Lean statement: `D5/S3/Weil/ZetaExplicit/LandauLeftVertical.norm_left_vertical_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaExplicit/LandauLeftVertical.norm_left_vertical_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real x>1 and V>=1, integrate x^(-1/4+it) times the negative logarithmic derivative of the Riemann zeta function over 1<=t<=V. The norm is at most x^(-1/4)*(80*(V-1)+20*(1+log(V))/log(x)).

The zeta functional equation reflects the zeta term to real part 5/4. The digamma recurrence and Binet bound isolate log(3/4+it). The reflected term, tangent and remaining digamma terms have bounded norm, so their integral costs at most 80*(V-1) before scaling.

For the logarithm term, integrate by parts against exp(it*log(x)). The phase primitive has norm 1/log(x) and the logarithm derivative has norm at most 1/t. The endpoints and the integrated derivative give 20*(1+log(V))/log(x).

The estimate is unconditional and the second term exhibits the loss as x decreases to 1. The sum over zeros also requires a rectangle residue identity, control of the horizontal edges and a transfer to arbitrary cutoff heights.

## References

- Truth anchor: `D5/S3/Weil/ZetaExplicit/LandauLeftVertical.norm_left_vertical_integral`
- Dependency: [D5/S3/Weil/Mertens/Cryptids/DigammaBinet](../Mertens/Cryptids/DigammaBinet.md)
