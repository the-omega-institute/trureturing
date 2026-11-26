# Explicit bounds for the weighted Chebyshev tail

## Abstract

Explicit bounds for the weighted Chebyshev tail.

The unconditional integrated explicit formula splits the weighted Chebyshev error into the actual zero response and a residual from the trivial zeros and the constant term.

**Theorem 1.1 (Two-sided logarithmic bounds).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound.J_log_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound.J_log_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For j in [1,10] and u at least log 2, assuming every actual occurrence lies on the critical line, the upper bound is the first Li mass times exp((1/2 − j)u) H(j,u). The lower bound is its negative minus log(2π) exp(−ju)/u.

**Theorem 1.2 (First Li mass constant).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound.firstLiMass_lt_twentieth`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound.firstLiMass_lt_twentieth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact bounds on Euler’s constant and the logarithms give a first Li mass strictly below 1/20.

**Theorem 1.3 (Scaled weighted tail lower bound).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound.actual_weighted_tail_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound.actual_weighted_tail_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x at least 2 on the same occurrence-line premise, the weighted Chebyshev tail scaled by √x log x is at least −((1/20)(1 + 1/log x) + 2/√x).

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound.J_log_bounds`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound.actual_weighted_tail_lower`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound.firstLiMass_lt_twentieth`
- Dependency: [D5/S3/Arith/GoldenResource/RobinRationalBasis](../../../Arith/GoldenResource/RobinRationalBasis.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedTail](RobinActualWeightedTail.md)
