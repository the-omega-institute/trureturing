# Small-window remainder bounds

## Abstract

The complete actual-K small-window remainder.

**Theorem 1.1 (The actual small-window continuum payment).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelSmallWindowBounds.small_V_abs_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelSmallWindowBounds.small_V_abs_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the inclusive window 0<=D<=log 3, the retained exact finite-prime cases, scalar estimates and continuum integral bound control the actual V remainder. The proof includes the endpoints log 2 and log 3. These bounds are consumed by the complete-K q6 and q22 certificate and retain their original proof terms. They assert neither global positivity nor RH.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelSmallWindowBounds.small_V_abs_bound`
- Dependency: [D5/S3/Arith/GoldenResource/RobinRationalBasis](../../../Arith/GoldenResource/RobinRationalBasis.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentPayments](ActualKernelMomentPayments.md)
