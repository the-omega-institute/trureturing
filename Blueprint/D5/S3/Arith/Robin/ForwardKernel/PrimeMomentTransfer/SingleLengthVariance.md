# Single-length cumulative variance

## Abstract

The second-moment part of Corollary 498.5 gives the cumulative variance asymptotic for the complete Chebyshev error.

**Theorem 1.1 (Ms implies 490 2).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthVariance.ms_implies_490_2`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthVariance.ms_implies_490_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume Montgomery–Soundararajan 2004 Theorem 3 (MSThirdTheorem) for k=2 and k=4 under their correlation hypothesis (20), and HL4 for the concrete singular series, which supplies (20) on the band. For 0<alpha<beta<1/4, the function psi-id satisfies (490.2): its cumulative second moment divided by Y v log(Y/v) tends to one uniformly for Y^alpha<=v<=Y^beta. This is the variance assertion of Corollary 498.5. Together with the established results of Sections 497–498 and their stated hypotheses, the two assertions of Corollary 498.5 yield the conclusion of Theorem 494.2 for psi-id whenever alpha<theta<beta.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthVariance.ms_implies_490_2`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthFourth](SingleLengthFourth.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMoments](SingleLengthMoments.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates](SingleLengthRates.md)
