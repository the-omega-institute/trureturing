# Corollary 498.5: the fourth moment

## Abstract

The single-length Montgomery–Soundararajan formula transfers to the cumulative fourth moment of psi minus the identity.

**Theorem 1.1 (A uniform discrete fourth-moment bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthFourth.discrete_fourth_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthFourth.discrete_fourth_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the Montgomery–Soundararajan Theorem 3 formula and the strong Hardy–Littlewood hypothesis for the concrete singular series. For positive alpha less than beta less than one quarter, there is A at least one such that the discrete fourth moment at the natural floors of Y and v is at most A Y v squared log squared Y, uniformly for Y^alpha at most v at most Y^beta and sufficiently large Y. The restricted correlation hypothesis follows from Hardy–Littlewood with shift multiplier two. The explicit moment error and the cutoff and length replacement errors vanish uniformly; the remaining logarithmic main integral is bounded directly.

**Theorem 1.2 (Ms implies 497 6).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthFourth.ms_implies_497_6`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthFourth.ms_implies_497_6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume Montgomery–Soundararajan 2004 Theorem 3 (MSThirdTheorem) for k=2 and k=4 under their correlation hypothesis (20), and HL4 for the concrete singular series, which supplies (20) on the band. For 0<alpha<beta<1/4, the function psi-id satisfies (497.6): its cumulative fourth moment has main term 3 v^2 times the integral of (log(y/v)+B)^2 from one to Y, with error little-o of Y v^2 log(Y/v)^2 uniformly for Y^alpha<=v<=Y^beta. Here B=1-gamma-log(2 pi). This is the fourth-moment assertion of Corollary 498.5. Together with the established results of Sections 497–498 and their stated hypotheses, the two assertions of Corollary 498.5 yield the conclusion of Theorem 494.2 for psi-id whenever alpha<theta<beta.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthFourth.discrete_fourth_upper`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthFourth.ms_implies_497_6`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMoments](SingleLengthMoments.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates](SingleLengthRates.md)
