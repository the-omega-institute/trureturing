# Every natural 2<=a<d<c<b with c<=a+d

## Abstract

Second peak, moderate third gap: complete physical joint lift

**Theorem 1.1 (One original permutation and one literal fresh insertion).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakModerateThirdGap/Endpoint.actualSource_second_peak_moderate_third_gap_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakModerateThirdGap/Endpoint.actualSource_second_peak_moderate_third_gap_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put x=2^a, R=2^(d-a-1), r=2^(c-d), lambda=2^(b-c-1), t=2xR, z=rt and y=2lambda z. The endpoint keeps the physical terminal order W-, X-, U-, V- and transfers one of the native U masks 0, 1 or 2 into the third bank.

For C=2lambda L and E=N+A-B-K, the selector uses Hminus=floor((E+2uA)/C)+1 and Hplus=floor((E+2uA+A-1)/C). In the r>=4 branch u=0 is paid by A-(r-1)C>1. Ratio estimates are confined to r=2; A<2C is false on the full domain. In the r=2 branch the source is the three-residue integer lemma: 8/5<A/C<2 gives three choices, while A/C>5/3 gives the two-choice R=2 branch; the exact R=1 and R=2,x=4 families are discharged by their displayed polynomial inequalities.

The selected H is early when F(Hminus)<=0 and late otherwise, with F(H)=CH-E-2uA-(1+lambda(z+H)(z+1)). Both seams use the same unchanged A. The native masks are U[full-u], W[lambda H], W[lambda(z-1-H)] ++ X[full] ++ U[u], and V[full] ++ W[lambda-1]; all physical labels occur exactly once, including lambda=1 and the actual U1 transfer.

The fresh label starts the second bank in the early case and the third bank in the late case, giving a literal insertion immediately after W- or X-. The Lean source consumes PacketNormalForm actual values, native terminal masses, the actual_nat_joint_iff bridge, and zero_period_transport. It states all natural replicate/flatten/take bounds for the old modulus(k)/2 and enlarged modulus(k), and proves the old and enlarged repeated totals separately. The unrestricted Circle J and C3.1 remain open; the theorem addresses exactly the stated full moderate-third-gap sector. The construction formalizes the caller-supplied source without asserting literature novelty or official acceptance.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakModerateThirdGap/Endpoint.actualSource_second_peak_moderate_third_gap_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/Endpoint](../SecondPeakMiddleGap/Endpoint.md)
