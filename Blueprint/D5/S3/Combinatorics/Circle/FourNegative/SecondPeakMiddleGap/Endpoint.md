# Every independent natural 2<=d<c<a<=b

## Abstract

Second peak, middle gap: complete two-route physical joint lift

**Theorem 1.1 (One old permutation and its single literal fresh insertion).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/Endpoint.actualSource_second_peak_middle_gap_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/Endpoint.actualSource_second_peak_middle_gap_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural quadruple 2<=d<c<a<=b, let k=a+b+c+d and A=1+2^a+2^(a+b)+2^(a+b+c). The theorem supplies one permutation sigma of all actual Fin k labels and a natural cut j<=k. Both OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)) hold. The same witnesses satisfy the old and new strip bounds for every natural prefix n of every finite number m of repetitions, including m=0, n=0 and prefixes beyond the finite repeated word. Both repeated words have total zero for every finite m. The original actualSource family is unchanged. The unrestricted Circle J and C3.1 remain open.

Write x=2^a, y=2^b, z=2^c, w=2^d, N=xyzw-1, Q=2N+1. The old heads are A=1+x+xy+xyz, B=1+w+wx+wxy, L=1+z+wz+wxz and K=1+y+yz+wyz; let H=1+y+yz. The new heads are 2A, SU=2B-1, SV=2L-1-z and SW=2K-H. Existing PacketNormalForm source and native terminal results identify both centered rows and all terminal increments on actual labels. Their totals are zero and -A on old labels; the single fresh label k contributes (0,A).

The terminal order is W,X,U,V. For depth j the physical labels are U_j=d-j-1, V_j=d+c-j-1, W_j=d+c+b-j-1 and X_j=k-j-1. The first packet uses W depths 1 through a-1. The last packet uses every V positive, W depths a through b-1 and X depths c+1 through a-1. Every U positive belongs to the U packet. Define q=2^(b-a), v=2^(a-c-1), h=2^(c-d-1) and s=hv=2^(a-d-2). Then z=2wh, x=4whv and y=qx. These exact dyadic relations include q=1, v=1 and h=1, so all equal-boundary empty ranges are retained.

Put alpha=4sH-(1+x+xy), gamma=2sH-(1+x+xy), D=K-qL and Dprime=SW-qSV. If gamma<=Dprime, the X packet receives X depths 1 through d, the U packet receives X depths d+1 through c, and fresh is inserted immediately before the U terminal. Otherwise the X packet receives depths 1 through d-1 and depth d+1, while U receives depth d and depths d+2 through c; fresh is immediately before the X terminal. The physical transposition of X_d and X_(d+1), together with moving fresh between X and U, is an involution on these two allocations. It preserves the full inventory and the endpoint after U. With t=2s its change at X is (-tK/2,A-tSW/2). This mechanism is consumed directly in the branch-selected certificate.

The first endpoint is (D,Dprime). Let r=2s on the first route and r=3s on the second, and let ear=0 on the first route and ear=A on the second. The X endpoint is (D+A-rK,Dprime+A+ear-rSW). Both routes then reach (E,F)=(B+D-vK,SU+Dprime-vSW) after U, and (0,0) after V. Exact physical dyadic interval sums prove the packet masses: W has coefficient y/2-q; X has coefficient x/2-r; U contains its whole coefficient w/2-1 plus X coefficient r-v; V contains its whole coefficient z/2-1 plus W coefficient q-1 and X coefficient v-1. Equal-valued occurrences remain distinct physical indices.

The arithmetic proof establishes 0<=Dprime<=D<=H; 2H<=K-1, SW-1 and A-1; gamma>=1; alpha>=2H+1; 4alpha<=A-1; and 8gamma<=A-1. The identities 4sK=A+alpha and 2sSW=A+gamma prove the two X windows under the explicit gamma comparison. Both U windows follow from exact nonnegative slack polynomials for E, F, B-1-2E and SU-1-2F. The dyadic substitutions express these margins as polynomials with nonnegative coefficients in w-4,h-1,v-1,q-1; Lean checks each polynomial identity and positivity over the complete unbounded cone.

Complete interval inventory and native paired masses construct an unconditional PacketNormalForm.Certificate, including all old and new finite checks. No certificate-existence or stock-feasibility hypothesis is added. The existing actual_four_packet_iff supplies the same old physical permutation and its literal ear word in both OriginalOrder clauses. SourceWidth strip concatenation at zero transports each complete order to all finite repeated prefixes and totals. This is a repository formalization of the caller-supplied ordinary construction, without a claim of literature novelty or official acceptance.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/Endpoint.actualSource_second_peak_middle_gap_joint_lift`
