# Original gaps and one literal ear

## Abstract

The entire tied-last-two maximum face

**Theorem 1.1 (All independent parameters on the original face).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/LastTwoMaximum/Endpoint.actualSource_last_two_maximum_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/LastTwoMaximum/Endpoint.actualSource_last_two_maximum_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural a,b,s with 2<=a, 2<=b and max(a,b)<=s, put k=a+b+s+s and A=1+2^a+2^(a+b)+2^(a+b+s). The public theorem constructs one permutation sigma of every original Fin(k) label and one j<=k. It proves OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)), both repeated-prefix strips for every natural repetition count m and take length n, and separately both zero totals for every m. Empty repetitions, empty takes and overlong takes are included. The exact public telescope has only a,b,s and their three parameter hypotheses.

The partition is literal. At a=s use EqualOuterThree(s,b); at a=b use FourNegativeAdjacentPairsJointLift(a,s). Otherwise a<s and a differs from b. For b<a use the hybrid-borrow construction. For a<b<=s use the singleton-W-tail construction, except the exact corner b=s=a+1, which uses BalancedGaps(a,b,s,s). The overlap index and exponent equalities are explicit. No seed change, rotation, reflection, parameter cutoff or source-feasibility assumption appears.

Write x=2^a,y=2^b,z=2^s,v=2^(b-2). The original physical U,V,W,X chains have lengths s,s,b,a, starts 0,s,2s,2s+b, and terminals s-1,2s-1,2s+b-1,k-1. After swapping the actual U/V bits below b-2, the remaining hybrid mask t has old mass F(t)=tB-(t mod v)(B-A) and new mass 2F(t)-(t-t mod v). Both bank constructions use the canonical decoded masks and their XOR complements, retaining physical multiplicity. In the borrow sector u is a proved bit-submask of t, not merely a smaller number.

In the borrow sector the new ear is before the final X terminal when s=a+1. Otherwise it is before V when Rp<0, before W when Rp>=0 and Gp<0, and before X otherwise. The W window accounts for an earlier fresh at V. In the singleton sector the ear is before V when Rp<0 and before X otherwise; both possible W windows are proved universally. Native chain masses and the four terminal heads give the positive-bank peaks and post-terminal seams in both rows. withEar_split returns the actual old prefix and the fresh label k; canonical actual_nat_joint_iff converts the same physical word and literal insertion to the two orders.

The old scalar total is zero. The new total over old labels is -A; the actual fresh value A makes the new total zero. Canonical zero_period_transport extends the two complete orders to all finite repeated prefixes and both repeated zero totals. The construction follows the caller's corrected ordinary proofs. The unrestricted whole Circle assertion remains OPEN.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/LastTwoMaximum/Endpoint.actualSource_last_two_maximum_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentPairsJointLift](../Adjacent/FourNegativeAdjacentPairsJointLift.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Endpoint](../BalancedGaps/Endpoint.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/EqualOuterThree/Endpoint](../EqualOuterThree/Endpoint.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/LastTwoMaximum/SourceCertificate](SourceCertificate.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/Endpoint](../SecondPeakMiddleGap/Endpoint.md)
