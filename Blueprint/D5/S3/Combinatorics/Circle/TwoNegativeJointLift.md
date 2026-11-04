# Native common-cut two-negative joint lift

## Abstract

Native common-cut two-negative joint lift

**Theorem 1.1 (Native common-cut two-negative joint lift).**

Lean statement: `D5/S3/Combinatorics/Circle/TwoNegativeJointLift.actualSource_two_negative_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/TwoNegativeJointLift.actualSource_two_negative_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a>b>=2, with k=a+b, q=2^a, r=2^b, N=qr-1 and v=q+1, the actual old source and actual doubled source admit full physical permutations at one shared cut. The selector uses one literal V-ladder support with w=floor((N-v)/(2r+1)); its old mass is (r+1)w and its new mass is (2r+1)w.

The U and V labels, alpha and beta negatives, and the fresh new label are physical occurrences. The old U entries are (q+1)2^i for 0<=i<b-1, alpha at b-1 has value -C+r/2, the old V entries at b+i are (r+1)2^i for 0<=i<a-1, and beta at k-1 has value -C+q/2. In the new source the same physical entries have values 2(q+1)2^i, -N+r, (2r+1)2^i and -N+q/2; the fresh label k has value v. E is the image of one bounded bit mask and F is the complement of E, alpha and beta among all physical labels.

For q=2r, w=r-2 and the words are F,alpha,E,beta and F,alpha,E,k,beta at j=k-1. Their seam heights are respectively 0,alphaMagnitude+1,1,betaMagnitude,0 and 0,N-r,0,(2r+1)w,N-r,0. For q=4r, w=2r-3 and the old selected mass exceeds betaMagnitude by r-2, while the new selected mass plus v equals N-1. For q>=8r the floor remainder gives the two simultaneous mass inequalities. In both latter cases the words are E,beta,F,alpha and E,k,beta,F,alpha at j=length(E). Positive block interiors and the explicit seams give every natural prefix, including empty, full and overlong takes.

This constructor does not assert nonzero phase transport, a numerical-period quotient, or completion of the full Circle C3.1 problem.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/TwoNegativeJointLift.actualSource_two_negative_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/DyadicPrefix](DyadicPrefix.md)
- Dependency: [D5/S3/Combinatorics/Circle/RunFirstEarTransport](RunFirstEarTransport.md)
