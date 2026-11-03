# Every natural 2<=a<c<b with c=d

## Abstract

Second peak, equal-tail: complete dyadic-mask joint lift

**Theorem 1.1 (One original permutation and one literal fresh insertion).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/Endpoint.actualSource_second_peak_equal_tail_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/Endpoint.actualSource_second_peak_equal_tail_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural a,b,c with 2<=a<c<b and the original equal tail c=d, put k=a+b+c+c and A=1+2^a+2^(a+b)+2^(a+b+c). The theorem supplies a permutation sigma of every original Fin k label and a cut j<=k. Both OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)) hold with the unchanged actualSource family.

The selector is unbounded in r=c-a and t=b-c-1. It chooses alpha,m0,v,j0 and an early Boolean branch from six polynomially certified windows. The physical masks use T_s(m)=s(m+1)-1, preserve sparse submask containment and partition every W bank, including the sole small tuple (a,c,b)=(2,3,4).

Both original orders retain every physical occurrence exactly once. The fresh label is inserted literally in either of the two selector modes; no source relabeling, rotation or finite feasibility assumption is used. The endpoint also records every natural repeated prefix and take, including zero repetitions and overlong prefixes, together with separate zero totals for the old and fresh words.

The proof reuses PacketNormalForm source values, terminal masses and zero-period transport. The old bound is modulus(k)/2 and the new bound is modulus(k); the identity modulus(k+1)/2=modulus(k) transfers the new repeated-prefix result. This is the complete second-peak equal-tail face and leaves the unchanged wholeCircle J/C3.1 objective open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/Endpoint.actualSource_second_peak_equal_tail_joint_lift`
