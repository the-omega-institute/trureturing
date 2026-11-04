# QTwoStructural

## Abstract

Second peak: unbounded q-two selector

For arbitrary integers p>=8 and h>=1, put j=(32p+6) mod 9, v=(16p+3-5j)/9, m=hj and M=h(2p-1). The residue equation 9v+5j=16p+3 implies 1<=v<=2p. Substitution into the actual old and new physical endpoints proves all four windows, including the distinct third heads and the zero seam, with every stock bound. No window or feasibility certificate is assumed.

For p=2^P with P>=3 and h=2^H with unrestricted natural H, j lies below the full mask 2^(P+1)-1. Multiplication by 2^H shifts both masks without carries, preserving bit inclusion. The strict inequality m<M makes this inclusion proper. Natural and integer casts transport the arithmetic windows to Good. At p=4, the late fresh cut admits the uniform affine choice v=5, m=5h, M=8h-1 for every integer h>=1. The first old and new endpoints are 2010h+48 and 474h+88, with positive upper slacks 294h-44 and 1830h-84. The remaining charged endpoints and their slacks are affine and nonnegative at h=1 with nonnegative slopes. For h=2^H, M=2^(H+3)-1 is a full mask and m<2^(H+3), so the existing predecessor-mask theorem gives literal bit inclusion. This same construction covers H=0 and H=1 without exceptional witness rows. Finite uses these two unbounded constructions for all eight q=2 cases. The q>=4 cases remain outside these selectors.

**Theorem 1.1 (q_two_dyadic_good).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QTwoStructural.q_two_dyadic_good`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QTwoStructural.q_two_dyadic_good` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural P,H, if 3<=P, there exist natural v,m,M such that Good (2^P) 2 (2^H) v m M true. Here Good includes 1<=v, 2v<=8p, m<M, 2M<16hp, Submask m M and every exact old/new window.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QTwoStructural.q_two_dyadic_good`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Algebra](Algebra.md)
