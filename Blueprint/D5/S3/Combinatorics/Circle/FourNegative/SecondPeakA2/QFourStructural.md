# QFourStructural

## Abstract

Second peak: unbounded q-four selector

For p=2^P, P>=4, and arbitrary h=2^H, put j=(3p+9) mod 17, v=(64p+5-10j)/17, m=hj, M=h(5p-1), before=true. The exact residue equation 17v+10j=64p+5 makes v integral and gives 1<=v<=4p. The first old and new endpoints reduce to 10v-2+h(192p+34j) and 20v-2+h(1472p+34j). Their upper slacks have nonnegative coefficients after using 0<=j<=16 and h>=1. For the remaining physical rows, substitution p=u+16 and h=w+1 leaves polynomials with nonnegative coefficients in u,w. This checks the actual distinct K and SW heads, as well as the separate zero seam.

At p=16 the same residue formula gives j=6; above 16, j<=16<p. The existing predecessor-mask theorem therefore proves Submask j (5p-1). Multiplication by 2^H shifts bit positions and preserves this inclusion; arbitrary multiplication is not used. Strict m<M and 2M<32hp supply the physical stock bounds. At p=4 the uniform affine choice is v=6,m=16h,M=20h,before=true. At p=8 it is v=29,m=3h,M=39h,before=false. Both work for every h>=1, including h=1,2, with the same formulas. The p=8 fresh endpoint retains its actual subtraction of 2A. The literal masks 16<=bits20 and 3<=bits39 shift dyadically. The three branches cover every P>=2 and natural H; natural/integer casts transport each window without changing the source predicate.

Finite consumes this theorem for all eight q=4 cases while preserving finite_exists and the original near-b endpoint. The q-eight, q-sixteen and q-thirtytwo unbounded selectors supply the other branches; Finite retains no positive witness table. This selector supplies a structural q=4 sector and does not settle the full Circle objective.

**Theorem 1.1 (q_four_dyadic_good).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QFourStructural.q_four_dyadic_good`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QFourStructural.q_four_dyadic_good` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural P,H with 2<=P there exist natural v,m,M and before:Bool such that Good (2^P) 4 (2^H) v m M before. Good includes 1<=v, 2v<=16p, m<M, 2M<32hp, literal Submask m M, and all actual old/new physical windows.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QFourStructural.q_four_dyadic_good`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QTwoStructural](QTwoStructural.md)
