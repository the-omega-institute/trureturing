# QSixteenStructural

## Abstract

Second peak: unbounded q-16 selector

For P>=5, put p=2^P,h=2^H,k=2^(P-1),c=17+((p+3) mod 5),S=(1024p+c)/5,j=(5S) mod 13,v=(S-8j)/13. Divisibility by five and thirteen gives 65v+40j=1024p+c with 17<=c<=21,0<=j<=12,1<=v<=16p. Set m=hj,M=h(49k-1),before=true. The integer remainder becomes R=5v-1+h(128(4c-65)p+65j). Bounds on c,j,v control the first two endpoints and their upper slacks for all h>=1. Substitution p=2k,k=u+16,h=w+1 proves all other physical windows by nonnegative polynomial coefficients.

Because j<=12<k and 49k-1=49*2^(P-1)-1, the existing predecessor-mask theorem supplies literal bit inclusion; shifting by H supplies the scaled mask. The branches p=4,8,16 use respectively (v,m/h,M/h)=(43,33,97),(87,64,195),(173,129,391), always before=true. Each is an affine family for every scale, with all endpoint lower bounds and upper slacks proved as integer inequalities, and each literal base mask shifts by H. These branches preserve the original stock inequalities and distinct physical heads.

Finite consumes this structural theorem in every corresponding parameter branch without retaining a positive witness table. The unchanged original A2 endpoint is the consumer; the entire Circle objective and official delivery remain open.

**Theorem 1.1 (q_sixteen_dyadic_good).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QSixteenStructural.q_sixteen_dyadic_good`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QSixteenStructural.q_sixteen_dyadic_good` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural P,H with 2<=P there exist natural v,m,M and before:Bool such that Good (2^P) 16 (2^H) v m M before. Good includes 1<=v, 2v<=4pq, m<M, 2M<8hpq, literal Submask m M, and every original old/new physical window.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QSixteenStructural.q_sixteen_dyadic_good`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QTwoStructural](QTwoStructural.md)
