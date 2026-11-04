# Minus-one physical joint transport with a periodic daughter

## Abstract

Minus-one physical joint transport with a periodic daughter

**Theorem 1.1 (Minus-one physical joint transport with a periodic daughter).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Construction.periodic_daughter_joint_shortening`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Construction.periodic_daughter_joint_shortening` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d>=2, 1<=w<=2^(d-1)-1, r>=2 and cut<=d, assume the full actual OriginalOrder of tau at (d,w) and of its literal ear eta at (d+1,2w). Put D=d+1, K=D*r-1, U=w*geom(D,r). The explicit OLD word consists of ascending copies of eta at physical blocks j<r-1 followed by the top copy of tau. Its common cut is (r-1)*D+cut, at most K. The conclusions are both full actual OriginalOrder predicates, at (K,U) and (K+1,2U), with the latter word exactly the literal global ear of the former.

Write q=2^D, n=2^d-1, H_j=geom(D,j), H=H_(r-1), R=q^(r-1), G=geom(D,r), N=2^K-1. Then G=H+R=1+qH and (q-1)G=2N+1. The native old digit charge e_i satisfies alpha_i=2^i*w-n*e_i and beta_i=2*alpha_i-e_i. Extend the distinct local ear phase by alpha_d=e_d=beta_d=w. Its total charge is 2w. The nonnegative defect B_j(i)=2^(i+1)*w*H_j+e_i has total 2w*q^j.

For a regular OLD label jD+i the integer V_j(i)=2^d*H*beta_i+alpha_i+2^i*w*H_j satisfies 2V_j=G*beta_i+B_j. The exact uncentered difference is N*B_j=N*(H_j*beta_i+q^j*e_i). The inequality 4w<=q-4 and H_j+q^j<=H give G*n+2wH<=N-1. Thus both centered bounds and every regular block prefix hold at the actual OLD modulus; its total is w*q^j and its incoming height is w*H_j. This uses an integer formula throughout, with no parity or integer division assumption.

For a top OLD label (r-1)D+i the actual centered value is T_i=R*alpha_i+H*beta_i. Its exact uncentered difference is N*(2^(i+1)*w*H+e_i). Centered uniqueness follows from N=R*n+(q-1)H. A top prefix has incoming height wH, an alpha prefix a in [0,(n-1)/2], and a beta prefix b in [-w,n]. The latter follows from the actual eta prefix at h or h+1 and beta_d=w. Therefore wH+R*a+H*b is nonnegative and its doubled upper bound is R(n-1)+2H(n+w)<=N-1. The top total is -wH; the complete OLD total is zero.

At every enlarged physical label jD+i the exact actual source is G*beta_i at modulus 2^(Dr)-1=(q-1)G. Each complete eta block is a scaled zero loop. Every natural prefix lies in [0,G*n], and G*n is at most the enlarged half modulus. The literal ear identity produces r complete ascending eta blocks. Product inventory proves each enlarged physical label occurs once; deleting only the global fresh label proves the OLD permutation. The recursive strip and take lemmas include empty, complete and overlong prefixes and both endpoint cuts.

The theory connects cyclic doubling orbits and arithmetic across adjacent moduli: repetition scales the daughter orbit, while nonnegative native charges control the shortened parent. No cyclic gap invariance or cross-modulus equivariance is assumed. Numerical equality never identifies distinct physical labels. This theorem is a new MINUS-one construction, not an application of PLUS-one shortening or forward OLD repetition.

## Unbounded four-gap application

Let a>=2, b>a and b>=3. Set d=a+b-1, w=2^a+1, r=2. The two base gaps are a and b-1, both at least two; the library two-negative nondecreasing/strict joint-lift theorems supply a common-cut witness according as a<=b-1 or b-1<a. Since b-1>=2, d-1>=a+1 and 2^a+1<=2^(d-1)-1. Then K=2(a+b)-1 and U=(2^a+1)(1+2^(a+b))=1+2^a+2^(a+b)+2^(2a+b), the four gaps (a,b,a,b-1). This is an entire unbounded application, including (s,s+1,s,s); it is explanatory algebra under the generic endpoint, with no additional specialization theorem or registration.

Full arbitrary b-maximum J and CircleJ/C3.1 remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Construction.periodic_daughter_joint_shortening`
