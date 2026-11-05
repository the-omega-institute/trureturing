# Unbounded positive polynomial certificates

## Abstract

All original intermediate-tail seams and slacks

Use the original powers x=2^a, t=2^d=r*x, y=2^b=s*r*x and z=2^c=q*s*r*x, where r=2^(d-a), s=2^(b-d), q=2^(c-b). The original domain gives x>=4, r>=1, s>=2 and q>=2. The four old heads are A=1+x+xy+xyz, B=1+t+xt+xyt, L=1+z+zt+xzt and K=1+y+yz+yzt; the enlarged heads are 2A, SU=2B-1, SV=2L-z-1 and SW=2K-1-y-yz. No gaps are relabelled.

Terminal order is V,W,X,U. Old successor heads are L,K,A,B and new successor heads are SV,SW,A,SU. For every bank the window is 0<=E and 2E<=H-1. Arithmetic.lean contains 14 strict certificates in each of four symbolic branches: six nonfinal seams and eight upper slacks. Each certificate proves that eight times its actual expression is a polynomial with nonnegative coefficients and a positive constant in x-4, q-2 and the applicable r-2 and s-4. Ring proves the identity and positivity uses only these proved offsets. These are universal algebraic scripts, not finite controls.

In I, E2=E0+A-(3s/4)L and F2=F0+2A-(3s/4)SV. For adjacent II and III, E2=A-L-(q/2)B and F2=2A-SV-(q/2)SU. The V split is essential: its single high bit q/2 is paid before nX while the lower bits q/2-1 remain for the last bank. This yields the positive adjacent boundary polynomials uniformly at x=t=4 and q=2.

In III, fresh A is already present in F1: F0=SV-qSU contains no fresh term; F1=F0+A+SW-2SV; F2=F1+(q/2)SU+A-SW. The last A in this increment comes from the original X-terminal identity. There is only one physical fresh occurrence. Using the late timing in this branch would change the actual bank1 window.

These inequalities hold throughout the original cone 2<=a<=d<b<c. They establish the windows for the specified inventory transfer. No literature novelty is claimed; unrestricted four-gap joint lifting and the full Circle/J/C3.1 remain OPEN.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Source](../PacketNormalForm/Source.md)
