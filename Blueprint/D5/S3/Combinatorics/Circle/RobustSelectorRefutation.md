# A Robust Selector Obstruction on the Physical Circle

## Abstract

An original modular source obstructs the universal robust lower-half residue selector.

The cyclic action on physical labels determines the signed source, its LARGE parents and the SMALL rows between them. For one such source, the depleted row mask has only one robust subset, and that subset misses the required lower half of the endpoint residue interval. This refutes the intermediate universal selector; original word existence remains open.

## The complete source family

Let m,k,t,L be natural numbers, a,b integers, and p,d,x physical labels in Fin(k). Put N=2^k-1, Q=2^(k-2), C=(N-1)/2 and s(i)=((2^i*t+C) mod N)-C. Advance is iteration of finRotate(k). OriginalSource requires m>=5, s(i)!=0 on every label, a>0 and a<b<2a. Every negative magnitude is at least a and every positive value is at least b, with both bounds attained. The labels p and d are the positive maximum and negative minimum. Exactly m labels of each sign are LARGE at the inclusive threshold Q, and x is positive LARGE. No quotient by tied values, coprimality condition or primitive numerical-period assumption is imposed.

List the LARGE offsets from x in increasing order as 0=d0<...<d_(2m)=k, and write P_i=advance(x,d_i), l_i=d_(i+1)-d_i-1. The last point P_(2m)=x is the excluded boundary; enumeration beyond the last LARGE offset saturates at k. Own rows omit their terminal LARGE label. Retain P1=d, OwnRow(p,L), l0=l1=l2=L, l3<L and l4=L-1. With q=2^L, H=2q, z=N-2s(x), Delta=b-z, n=seed2, b1=seed3, w=N-2s(P4), u=N-2s(P6) and F=2^(l6+1), retain N-Ha>2a, L>=2 or P2!=p, Delta>0, a-1<(H^2+1)Delta, b1>=2a-1, a<=w<=2a-3, n+Delta<w and u>z. The power branch is F=H/2 with H/2>=4, or F<=H/4. The nonET condition supplies an actual offset j<k with d7<=j and -Q<s(advance(x,j))<0.

CornerGeometry further requires m>5, 2^l5=1, 4<=F<=H/4, b<=y<=2b-3 and A>=2b+1, where y=seed7 and A=seed8 is the original a0. Set E(V)=(N+z-2V)/2 and ell=floor(E(A)/b); require ell<=q-3 and E(A)-ell*b>(y-1)/2. The actual row factors define B0=N-2*2^l8*A and T1=N-2*2^l9*B0. Require (F/2,q)=(2,8) or (4,16), A<B0<T1 and B0+1<2A. All quotients here and below are integer quotients. There is no assumed successful landing or endpoint closing equation.

## The selector and its physical support

Restrict to q=16,F=8,m>=9. Let S=seed11, h=2^l11 and U=seed12, with U>z and 3U<N. For 1<=r<=m-7, require the first r actual pairs to be empty on both signs: l_(12+2j)=l_(13+2j)=0 for every j<r. This range includes the true last positive frontier P_(2m-2). Put T=seed_(12+2r) and lambda=floor((((U-z)/2)-1)/S). The natural mask M is h-1-lambda.toNat, using natural subtraction. bitsRS consists of the physical labels in sourceMask of row11 selected by the set binary bits of M. For a physical subset K, charge(K)=sum_(i in K)s(i) and compressedHeight(K)=(N-T+2z)/4-charge(K).

**Definition 1.1 (The universal selector).**

Lean statement: `D5/S3/Combinatorics/Circle/RobustSelectorRefutation.claim`

*Formalization.* `D5/S3/Combinatorics/Circle/RobustSelectorRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every complete OriginalSource and CornerGeometry in this branch, and every r in the stated range with the required empty pairs, claim asserts the existence of K subset bitsRS such that N<=8*charge(K) and compressedHeight(K) mod T<=(T-1)/2. The first inequality is the exact threshold charge(K)>=N/8, without rounding it down. No additional condition on the endpoint row factor or subsequent rows is included.

## The k=51 obstruction

Take m=10,k=51,t=2183577952606008,L=4,a=53391520898079,b=68700259149599,p=9,d=4,x=50. Evaluation of the original modular source verifies all OriginalSource and CornerGeometry conditions. In particular the negative and positive minima are attained at labels10 and5, the extrema at9 and4, and nonET is label40 at offset41 from x. Here N=2251799813685247 and z=68221861079239.

The LARGE labels from x are [50,4,9,14,16,20,21,24,28,30,31,32,35,36,37,38,39,42,44,47]. The corresponding SMALL row lengths are [4,4,4,1,3,0,2,3,1,0,0,2,0,0,0,0,2,1,2,2]. Thus r=2 gives two empty pairs after P12=35, with a nonfinal endpoint P16=39. The allowed upper bound m-7=3 also includes the last positive P18=44.

For this source S=191804389259021,h=4,U=717364699613079,lambda=1 and M=2. Row11 has SMALL labels33 and34; the actual depleted support is exactly {34}. An empty K violates N<=8*charge(K), so every robust subset of bitsRS is {34}. Its charge is 383608778518042, giving 8*charge(K)-N=817070414459089>0.

**Theorem 1.2 (Refutation).**

Lean statement: `D5/S3/Combinatorics/Circle/RobustSelectorRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/RobustSelectorRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r=2 and K={34}, the endpoint seed is T=218836125383029 and compressedHeight(K)=158743074097132. This height is between 0 and T, so it equals its residue modulo T. But (T-1)/2=109418062691514, and the residue exceeds this bound by 49325011405618. The unique robust supported subset therefore fails the landing condition, contradicting claim.

## What the obstruction leaves open

The failed policy retains a robust subset of the depleted holding while requiring a lower-half residue at the endpoint. Any replacement must allow a different supported choice or a different ordering, with the spent labels and every positive cost accounted for. No attained-prefix assertion or continuation theorem is part of this refutation. A supported replacement covering all actual endpoints and mixed tails through the final positive frontier remains to be proved, as do full original existence and coverage of both power branches for all m.

The original circle question is Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture3.1, DOI10.5070/C6.68671. The robust selector is a separate intermediate assertion. Its refutation does not refute that conjecture or establish a literature novelty claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/RobustSelectorRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Circle/RobustSelectorRefutation.result`
- Dependency: [D5/S3/Combinatorics/Circle/OriginalLowerFullBank](OriginalLowerFullBank.md)
