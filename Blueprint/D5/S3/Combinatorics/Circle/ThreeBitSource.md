# Three-bit circle sources at half-modulus capacity

## Abstract

All three-bit centered sources admit physical-label permutations with every integer prefix in the half-modulus strip and integer total zero.

**Theorem 1.1 (A complete order for every three-bit source).**

$$\forall k \in \mathrm{Nat},\; \forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; 0 < a \Rightarrow \left(a < b \Rightarrow \left(b < k \Rightarrow \left(\exists word \in \operatorname{List}\left(\operatorname{Fin}\left(k\right)\right),\; \operatorname{Perm}\left(word, \operatorname{finRange}\left(k\right)\right) \land \left(\left(\forall n \in \mathrm{Nat},\; 0 \le \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(k, 1 + 2^{a} + 2^{b}\right), \operatorname{take}\left(n, word\right)\right)\right) \land \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(k, 1 + 2^{a} + 2^{b}\right), \operatorname{take}\left(n, word\right)\right)\right) \le 2^{k - 1} - 1\right) \land \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(k, 1 + 2^{a} + 2^{b}\right), word\right)\right) = 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeBitSource.three_bit_source_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural k,a,b with 0<a<b<k, put t=1+2^a+2^b, N=2^k-1 and C=2^(k-1)-1. The theorem supplies a permutation of all original Fin(k) labels. Every natural-length prefix of its actualSource(k,t) increments has integer sum in the closed interval [0,C], and the integer total is zero. The statement includes n=0, every internal prefix and saturated takes with n>k. It assumes neither coprimality nor distinct source values, a primitive period, an annulus, a capacity witness or a special gap regime. At k=3 the hypotheses force a=1,b=2 and t=N, so all physical increments are zero.

Multiplication by two modulo N cyclically rotates the three support positions. Rotating physical labels is a bijection even when a nonunit source has repeated values or a shorter value period. Write the positive cyclic gaps as x,y,z, with x+y+z=k, and set P=2^x, Q=2^y, R=2^z. The three post-negative bases are u=1+P+PQ, v=1+R+RP and w=1+Q+QR. Choose any minimum among u,v,w and rotate its physical labels to the first position. Equality is retained: no unique minimizer is required. Binary power comparison then forces x<=z, y<=z; if z=x, all gaps are equal. Thus z>=2 for k>=4.

The source identities are Ru=N+v, Qv=N+w and Pw=N+u. They give exactly the U ladder 2^e u for e<z-1, its negative label -A_v, the V ladder 2^e v for e<y-1, its negative label -A_w, and the W ladder 2^e w for e<x-1, followed by -A_u, where A_s=(N-s)/2. All halves here are exact integer halves. Empty V or W ladders are allowed. These are the actual centered representatives at the physical positions, derived by the source rotation and centered representative uniqueness. The supplier's unsigned potential telescopes around the full physical cycle, proving integer total zero rather than merely zero modulo N.

The first packet is fixed exactly. Put m=floor(C/u) and n=2^(z-1)-1-m. Oddness and Ru=N+v give n=floor((v-1)/(2u)), A_v<=mu<=C and h=mu-A_v=v-(n+1)u in [0,C]. The m-bits of the U ladder form the first packet. The original DyadicPrefix.bitSubset decoder supplies its physical positions and sum. Since m+n is the all-ones mask, the n-bits are exactly its disjoint complement; replacing this complement by an interval of available coefficients would be invalid.

The second packet uses an actual submask c of n and legal untouched-ladder coefficients 0<=dV<Q/2 and 0<=dW<P/2. Its mass is q=cu+dVv+dWw, and the construction proves q>=0 and 0<=E=C-h-q<=D=(w-1)/2. Thus h+q lies between A_w and C. For P<Q, Q>=4P admits a ceiling choice on the V ladder. The adjacent power Q=2P splits into R<=P^2/2, R>=2P^2 and the sole middle power R=P^2. The middle coefficient formula uses P>=4; P=2,R=4 is handled separately. For P>=Q, put H=P/Q, delta=R-P-H+1 and T=(u-1)/2. The direct choice c=n,dV=0,dW=P/2-H works when delta<=T, including all equal-gap ties.

When delta>T, an actual unused mask with residue s in [delta-T,w-u] permits a coupled transfer across both untouched ladders. The modular extraction chooses a legal V coefficient and compensates by a W coefficient; it proves their full upper and lower bounds as well as the final residue bound. For Q=2, the V ladder is empty. P=2 admits the empty packet; otherwise the source quotient forces one of two specified singleton bits to work. The odd branch includes the double wrap. For Q>=4 and H=1,2,4, the source forces the top bit R/(4Q) to be present, and the ratio-specific residue calculations use respectively zero, zero and one wrap. None of these arguments asserts a universal rule for the highest unused bit.

The remaining cone is Q>=4, H>=8, R>=PQ. Put L=R/(PQ), n0=floor(PQ(P+1)/(2u)) and b0=n0 mod Q. Division of the power P/2 by the odd number Q+1, together with coprimality, excludes a zero remainder. The exact quotient calculation gives 0<b0<Q. From floor(n/L)=n0 one obtains n=LQj+Lb0+e with 0<=e<L. Let e0 be the least index of a nonzero binary digit of b0 and put ell=2^e0. Then r=L ell is an actually present bit of n in the window z-x-y through z-x-1, with 1<=ell<=Q/2. Its deletion c=n-r is a support difference with no borrow, not just a numerical inequality.

For this forced bit, S=ru satisfies delta-T<S<w-u<w without a wrap. Set i=min(Q/2,floor((S+T)/delta)). Then 1<=i<=Q/2 and E=S+T-i delta lies in [0,D]. The coefficients c=n-r, dV=i-1 and dW=P/2-iH are legal simultaneously, and their actual packet mass ends at C-E. This is the two-ladder transfer: a selected U bit is exchanged against linked V and W allocations belonging to the same source. A generic highest-unused-bit rule would fail, for example at k=24,a=8,b=10,t=1281; the source-forced window selects bit 32 instead.

Map these masks injectively to their U,V,W physical labels. Let F be the first mask, Qset the disjoint union of the three second-packet masks, and G every remaining positive physical label. The word is F, the negative-v label, Qset, the negative-w label, G, the negative-u label. Its seam heights are 0,mu,h,h+q,h+q-A_w,A_u,0. Positive blocks stay between their endpoints, and every negative jump has both endpoints in [0,C]. Disjoint support and exhaustive complement prove a permutation of all k physical labels. The final cyclic permutation returns this word to the original labels. Equal values never identify physical occurrences.

This supplies another sufficient source family at the exact half-modulus capacity C. It does not solve the full arbitrary-source problem, and it makes no minimum-width or global optimality claim. The source problem is Damasdi–Frankl–Pach–Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. The three-bit construction is repository-derived; the paper is not asserted to contain it. No worldwide novelty or model-diversity claim is made.

Informal construction sources are identified by supplied terminal artifact role and content identity: residual proposal 6e20147c2660b5103218a9182c3b9f3ac5a899ebe9733daf612eb50f6f920f2f; complementary audit 7cf9ff5790ae6e678e05e6b10b7a38016b6a8fe1514ef7d87a7934580f14b2d7; second-packet progress fbf46f521c50dc947edddce95c0d7587581e033bc10ccea9bc89e21b9f7ddbad; three-chain progress 91f74315f42924fa8202703b3cf579f6d43027ece89fc7ea040138848d960430. These identities supply provenance, not formal truth or a human authorship attribution.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeBitSource.three_bit_source_order`
- Dependency: [D5/S3/Combinatorics/Circle/DyadicPrefix](DyadicPrefix.md)
- Dependency: [D5/S3/Combinatorics/Circle/SourceWidth](SourceWidth.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeBitSourcePackets](ThreeBitSourcePackets.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeBitSourceResidual](ThreeBitSourceResidual.md)
