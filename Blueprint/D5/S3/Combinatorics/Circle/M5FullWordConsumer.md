# The original M5 source-to-word implication

## Abstract

Every covered original M5 centered source admits a complete physical-label word beginning with x, with integer total zero and all natural take sums in its original half-modulus strip.

**Theorem 1.1 (All original labels and every take length).**

Lean statement: `D5/S3/Combinatorics/Circle/M5FullWordConsumer.exists_full_word`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/M5FullWordConsumer.exists_full_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural k,t,L, integers a,b and physical labels p,d,x in Fin(k), assume OriginalM5(k,t,L,a,b,p,d,x). Set s=SourceWidth.actualSource(k,t), N=2^k-1, Q=2^(k-2) and C=(2^k-2)/2. Then there exists a list word permuting List.finRange(k), with word.head?=some(x), integer sum(word.map(s))=0, and 0<=sum((word.take(j)).map(s))<=C for every natural j. The empty, complete and overlength takes are included. The permutation places every physical label exactly once, including x.

The hypotheses describe the original centered modular source. It is nonzero; a and b are its attained least negative magnitude and positive value, with a<b<2a; p,d attain its positive maximum and negative minimum. Exactly five physical LARGE labels have each sign, where LARGE means absolute value at least Q. Starting at the positive LARGE x, the sorted next-LARGE cycle is x,d,beta,gamma,P,J,T,U,V0,D0, with x only as boundary. The own rows after p,x,d,beta have length L, the gamma row has length less than L, and the P row has length L-1.

Write H=2^(L+1), z=N-2s(x), n=sourceSeed(2), Delta=b-z, b1=sourceSeed(3), w=N-2s(P), u=N-2s(T), F=2^(length(row after T)+1), and a0=sourceSeed(8). The remaining positive-hard conditions are 2a<N-Ha; L>=2 or beta differs physically from p; Delta>0; a-1<(H^2+1)Delta; 2a-1<=b1; a<=w<=2a-3; n+Delta<w. An actual negative SMALL label lies on the U-inclusive, x-exclusive physical tail. Assume u>z, a0<=z and either F=H/2>=4 or F<=H/4. All offsets, parents, seeds and lengths in these conditions are computed from s, rather than supplied as an arithmetic certificate.

The centered recurrence first gives the exact ten-row telescope and disjoint physical partition. From these source predicates it derives the integer geometry, canonical retained masks, and legal W_J prefix. The T selections are proved in both F branches using the present n,w,z,b,v bank and actual u indices. Depleted binary support is retained explicitly. Neither T selection uses a SMALL label from a row beyond the u row.

After T, the retained old bank, complementary u mask and whole y row give the endpoint -U+(z-a0)/2. U and V0 each pass their own gate. The unused complement after V0 is exactly D0 and the two final own rows. Conservation and the existing TwoLargeOrdering theorem complete this complement. Mapping occurrences to the original Fin(k) partition proves the complete permutation, and SourceWidth.inStrip_prefix gives every natural take sum.

The statement uses the original k and C throughout. It allows tied values, nonunits and source orbits shorter than k, and never replaces physical labels by distinct values. It assumes neither a chosen complete word, an untouched reserve, raw gap persistence, interval density, future viability nor a free action. No prefix reversal or unproved transport is used.

The source problem is Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. This theorem covers precisely the stated positive-hard R1, nonET, u>z, m=5 and a0<=z slice, in both power branches. The arbitrary-tail all-m conjecture remains open. No literature novelty or official acceptance is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/M5FullWordConsumer.exists_full_word`
- Dependency: [D5/S3/Combinatorics/Circle/M5RetainedTail](M5RetainedTail.md)
- Dependency: [D5/S3/Combinatorics/Circle/M5SourceRows](M5SourceRows.md)
- Dependency: [D5/S3/Combinatorics/Circle/SourceWidth](SourceWidth.md)
