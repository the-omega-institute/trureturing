# A local physical two-root repair

## Abstract

A finite mesh on physical SMALL labels and one virtual root increment repairs one local root-only cut.

**Theorem 1.1 (The first slot and its actual negative label stay in the half strip).**

Lean statement: `D5/S3/Combinatorics/Circle/LooseRootRepair.source_cut_root_repair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/LooseRootRepair.source_cut_root_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let alpha be any type with decidable equality, f:alpha->Z its actual weights, and Y a finite set of physical SMALL labels. Let r,s,n,m be four actual labels such that r::s::n::m::Y.toList is duplicate-free. Thus both roots and both negative labels are literally distinct and outside Y. Equal numerical weights of different SMALL labels remain separate occurrences. The integer parameters satisfy Q>=1, N=4Q-1, C=(N-1)/2, B=N-2p, Q<=p<=f(r), 3f(r)<=N, Q<=f(s), f(s)=4p-N<p, f(n)=-B, and f(m)<0. Every x in Y satisfies 0<f(x)<=M and 2M<=B. The entering height satisfies h>=0 and h+f(s)<=C, while C<h+f(r)+sum(Y,f). No subset, allocation, source partition or completion witness is assumed.

There are positive lists P and Q' whose concatenation permutes exactly r::s::Y.toList, is duplicate-free, has disjoint lists, and satisfies P.toFinset union Q'.toFinset = {r,s} union Y. Their heads are respectively r,s or s,r. Every weight in either positive list is strictly positive. The actual first-slot word P++[n] satisfies SourceWidth.InStrip(f,C,h), which bounds every natural take-prefix, including the negative label and both endpoints. Its landing h+sum(P.map(f))-B lies in [0,C-B]. The two positive masses sum to f(r)+f(s)+sum(Y,f). The complete two-slot word (P++[n])++(Q'++[m]) permutes (r::s::Y.toList)++[n,m], and its final height is exactly h+f(r)+f(s)+sum(Y,f)+f(n)+f(m). Thus both outer endpoints and every physical occurrence are preserved. This theorem does not assert that the second slot is legal.

The consumed private mesh lemma uses delta>0, delta<=c and 0<f(x)<=M<=delta+c. For every integer 0<=U<delta+sum(Y,f), it constructs A subset Y and a Boolean e with z=sum(A,f)+(if e then delta else 0)<=U and U-z<c. Induct by adding one actual label of weight w to an old inventory of augmented mass T. If U<T, omit the new label and use the old mesh. Otherwise, if w<=U, use the old mesh at U-w and include the new label. In the remaining case T<=U<w, select the entire old inventory including the virtual increment; T>=delta and w<=delta+c imply U-T<c. The empty actual inventory uses z=0. There is no powerset computation or numerical-value deduplication.

For the physical repair set b=f(s), delta=f(r)-b, c=C-B, and U=C-h-b. The local source arithmetic gives C=2Q-1, c=(b-1)/2, B>0, 0<delta<=c and M<=delta+c. In particular the odd integer B and 2M<=B yield M<=(B-1)/2; p<=f(r) supplies (B-1)/2<=delta+c. The strict premise b<p is retained explicitly; no global exclusion of the constant root-only orbit is claimed. Mesh selection chooses root r when e is true and root s otherwise, together with A; the other root and Y minus A form the second inventory. The first positive mass is b+z, its peak is at most C and its landing is c-(U-z). Strict positivity makes all positive prefixes monotone, and the actual negative step ends at the proved legal landing.

The motivating source is Circle Conjecture 3.1 in Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2. Native moduli N=2^k-1 with k>=2 have the required form N=4Q-1. The source-local cut identities and geometric bands are explicit hypotheses here. The construction formalizes the local root-only step of the completed HAND loose-sweep argument; that argument and finite controls are fallible inputs, not independent certification. Full native chain extraction, the strict-root condition from SMALL presence, global endpoint propagation, a finite sweep, active-to-active repairs, arbitrary source completion and full C3.1 remain outside this local result. No literature-priority claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/LooseRootRepair.source_cut_root_repair`
- Dependency: [D5/S3/Combinatorics/Circle/SourceWidth](SourceWidth.md)
