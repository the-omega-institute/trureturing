# A sharp three-parent source family

## Abstract

An infinite family of actual centered doubling sources has an exactly optimal physical permutation width, ten below its half-modulus capacity.

**Theorem 1.1 (Every label, every prefix, and the matching lower bound).**

$$\forall r \in \mathrm{Nat},\; 4 \le r \Rightarrow \left(\left(\exists word \in \operatorname{List}\left(\operatorname{Fin}\left(r + 4\right)\right),\; \operatorname{Nodup}\left(word\right) \land \left(\operatorname{toFinset}\left(word\right) = \mathrm{univ} \land \left(\forall n \in \mathrm{Nat},\; 0 \le \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(r + 4, 11 \cdot 2^{r - 1} - 1\right), \operatorname{take}\left(n, word\right)\right)\right) \land \left(\operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(r + 4, 11 \cdot 2^{r - 1} - 1\right), \operatorname{take}\left(n, word\right)\right)\right) \le 8 \cdot 2^{r} - 11 \land \left(0 \le \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(r + 4, 11 \cdot 2^{r - 1} - 1\right), \operatorname{take}\left(n, word\right)\right)\right) \land \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(r + 4, 11 \cdot 2^{r - 1} - 1\right), \operatorname{take}\left(n, word\right)\right)\right) \le 8 \cdot 2^{r} - 1\right)\right)\right)\right)\right) \land \left(\forall word \in \operatorname{List}\left(\operatorname{Fin}\left(r + 4\right)\right),\; \operatorname{toFinset}\left(word\right) = \mathrm{univ} \Rightarrow \left(\forall L \in \mathrm{Int},\; \forall B \in \mathrm{Int},\; \left(\forall n \in \mathrm{Nat},\; L \le \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(r + 4, 11 \cdot 2^{r - 1} - 1\right), \operatorname{take}\left(n, word\right)\right)\right) \land \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(r + 4, 11 \cdot 2^{r - 1} - 1\right), \operatorname{take}\left(n, word\right)\right)\right) \le B\right) \Rightarrow 8 \cdot 2^{r} - 11 \le B - L\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeParentFamily.sharp_actual_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural r>=4, set T=2^r, k=r+4, N=16T-1, C=8T-1 and natural t=11*2^(r-1)-1. The source is exactly SourceWidth.actualSource(k,t), on all Fin(k) occurrence labels. There exists a distinct complete physical-label list whose integer prefix sums, for every natural prefix length including lengths beyond its end, lie both in [0,P] and [0,C], where P=8T-11. Conversely, for any complete occurrence list and any integer interval [L,B] containing every prefix sum, P<=B-L. The lower bound even allows repeated labels in that other list; completeness forces the positive step P to occur.

Put U=T/2. Centered doubling gives the exact source sequence (11U-1,-10U-1,12U-3,-8U-5,16U-11,-21,-42,...,-21*2^(r-2)). The proof computes the first five branches and then inducts through the actual negative dyadic children. The modulus is 32U-1, and the bound 4*2^j<=U keeps every required internal child doubling in its centered branch. No coprimality assumption or replacement of occurrences by numerical values is used.

Let H=5U-10 and delta=(-H) mod 21, so 0<=delta<=20 and H+delta is divisible by 21. The children have total mass 21(U-1). The integer n=(H+delta)/21 satisfies 0<=n<U=2^(r-1). Binary digit selection partitions the original physical child list into before and after, with selected mass 21n=H+delta and complementary mass P-delta. Both lists consist solely of negative actual occurrences. Thus each segment decreases monotonically between its displayed endpoints.

At height delta the first two full arcs have heights delta, delta+11U-1, delta+U-2, delta+13U-5, delta+H. The selected children then reach zero; the third parent reaches P; the complementary children return to delta. Rotation at that attained zero is explicit: execute the third parent, the complementary children, the first two full arcs, and the selected children. All labels occur exactly once, and the closed path starts and ends at zero. The first-two-arc peak is 13U-5+delta. When r>=5, U>=16 and P-(13U-5)=3U-6>=42>20. At r=4, U=8, H=30, delta=12 and that peak is 111<=117=P. These bounds prove all intermediate prefixes, including both closed walls.

For the lower bound, locate physical label 4 in any complete list. Its actual value is P. The sums immediately before and after that occurrence differ by P, so any containing interval must have width at least P. This argument combines with the constructed word to give the exact optimum for this family. It does not assert that maximum absolute step is the optimum for arbitrary centered sources.

The source problem is Damasdi–Frankl–Pach–Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. The dynamic construction is a special-family result with a compatible binary split and movable base. It supplies no arbitrary-source choice of sign orders, arc partitions or compatible bases. The universal half-modulus forcing step and full C3.1 remain open. No literature novelty or official uniqueness claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeParentFamily.sharp_actual_family`
- Dependency: [D5/S3/Combinatorics/Circle/SourceWidth](SourceWidth.md)
