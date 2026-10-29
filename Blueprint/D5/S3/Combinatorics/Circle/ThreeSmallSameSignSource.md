# Three same-sign SMALL labels, including adjacency

## Abstract

Forward physical completion with exactly three same-sign SMALL occurrences

**Theorem 1.1 (One complete physical word with forward LARGE cyclic order).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeSmallSameSignSource.actualSource_three_small_same_sign_full_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeSmallSameSignSource.actualSource_three_small_same_sign_full_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k>=3 and t be arbitrary natural numbers, f(i)=SourceWidth.actualSource(k,t,i), N=2^k-1, Q=2^(k-2), and C=half(k)=(N-1)/2. Suppose exactly three physical labels satisfy |f(i)|<Q and all such values are nonnegative, or all are nonpositive. There exists one list L of Fin(k) labels which permutes List.ofFn(id), is Nodup, has toFinset equal to univ, satisfies InStrip(f,C,0,L), has mass zero, and satisfies the native Legal(k,t,L). For every natural n, including takes beyond the full length, 0<=mass(f,L.take(n))<=C. The LARGE filter of this same L is List.IsRotated to the LARGE filter of List.finRange(k). No coprimality, numerical injectivity, minimal period, isolation, supplied placement, or total-zero hypothesis is required. Repeated values retain their distinct physical labels.

A zero at one label propagates to the complete native row, so the forward inventory itself is a completion in that case. Otherwise orient the common SMALL sign positively and choose a minimum positive SMALL value as the physical origin. The other SMALL labels occur at forward offsets p and r. The original large_gap_profile, applied to each of the three actual gaps and its positive endpoint, forces the intervening LARGE counts to be 2A,2B,2D. Thus p=2A+1, r=2A+2B+2 and k=2A+2B+2D+3. All of these data are extracted from the native count and seam recurrence, rather than assumed.

Work in sixfold integer units. With F=4^A, G=4^B, H=4^D, let d=N-6w(0), e=N-6w(p), z=N-6w(r). The cyclic endpoint equations are 2Fd=N+e, 2Ge=N+z and 2Hz=N+d. Since N=8FGH-1 they give d=4GH+2H+1, e=4HF+2F+1 and z=4FG+2G+1. Choosing the least SMALL value makes d the greatest deficit. A block with deficit d has pair values 2N-2*4^j*d and -2N-4*4^j*d. From initial height h its valleys are h+2d-2*4^j*d and its peaks are h+2N+2d-4*4^j*d. The existing paired_segment induction, monotonicity and endpoint bounds control every physical step. A sixfold height at most 3N gives the sharp unscaled integer bound C.

If only the Z block is nonempty, the word is beta, the first D-1 Z pairs, alpha, gamma, then the last Z pair. If Y and Z are nonempty and A=0, start at beta and insert alpha before the last Y pair when e<=z, or after the whole Y block when z<e; insert gamma immediately before the last Z pair. These words also cover empty initial segments. With all blocks nonempty choose the least Y cut jY with d<=4^jY*e. Choose the Z cut explicitly from jZ=max(1,D-A). The closed deficits and maximality of d imply 1<=jZ<=D and d<=4^jZ*z<=2(d+z). Place beta, all X pairs, the first jY-1 Y pairs, alpha, the remaining Y pairs, the first jZ-1 Z pairs, gamma, and the remaining Z pairs. The inequalities on both sides of each cut bound the valleys below and peaks above; the cyclic endpoint equations give final height zero. Every physical position occurs once. In every branch deleting the three SMALL labels leaves precisely the consecutive X, Y and Z arcs in forward order.

The physical phase map is addition by the chosen origin in the cyclic group Fin(k). It transports the normalized inventory to the actual labels and sends the native forward inventory to a cyclic rotation. Filtering commutes with that map. For negative orientation the original negate_rotation theorem cuts the positive strip word at an extremum and negates the weights; prefix heights stay in the same strip, with no reversal of physical order. Filtering this final cyclic cut preserves the whole forward LARGE cycle. The group action transports occurrences rather than numerical values, so the argument includes nonunits and proper numerical periods.

The source context is Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. This construction treats the complete exactly-three, same-sign SMALL subcase with adjacency. Mixed SMALL signs, arbitrary SMALL counts with adjacency, and full Conjecture 3.1 remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeSmallSameSignSource.actualSource_three_small_same_sign_full_completion`
- Dependency: [D5/S3/Combinatorics/Circle/TwoSmallSource](TwoSmallSource.md)
