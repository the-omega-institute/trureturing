# Isolated SMALL labels with no bound on their number

## Abstract

A finite centered-doubling permutation whose SMALL labels have one sign and are never consecutive admits a full half-strip ordering.

**Theorem 1.1 (Completion of the complete physical inventory).**

Lean statement: `D5/S3/Combinatorics/Circle/IsolatedSmallSource.finite_isolated_small_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/IsolatedSmallSource.finite_isolated_small_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let sigma be a permutation of a finite nonempty type of physical labels, let Q>=2, N=4Q-1 and C=2Q-1, and let the integer value w(i) lie in [-C,C]. Assume w(sigma(i)) is the strict centered doubling of w(i). A label is SMALL when |w(i)|<Q. Assume all SMALL values are nonnegative or all are nonpositive, and that every SMALL label has a LARGE successor. There is a permutation word of all physical labels whose every prefix lies in [0,C] and whose total is zero. Neither the SMALL cardinality nor the number of permutation cycles is bounded. Equal numerical values keep their separate labels. A total-zero premise, unit hypothesis and minimal-period hypothesis are unnecessary.

In the positive orientation isolation excludes zero, every negative value is LARGE, a positive SMALL value doubles to a positive LARGE value, and a positive LARGE value p has successors 2p-N and 4p-N. A maximum positive value gives 3p<=N for all positive values and 6a<N for SMALL values. A minimum SMALL value a gives N<=7a by following three successors. A minimum positive LARGE value then gives 2N<=7p for every positive LARGE root. These are finite permutation arguments, independent of any gap classification.

Each positive LARGE label i owns its following negative label sigma(i). If sigma squared(i) is SMALL, it also owns that label, forming the ordered packet [i,sigma squared(i),sigma(i)]. Otherwise its packet is [i,sigma(i)]. The first packet has nonnegative net b<N/24 and peak <11N/24. The second has nonnegative loss ell<=N/28 and positive peak <=N/3. Inverse permutation and the three disjoint sign/size categories prove that these packets partition every physical occurrence exactly once. The unsigned potential identity from SourceWidth telescopes over sigma to derive the total zero.

Order whole packets by paying an affordable loss packet first, and otherwise taking a nonnegative packet. Packet boundaries satisfy 0<=h and 168h<13N. A nonnegative packet is entered with 28h<N; exact remaining mass prevents deadlock, including zero-loss and zero-net packets. Expanded nonnegative-packet heights are <83N/168, and loss-packet heights are <69N/168. Both are <N/2, so integrality gives the required upper bound C. For the negative orientation the existing negate_rotation theorem cuts at an attained extremum of prefix sums; it preserves all physical labels and does not reverse their order.

The motivating source is Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. For that conjecture the substitution is the actual centered source on Fin k, sigma=finRotate k, Q=2^(k-2), and k>=3. The native source geometry and seam recurrence supply all bounds and permutation hypotheses. This settles the complete isolated, same-sign SMALL subcase, with arbitrarily many SMALL positions. The construction may change the order of different LARGE pairs. Sources containing adjacent SMALL labels or SMALL labels of both signs, and full Conjecture 3.1, remain open.

**Theorem 1.2 (Both native cyclic filters and a strict prefix margin).**

Lean statement: `D5/S3/Combinatorics/Circle/IsolatedSmallSource.actualSource_isolated_same_sign_cyclic_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/IsolatedSmallSource.actualSource_isolated_same_sign_cyclic_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual centered source on every physical label Fin k, k>=3 and arbitrary natural t, assume only that all SMALL values have one weak sign and that every SMALL label has a LARGE physical forward successor. One ordering of all labels has every natural take-prefix height h in [0,C], satisfies 28h<13N, ends at zero, is native Legal, and preserves the native forward cyclic order of both its LARGE and its SMALL filtered lists. Here N=2^k-1, Q=2^(k-2), and C=(N-1)/2. The witness is a physical permutation, is duplicate-free and exhausts Fin k. An empty SMALL filter and all-LARGE sources are included. Isolation itself excludes the zero source.

Orient the common SMALL sign positively. The existing isolated_geometry bands show that every SMALL label a has a negative LARGE predecessor n and a positive LARGE predecessor p of n. Choose a physical positive LARGE root of minimum value p0. The label involution tau swaps each such adjacent negative/SMALL pair and fixes the other labels. Traversing the native cycle from the chosen root and mapping tau changes [p,n,a] to [p,a,n], and leaves [p,n] fixed. Scanning these disjoint adjacent pairs proves exact equality of each filtered order before restoring the native cyclic cut. Tau need not commute with the physical successor; no commuting conjugacy is asserted.

Use the corrected integer potential P(i)=2w(i)-w(pred(i)) on SMALL phases, and P(i)=w(i)+N on negative phases or w(i) otherwise. Its successor difference is w(tau(i)). Prefixes therefore telescope to P(phase(j))-p0, including long natural takes and the zero endpoint after k physical steps. The geometry bounds 2N<=7p0, 3p<=N and 6a<N give 0<=P-p0 and 28(P-p0)<13N in all three phase categories. Since N=2C+1, integrality gives the half-strip bound. The potential is attached to physical labels, so repeated values, nonunits and proper numerical periods introduce no extra assumptions.

For a nonpositive SMALL source, apply the construction to its negative and rotate the negated word at a maximum original prefix. Each resulting height is the old height at the cut minus another old prefix height, so it is nonnegative and at most the cut height. The old strict 13N/28 bound therefore transports explicitly, together with both filtered cyclic orders. The negate_rotation_prefix_bound theorem controls every rotated prefix by this cut height.

This strengthens the isolated same-sign subcase motivated by Monochromatic configurations on a circle, arXiv:2504.10687v2. It supplies neither an ordering for arbitrary adjacent SMALL labels nor a resolution of full Circle Conjecture 3.1. The argument and library synthesis make no literature novelty claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/IsolatedSmallSource.actualSource_isolated_same_sign_cyclic_completion`
- Truth anchor: `D5/S3/Combinatorics/Circle/IsolatedSmallSource.finite_isolated_small_completion`
- Dependency: [D5/S3/Combinatorics/Circle/SmallStepOrdering](SmallStepOrdering.md)
- Dependency: [D5/S3/Combinatorics/Circle/TwoSmallSource](TwoSmallSource.md)
