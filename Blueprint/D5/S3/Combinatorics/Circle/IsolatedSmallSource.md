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

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/IsolatedSmallSource.finite_isolated_small_completion`
- Dependency: [D5/S3/Combinatorics/Circle/SmallStepOrdering](SmallStepOrdering.md)
- Dependency: [D5/S3/Combinatorics/Circle/TwoSmallSource](TwoSmallSource.md)
