# Native full completion with exactly two physical SMALL labels

## Abstract

Native full completion with exactly two physical SMALL labels

The physical source is centered modulo N=2^k-1. A label is SMALL when its absolute increment is less than Q=2^(k-2); all other labels are LARGE. Physical occurrences are counted even when their numerical values coincide.

**Theorem 1.1 (Physical phase is cyclic addition).**

Lean statement: `D5/S3/Combinatorics/Circle/TwoSmallSource.phase_add`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/TwoSmallSource.phase_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k>0, a physical origin o in Fin(k), and any natural j, phase(k,o,j) is o plus the Fin(k) residue of j modulo k. Thus a phase change acts on physical occurrences by the cyclic group, independently of any coincidences among their numerical source values. Both the two-SMALL and three-SMALL constructions use this identity to recover forward physical coordinates.

**Theorem 1.2 (Filtering preserves a cyclic cut).**

Lean statement: `D5/S3/Combinatorics/Circle/TwoSmallSource.filter_rotate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/TwoSmallSource.filter_rotate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any label type, Boolean predicate p, list l and natural cut n, filtering l.rotate(n) is List.IsRotated to filtering l. Split l into its prefix and suffix at n modulo its length and filter both pieces. The conclusion includes empty filters and records cyclic order without reversal. It transfers the LARGE order through the physical phase and through the final sign-restoring cut in the two-SMALL and three-SMALL completions.

**Theorem 1.3 (Extracting and closing the actual physical gaps).**

Lean statement: `D5/S3/Combinatorics/Circle/TwoSmallSource.actual_two_gap_profile`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/TwoSmallSource.actual_two_gap_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural k>=3 and t, let f(i)=SourceWidth.actualSource(k,t,i), Q=ExpandingSourcePath.quarter(k), and C=ExpandingSourcePath.half(k)=(2^k-1)/2. Assume exactly two physical labels satisfy |f(i)|<Q. There exist an actual origin o, an orientation sign, and gaps ell<=m with k=ell+m+2 and ell,m of equal parity. In the oriented forward physical phase w, both SMALL magnitudes are positive, 3w(0)=C-(-2)^m and 3r=C-(-2)^ell, and both complete signed LARGE-arc formulas hold. For every j<k, Q<=|w(j)| holds exactly when j is neither 0 nor ell+1; this classification is derived from the original SMALL count. The shorter of the two actual circular distances determines the origin; orientation only changes arithmetic signs. A zero source value would propagate to the whole physical row by AntipodalSourceCompletion.opposite_rotation, making every label SMALL, which contradicts k>=3 and the count two. ExpandingSourcePath.phase_step includes the physical wrap, and SourceWidth.centered_bounds supplies the full centered interval. No numerical least period, coprimality or value injectivity is used.

**Theorem 1.4 (A complete physical half-strip word for every natural prefix).**

Lean statement: `D5/S3/Combinatorics/Circle/TwoSmallSource.actualSource_two_small_full_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/TwoSmallSource.actualSource_two_small_full_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under precisely k>=3, arbitrary natural t and exactly two physical SMALL labels, there exists a list L of physical Fin(k) labels which permutes List.ofFn(id), is Nodup, has toFinset equal to univ, lies in SourceWidth.InStrip(f,C,0,L), has total mass zero, and satisfies TwoOppositeLargeExchange.Legal(k,t,L). The theorem explicitly returns 0<=mass(f,L.take(n))<=C for every natural n. Thus the empty prefix, every intermediate prefix, the full word, and takes beyond its length are all included. Its LARGE physical-label filter is List.IsRotated to the LARGE filter of the forward native List.finRange(k) order, so sign restoration changes the cyclic starting point only and never reverses the physical order. Ties and proper numerical periods retain every distinct physical occurrence.

The native profile supplies every premise of the even-gap or odd-gap placement theorem, including all cut and seam bounds. Applying the physical phase map sends the natural-position permutation to an actual permutation of Fin(k). Positive orientation uses this word directly. Negative orientation first negates the word and cuts at an attained minimum prefix; ZeroSumWordCount.nonnegative_rotate_of_minimum supplies the lower bound, and its prefix_segment_sum together with the original strip supplies the upper bound C. Deleting the two SMALL ears in each normalized placement leaves the consecutive first and second LARGE arcs in forward order. Filtering commutes with the physical phase map; that map is the rotation of List.finRange(k) by the origin label. Filtering the minimum-prefix rotation preserves List.IsRotated. This establishes the final LARGE cyclic-order conjunct for the same completion witness. The scaled arithmetic is divided by three inside the integer strip predicate. The native Legal predicate then follows from Nodup and all prefixes. Equal odd gaps already have an opposite pair and fall within AntipodalSourceCompletion; they provide no separate extension of that source domain. The new two-defect placement allows unequal even gaps, unequal odd gaps and zero gaps.

**Theorem 1.5 (Restoring signs by a cyclic cut).**

Lean statement: `D5/S3/Combinatorics/Circle/TwoSmallSource.negate_rotation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/TwoSmallSource.negate_rotation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any integer-valued label word L in [0,C] with total zero, there is a cyclic cut j such that every natural prefix of L.rotate(j), evaluated with the negated weights, is again in [0,C]. Choose an attained minimum of the negated prefix sums. The existing nonnegative_rotate_of_minimum theorem gives the lower bound, while prefix_segment_sum and the original strip give the upper bound. The operation changes only the cyclic starting point and preserves every physical occurrence. Both the two-SMALL completion and the arbitrary-count isolated same-sign SMALL construction consume this same sign-restoration theorem.

The mathematical source context is Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. This result treats exactly two physical SMALL labels. Arbitrary-defect completion and the full global strict lexicographic exchange remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/TwoSmallSource.actualSource_two_small_full_completion`
- Truth anchor: `D5/S3/Combinatorics/Circle/TwoSmallSource.actual_two_gap_profile`
- Truth anchor: `D5/S3/Combinatorics/Circle/TwoSmallSource.filter_rotate`
- Truth anchor: `D5/S3/Combinatorics/Circle/TwoSmallSource.negate_rotation`
- Truth anchor: `D5/S3/Combinatorics/Circle/TwoSmallSource.phase_add`
- Dependency: [D5/S1/Words/Compositions/ZeroSumWordCount](../../../S1/Words/Compositions/ZeroSumWordCount.md)
- Dependency: [D5/S3/Combinatorics/Circle/AntipodalSourceCompletion](AntipodalSourceCompletion.md)
- Dependency: [D5/S3/Combinatorics/Circle/TwoSmallPlacement](TwoSmallPlacement.md)
