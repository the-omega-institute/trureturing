# Type-I Occurrences in the Seven-Letter Source Word

## Abstract

Native seven-letter substitution boundaries and terminal return cancellation.

The alphabet is Fin 7. The image of i below 6 is [0,i+1], and the image of 6 is [0,6,6]. The word u is the limit of the actual nested iterates on 0. B(i) is the length of the substituted prefix of i letters. Occ(s,q) means that the length-|s| factor at natural position q equals s. Consecutive starts a<b have no intervening occurrence; overlapping factors and the origin remain in the domain.

The Type-I sequence starts with W(0)=[6]. At ordinary phases W(n+1)=phi(W(n))[0]; at phase n modulo 6 equal to 5 it is [6]phi(W(n))[0,6]. Left and right extensions are defined by actual occurrences of c::s and s++[c], respectively.

**Theorem 1.1 (Actual limit and exact block semantics).**

$$\left(\forall k \in \mathbb{N},\; factor\left(word\left(\right), 0, length\left(image\left(phi\left(\right), k, 0\right)\right)\right) = image\left(phi\left(\right), k, 0\right)\right) \land \left(StrictMono\left(boundary\left(\right)\right) \land \left(boundary\left(0\right) = 0 \land \left(\left(\forall i \in \mathbb{N},\; boundary\left(i\right) = prefixImageLengthSum\left(i\right)\right) \land \left(\left(\forall i \in \mathbb{N},\; \forall n \in \mathbb{N},\; factor\left(word\left(\right), boundary\left(i\right), length\left(subst\left(phi\left(\right), factor\left(word\left(\right), i, n\right)\right)\right)\right) = subst\left(phi\left(\right), factor\left(word\left(\right), i, n\right)\right)\right) \land \left(\forall q \in \mathbb{N},\; word\left(q\right) = 0 \Leftrightarrow \left(\exists i \in \mathbb{N},\; q = boundary\left(i\right) \land \left(\forall j \in \mathbb{N},\; q = boundary\left(j\right) \Rightarrow j = i\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordTypeIOccurrence.actual_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All finite iterates are prefixes of u. Prefix compatibility follows by writing the next iterate on 0 as the current iterate followed by the same iterate on 1; the latter is nonempty. Unbounded lengths make the pointwise definition total. Substituting arbitrary prefix windows gives the fixed-point block equation. Every image starts with zero and has no other zero, so the zeros are precisely the unique true boundaries, including B(0)=0. The displayed prefixImageLengthSum(i) denotes the sum of |phi(u(j))| over j<i.

**Theorem 1.2 (Final-six deletion on actual return intervals).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; 0 < a \Rightarrow \left(a < b \Rightarrow \left(\left(word\left(a - 1\right) = 5 \lor word\left(a - 1\right) = 6\right) \Rightarrow \left(\left(word\left(b - 1\right) = 5 \lor word\left(b - 1\right) = 6\right) \Rightarrow returnWord\left(boundary\left(a\right) - 1, boundary\left(b\right) - 1\right) = append\left(singleton\left(6\right), dropLast\left(subst\left(phi\left(\right), returnWord\left(a, b\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordTypeIOccurrence.terminal_interval_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a<b with the actual predecessor letters at a and b in {5,6}, both preceding image letters are 6. The interval [B(a)-1,B(b)-1) has length B(b)-B(a), exactly the length of phi(u[a,b)). The identity therefore prepends 6 and deletes the final 6 of phi(u[a,b)); it does not increase the length. The proof uses contiguous native factors and applies whether or not the occurrence windows at a and b overlap.

**Theorem 1.3 (Bidirectional ordinary occurrence parsing).**

$$\forall s \in List\left(Fin\left(7\right)\right),\; \forall q \in \mathbb{N},\; Occ\left(sentinel\left(s\right), q\right) \Leftrightarrow \left(\exists i \in \mathbb{N},\; q = boundary\left(i\right) \land Occ\left(s, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordTypeIOccurrence.ordinary_occurrence_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every native finite word s and every natural q, phi(s) followed by zero occurs at q exactly when q=B(i) for an occurrence of s at i. The three-letter prefix of phi(c)[0] is injective in c: it is [0,c+1,0] below 6 and [0,6,6] at 6. Reserving the final zero therefore disambiguates the images of both 5 and 6. Recursive decoding includes empty s and imposes no nonoverlap condition.

**Theorem 1.4 (No Type-I occurrence at the origin).**

$$\forall n \in \mathbb{N},\; Occ\left(typeI\left(n\right), 0\right) \Rightarrow False\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordTypeIOccurrence.typeI_not_at_origin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An ordinary step desubstitutes an occurrence at zero to an occurrence at zero at the previous index. A terminal step starts with 6, whereas u(0)=0. Induction from W(0)=[6] excludes position zero at every index.

**Theorem 1.5 (Terminal parsing with exact source contexts).**

$$\forall s \in List\left(Fin\left(7\right)\right),\; \forall q \in \mathbb{N},\; Occ\left(terminal\left(s\right), q\right) \Leftrightarrow \left(\exists a \in \mathbb{N},\; 0 < a \land \left(q = boundary\left(a\right) - 1 \land \left(Occ\left(s, a\right) \land \left(\left(word\left(a - 1\right) = 5 \lor word\left(a - 1\right) = 6\right) \land \left(word\left(a + length\left(s\right)\right) = 5 \lor word\left(a + length\left(s\right)\right) = 6\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordTypeIOccurrence.terminal_occurrence_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initial 6 is the final 6 before a true boundary: the following zero excludes the first 6 of 066. Decoding the central sentinel gives the source occurrence. The preceding image ends in 6 exactly for source letters 5 and 6; its successor image begins 06 exactly for those same two letters.

**Theorem 1.6 (Ordinary consecutive returns).**

$$\forall s \in List\left(Fin\left(7\right)\right),\; \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; Consecutive\left(sentinel\left(s\right), boundary\left(a\right), boundary\left(b\right)\right) \Leftrightarrow Consecutive\left(s, a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordTypeIOccurrence.ordinary_consecutive_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict boundary monotonicity and the all-position occurrence equivalence transfer consecutiveness in both directions. Every intermediate target occurrence would decode to an intermediate source occurrence, including overlapping windows.

**Theorem 1.7 (All seven counts survive endpoint cancellation).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; 0 < a \Rightarrow \left(a < b \Rightarrow \left(\left(word\left(a - 1\right) = 5 \lor word\left(a - 1\right) = 6\right) \Rightarrow \left(\left(word\left(b - 1\right) = 5 \lor word\left(b - 1\right) = 6\right) \Rightarrow parikh\left(returnWord\left(boundary\left(a\right) - 1, boundary\left(b\right) - 1\right)\right) = mulVec\left(M\left(\right), parikh\left(returnWord\left(a, b\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordTypeIOccurrence.terminal_return_parikh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At positive source endpoints with predecessor letters in {5,6}, the deleted final 6 and the prepended 6 cancel in every coordinate. Thus the native shifted return has count vector M times the count vector of the source return. Column c of M is the actual count vector of phi(c).

**Theorem 1.8 (An actual minimum base return).**

$$\left(\exists a \in \mathbb{N},\; \exists b \in \mathbb{N},\; Consecutive\left(typeI\left(0\right), a, b\right) \land returnWord\left(a, b\right) = singleton\left(6\right)\right) \land \left(\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; Consecutive\left(typeI\left(0\right), a, b\right) \Rightarrow unit\left(6\right) \le parikh\left(returnWord\left(a, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordTypeIOccurrence.base_return_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sixth iterate on zero has a 6 at position 63. Its substituted block gives an actual 0660 window at B(63). The adjacent 6s are consecutive occurrences of [6], with return [6]. Every actual return to [6] begins with 6, so its count vector dominates e(6).

**Theorem 1.9 (Complete factor Parikh recurrence).**

$$\left(\forall n \in \mathbb{N},\; parikh\left(typeI\left(n + 1\right)\right) = mulVec\left(M\left(\right), parikh\left(typeI\left(n\right)\right)\right) + increment\left(n\right)\right) \land \left(\left(\forall n \in \mathbb{N},\; parikh\left(typeI\left(n\right)\right) = mulVec\left(matrixPower\left(M\left(\right), n\right), unit\left(6\right)\right) + parikhCorrectionSum\left(n\right)\right) \land \left(\forall n \in \mathbb{N},\; \forall c \in Fin\left(7\right),\; parikh\left(image\left(phi\left(\right), n, c\right)\right) = mulVec\left(matrixPower\left(M\left(\right), n\right), unit\left(c\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordTypeIOccurrence.typeI_parikh_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write e(c) for unit(c), and increment(n)=e(0) at ordinary phases and e(0)+2e(6) at phase 5. The correction sum at n is the sum of M raised to n-1-k times increment(k), over 0<=k<n. The displayed parikhCorrectionSum denotes exactly this finite sum. Induction proves both its equality with the actual factor counts and the matrix formula for actual iterated letter images.

**Theorem 1.10 (Exact actual left and right extension sets).**

$$\forall n \in \mathbb{N},\; Lext\left(typeI\left(n\right)\right) = \{phase\left(n\right),6\} \land Rext\left(typeI\left(n\right)\right) = \{phase\left(n\right),6\}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordTypeIOccurrence.typeI_extensions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both sets equal {n modulo 6,6}. Membership in each extension set means an actual occurrence with the indicated neighboring letter, so equality includes witnesses for both letters. The base witnesses are 06,66,60 in the actual 0660 window. Ordinary steps send contexts through the last letter of their images. At phase 5, the extra terminal letters expose the second-last and third image letters, sending 5 to 0 and 6 to 6.

**Theorem 1.11 (All-index bidirectional occurrence transfer).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; Occ\left(typeI\left(n + 1\right), q\right) \Leftrightarrow \left(\exists a \in \mathbb{N},\; q = occurrenceMap\left(n, a\right) \land Occ\left(typeI\left(n\right), a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordTypeIOccurrence.typeI_occurrence_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occurrence map is B(a) at ordinary phases and B(a)-1 at phase 5. At phase 5 the proved extension sets supply both source contexts required by terminal recognition. No context premise remains in this all-index equivalence.

**Theorem 1.12 (All-index bidirectional consecutive-return transfer).**

$$\forall n \in \mathbb{N},\; \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; Consecutive\left(typeI\left(n + 1\right), occurrenceMap\left(n, a\right), occurrenceMap\left(n, b\right)\right) \Leftrightarrow Consecutive\left(typeI\left(n\right), a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordTypeIOccurrence.typeI_consecutive_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occurrence map is strictly increasing even at the origin, since every image has length at least two. The occurrence equivalence then transfers every consecutive pair, without a restriction on the overlap of its occurrence windows.

**Theorem 1.13 (Parikh transport of every actual return).**

$$\forall n \in \mathbb{N},\; \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; Consecutive\left(typeI\left(n\right), a, b\right) \Rightarrow parikh\left(returnWord\left(occurrenceMap\left(n, a\right), occurrenceMap\left(n, b\right)\right)\right) = mulVec\left(M\left(\right), parikh\left(returnWord\left(a, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordTypeIOccurrence.typeI_return_parikh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an ordinary step the actual interval is phi(R). At phase 5 it is 6 followed by phi(R) with its final 6 deleted. Both therefore have vector M times the vector of R.

**Theorem 1.14 (Realized minimum and universal componentwise bound).**

$$\forall n \in \mathbb{N},\; \left(\exists a \in \mathbb{N},\; \exists b \in \mathbb{N},\; Consecutive\left(typeI\left(n\right), a, b\right) \land parikh\left(returnWord\left(a, b\right)\right) = mulVec\left(matrixPower\left(M\left(\right), n\right), unit\left(6\right)\right)\right) \land \left(\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; Consecutive\left(typeI\left(n\right), a, b\right) \Rightarrow mulVec\left(matrixPower\left(M\left(\right), n\right), unit\left(6\right)\right) \le parikh\left(returnWord\left(a, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordTypeIOccurrence.typeI_return_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transporting the actual adjacent-six base return constructs an actual consecutive return with vector M raised to n times e(6) at every index. Conversely every actual target return decodes to an actual source return. Multiplication by the nonnegative incidence matrix preserves the componentwise inductive lower bound. Both conclusions cover all natural indices and unrestricted occurrence overlaps.

## References

- Truth anchor: `D5/S1/Words/RichWordTypeIOccurrence.actual_fixed_point`
- Truth anchor: `D5/S1/Words/RichWordTypeIOccurrence.base_return_minimum`
- Truth anchor: `D5/S1/Words/RichWordTypeIOccurrence.ordinary_consecutive_iff`
- Truth anchor: `D5/S1/Words/RichWordTypeIOccurrence.ordinary_occurrence_iff`
- Truth anchor: `D5/S1/Words/RichWordTypeIOccurrence.terminal_interval_cancellation`
- Truth anchor: `D5/S1/Words/RichWordTypeIOccurrence.terminal_occurrence_iff`
- Truth anchor: `D5/S1/Words/RichWordTypeIOccurrence.terminal_return_parikh`
- Truth anchor: `D5/S1/Words/RichWordTypeIOccurrence.typeI_consecutive_iff`
- Truth anchor: `D5/S1/Words/RichWordTypeIOccurrence.typeI_extensions`
- Truth anchor: `D5/S1/Words/RichWordTypeIOccurrence.typeI_not_at_origin`
- Truth anchor: `D5/S1/Words/RichWordTypeIOccurrence.typeI_occurrence_iff`
- Truth anchor: `D5/S1/Words/RichWordTypeIOccurrence.typeI_parikh_formula`
- Truth anchor: `D5/S1/Words/RichWordTypeIOccurrence.typeI_return_minimum`
- Truth anchor: `D5/S1/Words/RichWordTypeIOccurrence.typeI_return_parikh`
- Dependency: [D5/S1/Words/MBonacciSentinelDesubstitution](MBonacciSentinelDesubstitution.md)
