# Actual objects for the A398542 fixed-bottom conjecture

## Abstract

Actual fixed-bottom permutations and their exact gap configurations.

The source is OEIS A398542, revision 18, August 30, 2026. Perm(n) means bijections of Fin(n), with zero-based values; adding one recovers the source alphabet 1,...,n. Contains is the existing generic classical containment predicate. All sizes in the semantic constructions are natural numbers, including zero. The eventual polynomial theorem requires m>=1. The new Library note records the exact source formula and the bounded literature comparison.

**Definition 1.1 (The literal pattern 132).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.pattern132`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.pattern132` (`✓ std3`).

*Citation.* Charles Cornell Norton (2026). *OEIS A398542: fixed-bottom polynomial conjecture*. URL: <https://oeis.org/A398542>.

*Commentary.*

The permutation of Fin(3) with values [0,2,1]. This is the source's 132 pattern after subtracting one from every value.

**Definition 1.2 (The literal pattern 213).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.pattern213`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.pattern213` (`✓ std3`).

*Citation.* Charles Cornell Norton (2026). *OEIS A398542: fixed-bottom polynomial conjecture*. URL: <https://oeis.org/A398542>.

*Commentary.*

The permutation of Fin(3) with values [1,0,2], representing the source's upper-cell forbidden pattern 213.

**Definition 1.3 (The literal pattern 1324).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.pattern1324`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.pattern1324` (`✓ std3`).

*Citation.* Charles Cornell Norton (2026). *OEIS A398542: fixed-bottom polynomial conjecture*. URL: <https://oeis.org/A398542>.

*Commentary.*

The permutation of Fin(4) with values [0,2,1,3], representing the forbidden pattern in the complete source permutation.

**Definition 1.4 (The literal lower-value word).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.lowerWord`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.lowerWord` (`✓ std3`).

*Citation.* Charles Cornell Norton (2026). *OEIS A398542: fixed-bottom polynomial conjecture*. URL: <https://oeis.org/A398542>.

*Commentary.*

For every m,k and w in Perm(m+k), read the values of w in increasing position order and retain exactly those less than m. The result is a list of natural numbers; it retains actual values, not just ranks.

**Definition 1.5 (The standardized upper-value word).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.upperWord`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.upperWord` (`✓ std3`).

*Citation.* Charles Cornell Norton (2026). *OEIS A398542: fixed-bottom polynomial conjecture*. URL: <https://oeis.org/A398542>.

*Commentary.*

For every m,k and w in Perm(m+k), read w in position order, retain exactly the values at least m, and subtract m from each retained value. This is a list over 0,...,k-1.

**Definition 1.6 (Values on lower positions).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.lowerValues`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.lowerValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For w in Perm(m+k), lowerValues is an equivalence from positions i satisfying w(i)<m to Fin(m). Its forward map is w(i), and its inverse is the position w inverse at the same lower value.

**Definition 1.7 (Values on upper positions).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.upperValues`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.upperValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For w in Perm(m+k), upperValues is an equivalence from positions i satisfying not w(i)<m to Fin(k). It sends i to w(i)-m; its inverse sends j to the position of value m+j.

**Definition 1.8 (Increasing lower-position enumeration).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.lowerOrder`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.lowerOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every w in Perm(m+k), lowerOrder is the increasing order isomorphism from Fin(m) to the subtype of positions with values below m. The cardinality equality is supplied by lowerValues.

**Definition 1.9 (Increasing upper-position enumeration).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.upperOrder`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.upperOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every w in Perm(m+k), upperOrder is the increasing order isomorphism from Fin(k) to positions with values at least m, using upperValues for their cardinality.

**Definition 1.10 (The actual lower permutation).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.lowerPerm`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.lowerPerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every w in Perm(m+k), compose lowerOrder with lowerValues to obtain a permutation of Fin(m). Its values are precisely lowerWord(w) in position order.

**Definition 1.11 (The actual standardized upper permutation).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.upperPerm`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.upperPerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every w in Perm(m+k), compose upperOrder with upperValues to obtain a permutation of Fin(k). It reads the upper cell in position order and subtracts the fixed value cut m.

**Definition 1.12 (An ordered interleaving).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.Shuffle`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.Shuffle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all m,k, Shuffle(m,k) consists of an equivalence from the disjoint sum Fin(m) plus Fin(k) to Fin(m+k), strictly increasing on each summand separately. Both summands may be empty.

**Definition 1.13 (Extract the two ordered position sets).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.extractShuffle`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.extractShuffle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every w in Perm(m+k), extractShuffle(w) combines lowerOrder and upperOrder into the common position set, retaining the order within each cell.

**Definition 1.14 (Insert the two actual value blocks).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.insert`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.insert` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For b in Perm(m), u in Perm(k), and s in Shuffle(m,k), insert(b,u,s) is the permutation whose value at s(lower i) is b(i), and whose value at s(upper j) is m+u(j). The shuffle determines positions only.

**Definition 1.15 (Mutually inverse insertion and extraction).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.insertionEquiv`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.insertionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every m,k, insertionEquiv is an equivalence from (Perm(m) times Perm(k)) times Shuffle(m,k) to Perm(m+k). The forward map inserts both cells; the inverse returns lowerPerm, upperPerm and extractShuffle. Both composites are identities, including empty cells. The increasing lower and upper enumerations recover the original positions and actual values.

**Definition 1.16 (The number of preceding lower positions).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.gap`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.gap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For s in Shuffle(m,k) and upper index j in Fin(k), gap(s,j) in Fin(m+1) is the cardinality of lower indices i with s(lower i)<s(upper j).

**Theorem 1.17 (Exact gap order and position recovery).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.gap_spec`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/A398542FixedBottom.gap_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m,k and s in Shuffle(m,k), gap(s) is weakly increasing; for all lower i and upper j, s(lower i)<s(upper j) if and only if i<gap(s,j); and for every upper j, the natural position s(upper j) equals gap(s,j)+j. Equal consecutive gaps are permitted. The proof identifies each lower prefix by its finite cardinality.

**Definition 1.18 (Reconstruct an ordered shuffle).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.shuffleOfGaps`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.shuffleOfGaps` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every weakly increasing g:Fin(k)->Fin(m+1), shuffleOfGaps(g) constructs a Shuffle(m,k). Its upper positions are g(j)+j; its lower positions fill the complement in increasing order.

**Definition 1.19 (Shuffles are exactly weakly increasing gaps).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.gapEquiv`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.gapEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all natural m,k, gapEquiv is an equivalence between Shuffle(m,k) and the subtype of weakly increasing functions Fin(k)->Fin(m+1). It uses gap and shuffleOfGaps, with both inverse laws.

**Definition 1.20 (A total prefix minimum).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.prefixMin`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.prefixMin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every b in Perm(m) and natural g, prefixMin(b,g) is the minimum of {m} together with all b(i) for i in Fin(m) satisfying i<g. In particular the empty prefix has value m.

**Definition 1.21 (The first forbidden later endpoint).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.dead`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.dead` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every b in Perm(m) and natural g, dead(b,g) is the minimum of {m+2} together with all j+1 for j in Fin(m) satisfying g<=j and prefixMin(b,g)<b(j). The endpoint uses the source's one-based bottom convention; m+2 is the sentinel when no endpoint exists.

**Theorem 1.22 (The exact mixed-pattern obstruction).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.contains1324_iff_mixed`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/A398542FixedBottom.contains1324_iff_mixed` (`✓ std3`). ∎

*Citation.* Charles Cornell Norton (2026). *OEIS A398542: fixed-bottom polynomial conjecture*. URL: <https://oeis.org/A398542>.

*Commentary.*

For every w in Perm(m+k), assume lowerPerm(w) avoids 132 and upperPerm(w) avoids 213. Then w contains 1324 if and only if there are positions a<x<c<y with w(a),w(c)<m, m<=w(x),w(y), w(a)<w(c), and w(x)<w(y). Every other distribution of a forbidden occurrence between the cells would contain one of the excluded cell patterns. The interleaved-ascent criterion is an existing ingredient in the domino literature cited by the source audit.

**Theorem 1.23 (A strict deadline for every upper ascent).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.gap_criterion`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/A398542FixedBottom.gap_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same two avoidance assumptions on w, let b=lowerPerm(w), u=upperPerm(w) and g=gap(extractShuffle(w)). Then dead(b,0)=m+2; for every natural t<=m, t<dead(b,t); and w avoids 1324 if and only if every pair i<j in Fin(k) with u(i)<u(j) satisfies g(j)<dead(b,g(i)). The strict cutoff is essential. The proof relates a lower ascent across a gap interval to its first later endpoint. It asserts no monotonicity of dead.

**Definition 1.24 (The literal source class).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.Actual`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.Actual` (`✓ std3`).

*Citation.* Charles Cornell Norton (2026). *OEIS A398542: fixed-bottom polynomial conjecture*. URL: <https://oeis.org/A398542>.

*Commentary.*

For every b in Perm(m) and k in N, Actual(b,k) is the subtype of w in Perm(m+k) such that lowerWord(w) is exactly the position-ordered list of b's values, w avoids 1324, and upperPerm(w) avoids 213. This is the original fixed value-cut class of actual permutations.

**Definition 1.25 (The equivalent gap data).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.Configuration`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.Configuration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For b in Perm(m) and k in N, a configuration consists of u in Perm(k) and weakly increasing g:Fin(k)->Fin(m+1), with u avoiding 213 and g(j)<dead(b,g(i)) for every i<j with u(i)<u(j). The bottom remains the whole fixed b.

**Definition 1.26 (Equivalence with the actual source permutations).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.actualEquiv`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.actualEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every m, b in Perm(m) avoiding 132, and k in N, actualEquiv(b,k) is an equivalence Actual(b,k) equivalent to Configuration(b,k). It combines the insertion and gap equivalences with the strict mixed-pattern criterion. The proof identifies lowerWord with the values of lowerPerm and upperWord with those of upperPerm, so equality of the bottom is literal list equality. Both composites are identities, including k=0.

**Definition 1.27 (Cardinality of actual permutations).**

Lean statement: `D5/S1/Words/Patterns/A398542FixedBottom.count`

*Formalization.* `D5/S1/Words/Patterns/A398542FixedBottom.count` (`✓ std3`).

*Citation.* Charles Cornell Norton (2026). *OEIS A398542: fixed-bottom polynomial conjecture*. URL: <https://oeis.org/A398542>.

*Commentary.*

For every b in Perm(m) and k in N, count(b,k)=Nat.card(Actual(b,k)). This is d(b,k) in the source. No recurrence is assumed in this definition; the next module proves the actual cardinal recurrence.

## References

- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.Actual`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.Configuration`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.Shuffle`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.actualEquiv`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.contains1324_iff_mixed`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.count`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.dead`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.extractShuffle`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.gap`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.gapEquiv`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.gap_criterion`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.gap_spec`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.insert`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.insertionEquiv`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.lowerOrder`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.lowerPerm`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.lowerValues`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.lowerWord`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.pattern132`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.pattern1324`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.pattern213`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.prefixMin`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.shuffleOfGaps`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.upperOrder`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.upperPerm`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.upperValues`
- Truth anchor: `D5/S1/Words/Patterns/A398542FixedBottom.upperWord`
- Dependency: [D5/S1/Words/Patterns/DerangementRatioNonconvergence](DerangementRatioNonconvergence.md)
