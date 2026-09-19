# MFH2025 raw-tuple count: a bounded classical report

This report records a classical proof of the September 2025 side conjecture
associated with the Newman/Erdos #407 discussion.  It is **not** a new
solution of the original Newman question: the current Erdos Problems page
marks that question proved.  It is also not a Lean proof, and it contributes
zero to the project's complete-solution KPI (which remains 0).

The statement counted here is the OEIS A387688 convention.  For a positive
integer N, let R(N) be the number of nonnegative exponent quadruples

    (r,s,t,u) with N = 2^r + 3^s + 2^t 3^u.

The six asserted last occurrences are

    last R=7,8,9,10,11,12 at N=2563,2267,515,299,161,37,

and the finite maximum is R(37)=12.  Equal *sets* of summands are not
identified in this definition; the OEIS entry explicitly warns about that
distinction.

## Sources and status

The source material checked for this report is:

* the #407 discussion: https://www.erdosproblems.com/forum/thread/407#post-347;
* OEIS A387688: https://oeis.org/A387688/internal;
* Prajeet Bajpai and Michael A. Bennett, *Effective S-unit equations beyond
  3 terms: Newman's Conjecture*, arXiv v1:
  https://arxiv.org/html/2308.05162v1.

The final bibliographic metadata is Acta Arith. 214 (2024), 421--458,
DOI 10.4064/aa230725-14-9.  The proof below uses BB Theorems 3, 10 and 11
from the arXiv v1 proof text as classical inputs.  The final journal proof
text was not accessed: the publisher URL returned subscription HTML.  No BB
proof or computation was replayed here, and no Lean formalization of those
theorems is installed.  Thus the result is a classical corollary with an
explicit finite checker, not a kernel-verified theorem or an axiom
declaration.

The bounded source audit was refreshed on 2026-09-19.  Direct fetches covered
the current #407 page, all five ordinary discussion posts, zero dedicated
proof claims, OEIS A387688, and BB arXiv v1.  No full proof of the raw-tuple
side conjecture appears in that inspected discussion.  This is not an
exhaustive claim of worldwide absence.

The source version boundary matters.  In BB v1 an unrestricted sentence
about four representations when min(a,b) >= 2 is false at N=13: exact
enumeration gives R(13)=8 and five BB set-classes.  The tail proof below does
not use that sentence.  It uses only the four displayed Type-I identities,
BB's upper bound, and the separate boundary analysis.  The N=13 clause is
retained here as an explicitly unused false clause, not silently repaired.

## Definitions and the fixed-N adapter

Write a raw tuple as

    x = (2^r, 3^s, 2^t 3^u),

and write C(x) for the *set* of its three values.  BB's omega(N) counts
distinct summand sets across all representations, whereas R(N) counts raw
tuples.  For a fixed N, equality of C does determine the three-term
multiset, which is the needed adapter.

**Fixed-N set-to-multiset lemma.**  If two raw tuples for the same N have
the same set C, their three-term multisets are equal.  If |C| is 3 or 1
this is immediate.  If C={x,y}, x != y, a representation using both values
has multiplicities (2,1) or (1,2), with sums 2x+y and x+2y; the fixed value
N selects at most one.  Consequently, after the multiset is fixed, a raw
tuple is an assignment of one term to the pure-2 role, one to the pure-3
role, and the remaining term to the mixed role.  There are only three
choices for the mixed occurrence; after that choice the other two values
have at most one orientation as pure powers, since a nontrivial power of 2
cannot be a nontrivial power of 3.  Repeated occurrences only identify
choices, so every class has fiber at most 3.  All three choices work exactly
when the multiset is

    [1, 2^i, 3^j],  i,j > 0,

with the three assignments (1,3^j,2^i), (2^i,3^j,1), and
(2^i,1,3^j).  Conversely these are three valid and distinct assignments.
This also covers every distinct/repeated arrangement: without three distinct
values there are fewer than three mixed choices, and without 1 the pure
roles cannot exchange.  Thus repeated-summand classes have fiber at most 2.

This proves the raw/set interface without assuming that summands are
distinct.

## The large-N argument

BB's notation is used as follows.  Type I is

    N = 2^a + 3^b,       a,b >= 0.

Type II is the union of

    N = 2^a + c 3^b,     c in {11,19},
    N = c 2^a + 3^b,     c in {5,7}.

Type III is the union of the following five explicitly listed families:

    N = 2^a + c 3^b,     c in {5,7,13,17,25,35,43,73,97,145,259},
    N = c 2^a + 3^b,     c in {11,13,17,19,25,35,41,73,97,145,259},
    N = 2^a 3^b + c,     b in {1,2}, c in {3,9},
    N = 2^a 3^b + c,     a in {1,2}, c in {2,4},
    N = 2^a 3^b + c,     c in {5,11,17,35,259}.

All exponents here are nonnegative.  The only facts needed below are the
published thresholds and caps:

* BB Theorem 3: omega(N) <= 4 for N >= 131082.
* BB Theorem 10: Type I has omega(N) <= 4 for N >= 131082; Type II has
  omega(N) <= 3 for N >= 532308; and Type III has omega(N) <= 2 for
  N >= 76546076.  The false N=13 Type-I equality sentence is not used.
* BB Theorem 11: the only non-special N with omega(N) >= 3 are

      274, 473, 505, 1109, 1595, 1811, 2297, 2779, 4403, 20761.

For regular Type I (a,b >= 2), put A=2^a and B=3^b.  The four BB identities
give the following underlying three-term multisets (brackets retain repeated
terms):

    [A/2,A/2,B], [A/4,3A/4,B], [A,B/3,2B/3], [A,B/9,8B/9].

The first two share the fixed summand B and have different residual
multisets [A/2,A/2] and [A/4,3A/4].  The last two share A and likewise have
different residual multisets [B/3,2B/3] and [B/9,8B/9].  A cross equality of
summand sets would, by the fixed-N lemma, be an equality of multisets.  It
would have to place B at A in the latter multiset, since all its other terms
are strictly below B; but A != B for a,b >= 2.  Thus the four classes are
distinct, with no separate boundary check.

Their fibers are 1, at most 2 only when a=2, 1, and at most 2 only when b=2,
respectively.  In the second class the extra assignment exchanges the two
pure-3 values 3 and B; in the fourth it exchanges the pure-2 values 8 and A.
Coincident repeated terms only lower these bounds.  Both doublings can occur
only at a=b=2, giving N=13 outside the tail.  BB Theorem 3 makes the four
classes exhaustive there, so R(N) <= 5.

For regular Type II the constraints are a>=1 for c=5, a>=2 for c=7, b>=1
for c=11, and b>=3 for c=19.  In each ordered triple below the entries are
`(pure-2; pure-3; mixed)`; forgetting the order gives the actual BB class:

    c=11: (A;3^(b+2);2 * 3^b),
          (A;3^(b+1);8 * 3^b),
          (A;3^(b-1);32 * 3^(b-1));
    c=19: (A;3^(b+1);16 * 3^b),
          (A;3^b;2 * 3^(b+2)),
          (A;3^(b-3);512 * 3^(b-3));
    c=5:  (2^a;3^b;4 * 2^a),
          (2^(a+1);3^b;3 * 2^a),
          (2^(a-1);3^b;9 * 2^(a-1));
    c=7:  (2^a;3^b;6 * 2^a),
          (4 * 2^a;3^b;3 * 2^a),
          (2^(a-2);3^b;27 * 2^(a-2)).

The c=11 and c=19 triples share the fixed summand A; the c=5 and c=7
triples share B.  After scaling their residual pairs by D=3^(b-1),
3^(b-3), E=2^(a-1), and 2^(a-2), respectively, the coefficient pairs are

    c=11: [6,27], [24,9], [32,1];
    c=19: [432,81], [486,27], [512,1];
    c=5:  [2,8], [4,6], [1,9];
    c=7:  [4,24], [16,12], [1,27].

Within each family these are three different unordered pairs of the same
sum.  If two complete summand sets were equal, the fixed-N lemma would give
equal complete multisets; cancelling one occurrence of the common fixed
summand would force the residual pairs equal.  This proves distinctness even
when the fixed term happens to equal a residual term.

For c=11 the first two fibers are 1, while the third is at most 2, with an
extra assignment possible only when b=1 makes 3^(b-1)=1; hence the total is
at most 4.  The c=19 accounting is the same, with the third doubling possible
only at b=3, again totaling at most 4.  For c=5 the fibers are 2 (the two
pure-2 values can exchange with the mixed role), 1, and at most 2 only at
a=1, totaling at most 5.  For c=7 they are 1, 1, and at most 2 only at a=2,
totaling at most 4.  Repeated terms lower multiplicity.  BB's omega <= 3 cap
makes these three classes exhaustive, so every regular Type-II family has
R(N) <= 5.

It remains to cover the regularity boundary.  A Type-I presentation with no
a,b >= 2 realization lies on the union

    1+3^b,  2+3^b,  2^a+1,  2^a+3.

A Type-II presentation failing its regular constraints lies on

    2^a+11; 2^a+19, 2^a+57, 2^a+171;
    5+3^b; 7+3^b, 14+3^b.

The first and fifth families are already Type III in BB's notation
(2^a 3^0+11 and 2^0 3^b+5), so after the Type-III branch the remaining
boundary rays are

    1+3^b, 2+3^b, 2^a+1, 2^a+3,
    7+3^b, 14+3^b, 2^a+19, 2^a+57, 2^a+171.

This is a union, not a disjoint partition; overlaps therefore cannot leave a
hole.  For N >= 76546076, every 3^b ray has b >= 17 and every 2^a ray has
a >= 27.

The four Type-I boundary rays use Theorem 3's omega <= 4 cap.  Their complete
accounting is:

* `1+3^b` has singleton classes
  {1,3^(b-1),2 * 3^(b-1)} and
  {1,3^(b-2),8 * 3^(b-2)}.  Any size-3 fiber among either of the at most two
  other classes would give 3^b=2^i+3^j with i,j>0, impossible modulo 3.
  Thus all remaining fibers are at most 2 and 1+1+2+2 <= 6.
* `2+3^b` has fiber 2 on the multiset [1,1,3^b], and singleton classes
  {2,3^(b-1),2 * 3^(b-1)} and
  {2,3^(b-2),8 * 3^(b-2)}.  A size-3 remaining fiber would give
  3^b+1=2^i+3^j.  Modulo 3 forces i even; modulo 8 excludes i=2 and every
  even i>=4.  The one remaining class therefore has fiber at most 2, giving
  2+1+1+2 <= 6.
* `2^a+1` has singleton multisets [1,2^(a-1),2^(a-1)] and the singleton
  class {1,2^(a-2),3 * 2^(a-2)}.  A size-3 fiber would give
  2^a=2^i+3^j, impossible by parity.  There are at most two other classes,
  so 1+1+2+2 <= 6.
* `2^a+3` has fibers 1, 1, and 2 on
  [3,2^(a-1),2^(a-1)], {3,2^(a-2),3 * 2^(a-2)}, and {1,2,2^a}.
  A size-3 remaining fiber would give 2^a+2=2^i+3^j, impossible by parity.
  The one remaining class has fiber at most 2, so 1+1+2+2 <= 6.

The five remaining rays use the stronger Type-II omega <= 3 cap:

* `7+3^b`: {1,6,3^b} has fiber 1 and {3,4,3^b} has fiber 2; the one
  remaining class has fiber at most 3, so R <= 1+2+3=6.
* `14+3^b`: {2,12,3^b} and {6,8,3^b} are singleton; the one remaining
  class has fiber at most 3, so R <= 1+1+3=5.
* `2^a+19`: {3,16,2^a} has fiber 2 and {1,18,2^a} has fiber 1; the one
  remaining class has fiber at most 3, so R <= 2+1+3=6.
* `2^a+57`: {9,48,2^a} and {3,54,2^a} are singleton; the one remaining
  class has fiber at most 3, so R <= 1+1+3=5.
* `2^a+171`: {27,144,2^a} and {9,162,2^a} are singleton; the one remaining
  class has fiber at most 3, so R <= 1+1+3=5.

The fixed-N lemma and the displayed unequal residual pairs show the forced
classes on each ray are distinct.  The exponent lower bounds make the stated
fiber counts immediate from which entries are pure or mixed.

Finally, a Type-III N has R(N) <= 3 omega(N) <= 6.  If N is non-special,
Theorem 11 says omega(N) >= 3 only at its ten listed exceptions, all below
the cutoff; hence a non-special N in the tail has omega(N) <= 2 and again
R(N) <= 6.  Thus every N >= 76546076 is covered by the Type-III,
non-special, regular Type-I, regular Type-II, or nine-ray branch, and every
branch has R(N) <= 6.

## Exact finite prefix

The accompanying `verify.py` uses integer loops, not floating logarithms.
Since 2^27 and 3^17 exceed B=76546075, every accepted tuple has

    0 <= r,t <= 26 and 0 <= s,u <= 16.

It enumerates all 27*17*27*17 = 210681 candidate tuples, retains those with
N <= B, and independently computes the same multiset by convolving the 459
pure sums 2^r+3^s with the 459 mixed terms 2^t3^u.  Counters are compared
entry-for-entry; duplicate pure sums are retained (5 has 2+3 and 4+1).
For each (N,C), the checker stores the first sorted three-term multiset and
compares every later tuple in that class against it.  It also checks both
directions of the fiber-3 characterization in the enumerated domain,
including that the two non-1 terms are a nontrivial power of 2 and a
nontrivial power of 3.  These are finite checks of the adapter and fiber
lemma, not proofs of their general statements.  The checker also checks all
57 supplied anchor tuples and the following summary:

    accepted raw tuples: 106750       represented N: 82943
    sum N*R(N): 1545759402665        sum R(N)^2: 173506
    histogram R=1..12:
      65019, 14228, 2283, 1026, 193, 93, 46, 31, 15, 6, 2, 1
    last occurrences: 7:2563, 8:2267, 9:515, 10:299, 11:161, 12:37.

It checks the class-fiber histogram 1:88197, 2:8657, 3:413, maximum 3 at
N=6 with terms {1,2,3}.  `--negative-control` intentionally deduplicates
the pure-sum list before convolution.  That changes the actual counting
semantics and must exit nonzero; changing an expected scalar alone is not a
meaningful test.

The finite computation proves the six prefix last-occurrence assertions and
absence of R>12 through B.  The BB tail proves R<=6 above B.  Together they
prove for every positive N that R(N)<=12 and that the largest occurrence
indices for R=7,8,9,10,11,12 are, respectively,
2563,2267,515,299,161,37.  This is a classical result conditional on the
cited BB theorems as published mathematics.  It does not close the project's
Lean dependency gap, solve a new original #407 problem, increment KPI 0, or
alter the full goal.

## Reproducibility and boundaries

The checker requires Python >=3.9 and only the standard library.  It was run
with Python 3.9.6 on Darwin 25.6 arm64, including from another working
directory, from a space-containing temporary copy, and under a clean
environment.  The intended entry point is portable from any working
directory:

    python3 /path/to/trureturing/docs/reports/erdos407-raw-count/verify.py
    python3 /path/to/trureturing/docs/reports/erdos407-raw-count/verify.py --negative-control

The second command is expected to fail with a nonzero exit.  No independent
delivery review, CI result, PR, or merge is claimed by this report.  The
underlying BB proof remains a cited classical dependency.
