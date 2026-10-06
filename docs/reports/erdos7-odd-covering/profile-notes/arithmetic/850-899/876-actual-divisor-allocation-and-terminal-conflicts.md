[Index](../../../marked_head_profile.md) · [Rooted obstructions](875-semiprime-obstructions-and-repairs-without-the-pure-label.md) · [Paid banks](872-matched-prefix-completion-and-paid-banks.md#shared-outputs-require-one-common-divisor-assignment) · [Whole-source capture](874-matched-prime-families-and-whole-source-capture.md#capturing-actual-traces-controls-the-simultaneous-deletion-hole)

# Actual divisor allocation and terminal conflicts

A common-root family of actual top originals with four matching
primes per owner admits three distinct two-prime divisors per owner,
with no numerical divisor reused anywhere in that family. Their CRT
outputs cover the entire union of the selected q-stripped classes.
This allocation reuses the existing finite-degree matching theorem;
the donor multiplicity is supplied by the actual prime-cut capacity.

For a fixed partial repair, a point at which no further three-divisor
step is possible satisfies an occupied-divisor incidence inequality.
This is an obstruction to further augmentation, not a proof that
augmentation covers the entire source. Count payment for a local
packet, lower-row service and globally compatible output phases are
separate obligations.

## A divisor with two prime factors serves at most two coherent owners

Let F be an actual odd distinct covering system, minimal first in
class count and then in modulus sum. Fix a natural number h and an
integer q at least seven. Assume no original modulus is divisible by
3^(h+1). Select distinct actual originals indexed by a finite set I,
with moduli

$$
n_i=3^h q m_i.
\tag{DA1}
$$

Their residues a_i have one common old word z modulo 3^h. Fix one
auxiliary root phi_p modulo every prime under consideration. A prime
matches owner i when it divides m_i and a_i is congruent to phi_p
modulo p. The cofactor m_i is positive, odd and coprime to three,
as follows from DA1 and the assumptions on F.

Suppose a numerical divisor d is eligible for an owner only when
d divides m_i and all primes dividing d match that owner. If d has
two distinct prime factors p and t, apply the actual prime-cut
capacity with constant left tag p and constant right tag t. The
two tag images are contained in the disjoint singleton sets {p}
and {t}. Therefore

$$
\#\{i:d\text{ is eligible for }i\}\le2.
\tag{DA2}
$$

All owners in this count share z and the same auxiliary roots.
They need not have the same q-color. The statement does not bound
the number of owners that can use d across different old words or
incompatible roots. No primality or height-one condition on q, nor
a bound of 27 primes, is needed for DA2.

## Four matching primes supply a simultaneous allocation

For each owner choose four distinct matching primes. The six
unordered pair products are distinct numerical divisors of m_i.
Distinctness follows from unique prime factorization; divisibility
uses coprimality of the two different primes. Call this six-element
bank C_i.

Every donor belongs to at most two banks by DA2. Replace each owner
by three copies with the same bank. Each copy has six candidates,
and each donor is incident with at most six copies. Directly applying
the existing finite-degree matching theorem gives an injection

$$
d:I\times\{0,1,2\}\longrightarrow\bigcup_i C_i,
\qquad d(i,c)\in C_i.
\tag{DA3}
$$

The reused declaration is
`NikolovSegal.finite_degree_matching` in
`D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lean`.
This is its degree-six instance, not a new Hall theorem. In
particular the six-donor stock and the multiplicity bound have been
derived from the selected actual originals rather than assumed as
an abstract allocation oracle.

## Fixed CRT outputs repair the full selected packet union

For each (i,c), use the modulus 3^(h+1)d(i,c), with residue specified
by

$$
x\equiv z+3^h c\pmod{3^{h+1}},
\qquad x\equiv a_i\pmod{d(i,c)}.
\tag{DA4}
$$

Reduce z modulo 3^h in this expression. CRT applies because the
donor is coprime to three. All output labels are distinct by DA3.
They are odd nonunits and are fresh against every original: each
is divisible by 3^(h+1), whereas no original is.

Every integer in an actual q-stripped class

$$
[a_i]_{n_i/q}=[a_i]_{3^h m_i}
$$

has exactly one next ternary digit c. Its congruence modulo m_i
implies the required congruence modulo d(i,c), so the corresponding
output contains it. One fixed assignment DA4 therefore covers the
entire union of these classes, not only a common witness point.

Put k=|I| and M=sum_i m_i. The construction has

$$
B=3k,\qquad
\sum_{i,c}3^{h+1}d(i,c)\le9\cdot3^h M.
\tag{DA5}
$$

For q=113 and k positive, this sum is strictly smaller than the
selected old sum 113*3^h*M. Deleting only those k originals and
adding 3k outputs increases the class count by 2k, so DA5 alone
does not contradict count-first minimality. A larger simultaneous
capture set, or a fully covered all-q deletion, is needed.

In the height-two branch with at most 27 cofactor primes,
Report864 PC61 already gives k at most 30 for four matching primes.
Thus B is at most 90. This numeric bound retains those additional
branch conditions; DA2--DA5 do not establish them for arbitrary F.

## Monotone augmentation keeps one source and one phase assignment

For the following global bookkeeping, retain the conditional branch
of Reports870--875: h=2, q=113 of height one, common period 9qW,
and W coprime to 3q. Let D be all q-bearing originals, retain all
q-free originals, and let E0 be their exact residual on 9W.
The fixed repair target on 27W is

$$
\widehat E_0=\{x\bmod27W:x\bmod9W\in E_0\}.
\tag{DA6}
$$

Use the actual divisor banks of the earlier reports. P2 consists
of cofactors m whose actual top label 9qm is present; P0 consists
of cofactors m whose row-zero label qm is present. Their divisor
closure and P2 contained in P0 belong to the stated branch.

Report872 MC11 already pays the count and modulus sum of any
family using each label in 27P0 at most once. Its cardinality is
at most |P0|, at most |D|; its sum is at most 27 sum(P0), strictly
less than 113 sum(P0), at most the deleted sum when P0 is nonempty.
Thus the same payment applies to its subbank 27P2. Payment does
not supply residues covering DA6.

This budget also has a direct actual-source Lean check. Define P0
as the image n_i/113 of the actual originals with 113 dividing n_i
and three not dividing n_i. Numerical distinctness gives exactly
one original 113d for each d in P0 and the exact identity
113 sum(P0)=sum(row-zero moduli). If any original is divisible by
113, sum-minimality and the existing prime-label theorem supply
the original label 113, so P0 contains one and is nonempty.
The count and strict sum bounds for every subset B of P0 follow.
Freshness uses no original divisible by 27. This budget check
needs no period or divisor-closure assumption; those remain needed
when asserting that particular donor divisors lie in P0. The bank
includes the pure label 27, available only once with one residue.

Let a partial repair using distinct labels 27d with d in P0 be
fixed, with occupied cofactor set Focc.
Keep every existing output residue unchanged. At an uncovered
point x, take an actual top owner i whose q-stripped class contains
x. Define

$$
C_i=\{d:d\mid m_i,\ \omega(d)\ge2\}.
\tag{DA7}
$$

If C_i contains three unused numerical divisors, choose them and
give them the three residues in DA4. They need not be pair products
for this single-owner step. The three new outputs cover that entire
q-stripped class, remain in 27P2, and preserve every point already
covered. The fixed retained family and target DA6 do not change.

Each step consumes three previously unused members of a finite
bank, so the procedure stops. This establishes finite termination,
not absence of uncovered points at termination. Different choices
can occupy a useful divisor with incompatible phases.

There is a useful initial case with no occupied two-prime cofactors.
The three-matching-prime repair of Report875 uses only prime
cofactors and anchors with at least three distinct prime factors.
It therefore leaves every two-prime cofactor unused. Any additional
top owner with at least three distinct prime factors supplies the
three pair products of a chosen triple. They are distinct and unused,
so one can append the three outputs covering its full q-stripped
class. No common auxiliary root with the earlier owners is required:
all three new phases come from this one owner's literal residue.

The single-owner conclusion has an exact Lean check assuming only
an actual F, q positive, its label 3^h*q*m, no original divisible
by 3^(h+1), at least three distinct prime factors of m, and no
occupied cofactor with exactly two distinct prime factors. It does
not require minimality or q at least seven. After this step the
two-prime bank is no longer empty, so the same initial condition
cannot be reused without a new unused-label check.

## A necessary law at any terminal uncovered point

At a fixed residual point x let I_x be all actual top owners whose
q-stripped classes contain x, and use their full banks DA7. Every
prime of every such m_i matches the actual root x modulo p. All
these owners have old word x modulo 3^h. Consequently DA2 applies
simultaneously to their donor incidences, with no extra incidence
premise.

If no three-divisor augmentation is available, then
|C_i minus Focc| is at most two for each i. At least
(|C_i|-2)_+ of its donors are occupied. Summing and applying DA2
to the occupied union gives

$$
\boxed{
\sum_{i\in I_x}(|C_i|-2)_+
\le2\left|F_{\rm occ}\cap\bigcup_{i\in I_x}C_i\right|.
}
\tag{DA8}
$$

Here positive part agrees with truncated natural subtraction.
The proof directly reuses finite-set decomposition and Mathlib's
`Finset.sum_card_eq_sum_biUnion_card`. The actual-source form
derives DA2 by the singleton prime cut from the common point x.
It applies at arbitrary h and q at least seven under DA1's
minimality and no-higher-ternary-layer conditions.

Focc is one fixed numerical bank, not a new choice at each x.
Because x is uncovered, every occupied donor counted on the
right has an output whose old word, next digit or cofactor phase
fails at x. Changing that output to serve x can uncover points
previously served by it. DA8 provides no such reassignment.

## Verification and the remaining global obligation

Scoped exact Lean checks cover the actual two-prime incidence
bound, six distinct pair-product donors from four matching primes,
the finite-degree matching application, and the full DA1--DA5
packet repair including distinctness, freshness, complete stripped
class coverage, count and modulus sum. A separate exact check
covers DA8 with the donor banks defined from the actual cofactors
and their common source point. All checks use only the standard
three axioms and default proof budgets.

These are applications of existing arithmetic, finite matching,
CRT and double-counting results. Their exact checks are transient;
no new canonical theorem is introduced merely to name those
applications. The numeric k<=30 supplier remains the earlier
PC61 result, and the global bank budget remains MC11. Neither
is counted as new mathematical content here.

The source-covering family from Report875 does not force a
three-divisor step at every uncovered point. Its serving owner
can lie in a lower row, or have too few unused donors. Lower-row
owners require their entire residual trace across the compatible
old words, not only the slice through x. Nor is DA2 a global bound
across different words and roots.

For the direct whole-child certificate MC11, a lower owner with e
required safe old words needs at least 3e different serving numerical
donors. Each donor has only one assigned old word and child, while
every pair (required word,child) must be represented. The finite
image-cardinality implication has an exact Lean check. This is a
necessary condition for that certificate, not for every possible
repair of a masked source: more refined partitions can fall outside
the whole-child scheme. The earlier five-word and three-word upper
bounds for rows zero and one do not reduce their obligation to
three donors per owner.

What remains is an actual-source theorem producing one common
output assignment that covers DA6, or an augmentation/reassignment
theorem that preserves existing service and cannot stop short of
that target, including lower rows. The finite allocation and
terminal inequality do not provide that theorem. This conditional
branch and unrestricted Erdos7 both remain unresolved.
