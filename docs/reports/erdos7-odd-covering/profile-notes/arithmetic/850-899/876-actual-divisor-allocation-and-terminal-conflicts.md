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

## A common literal phase bounds incidence across every row

There is an actual-source capacity bound that does not fix an old
word or ternary row. Let F be count-then-sum minimal, let q be at
least 28, and assume no original modulus is divisible by 27.
Retain actual originals of moduli 3 and 9 whose residue classes
are disjoint. Let d be positive, odd and coprime to three, with
at least fifteen distinct divisors. Select distinct originals with
q*d dividing each modulus and one common literal residue beta
modulo d. Then

$$
\#\{\text{selected originals}\}\le14.
\tag{DA9}
$$

Indeed, if fifteen such originals existed, delete exactly those
fifteen and retain every other original. The retained 3/9 guards
leave five safe words modulo nine, hence fifteen safe roots modulo
27. Assign a different divisor t of d to each safe root v, using
the CRT output x congruent to v modulo 27 and to beta modulo t.
Every point in the simultaneous deletion hole avoids the retained
guards and is congruent to beta modulo d, so one of these fifteen
outputs contains it. Their moduli 27t are distinct, odd nonunits
and fresh. Their sum is at most 405d, whereas the deleted sum is
at least 15qd, strictly larger for q at least 28. This contradicts
sum minimality at the same class count.

The selected originals cannot be the retained guards: q*d at least
28 divides their moduli. The proof needs neither a q-height-one
condition nor divisor closure of an inventory. Divisor closure is
still needed when these divisors are later claimed to belong to
the paid bank P0. The pure label 27 is legal in this proof-only
replacement; this argument reserves no label for a later repair.

In particular, fix four distinct primes different from three and
one phase at each. Among actual originals labelled
3^(a_i)*q*m_i, at most fourteen can have all four primes dividing
m_i and matching all four phases. Their product d has sixteen
distinct subset-product divisors. The common phase modulo d is
derived by CRT from one actual owner's residue; it is not a
separately chosen joint realization. Choose fifteen of those
divisors and apply DA9. Both DA9 and this four-prime supplier have
exact Lean checks with standard axioms. They count every row,
old word and q-color together.

For comparison, a one-word lower-row exchange has a smaller bound.
If the selected moduli are divisible by 3*q*d, share one word
modulo three and one phase modulo d, and d has eight distinct
divisors, then their number is at most ten for q at least fourteen.
Eight outputs of the form 27t cover eight of the nine extensions
of that word; three outputs 81t cover the last extension. Numerical
labels are distinct within and across heights, and all are fresh
under no27. Their sum is at most 459d, below the sum of eleven
deleted originals, at least 33qd. This bound also has an exact
actual-source Lean check. It does not replace the across-all-rows
bound DA9.

## Ten matching primes supply fifteen globally distinct donors

Under DA9's actual-cover and guard assumptions, suppose every
selected owner has at least ten distinct primes different from
three matching one fixed phase table. Choose ten such primes per
owner and take all products of four of them. Unique factorization
gives exactly 210 different numerical donors in each bank. Each
donor belongs to at most fourteen owner banks by the checked
four-prime incidence bound.

Replace each owner by fifteen copies. Every copy still has 210
candidates, and each donor is incident with at most 14*15=210
copies. Applying `NikolovSegal.finite_degree_matching` gives one
injection from I times Fin15 into the numerical donors, with each
chosen donor dividing its owner's cofactor and retaining four
matching prime factors. This entire actual-source application has
a scoped Lean check with standard axioms, including its stock
and global incidence suppliers. It needs no common old word,
q-color, q-height-one or bound on the total prime pool.

These donors give a complete fixed CRT repair of the selected safe
stripped traces. Number the fifteen roots modulo 27 that avoid both
retained guards. For each owner assign its fifteen donors to these
roots. On donor d assigned to root v use the output

$$
x\equiv v\pmod{27},\qquad x\equiv a_i\pmod d.
\tag{DA12}
$$

The product donor is coprime to three, so CRT applies. All 15|I|
numerical labels 27d are distinct, odd nonunits and fresh. Any point
in one selected q-stripped class that avoids the two guards has a
safe root v; the donor assigned to v divides that owner's cofactor,
so its fixed output contains the point. This covers the entire safe
trace, including every relevant old word of a lower-row owner.

Each four-prime donor omits at least six matching primes from its
owner. Oddness and exclusion of three put each omitted prime at
least five. Consequently

$$
5^6d(i,c)\le m_i,\qquad
5^6\sum_{i,c}27d(i,c)\le405\sum_i m_i.
\tag{DA13}
$$

The allocation, full CRT coverage, freshness and these bounds have
one complete actual-source Lean check. The selected family need
not share an old word or q-color.

Every nonunit divisor of an original modulus is itself an original
modulus. This follows from the stated minimality: an
absent divisor could replace its original class, preserving the
cover and numerical distinctness while strictly decreasing the
modulus sum. An exact singleton application of the existing finite
replacement theorem checks this closure. For q=113, since 113d
divides its owner's label, it supplies an actual row-zero original
of modulus 113d. Thus the donor image is
contained in the actual P0 bank. The checked all-q budget above
pays both its output count and its strictly smaller modulus sum.
Coverage of the residual is not inferred from the matching theorem.

This yields a necessary source restriction. Let E be the actual
complement of all q-free originals, and assume some original is
divisible by 113. Under the same guards, no27 and minimality,
the safe q-stripped traces of a fixed
ten-match sector cannot cover E. If they did, retaining every
q-free original and adding DA12 would give a legal cheaper cover
with no larger count. This implication has an exact Lean check
using the literal source predicate

$$
E(x)\iff
\forall j\ (113\nmid n_j\Longrightarrow x\not\equiv a_j\pmod{n_j}).
\tag{DA14}
$$

No independently prescribed mask or common-period premise enters
this noncoverage result. It restricts a hypothetical minimal cover
in the stated branch; it does not eliminate every possible cover.

## Published polychromatic coloring supplies a conditional route

Theorem 3 of Erdos and Lovasz, *Problems and results on 3-chromatic
hypergraphs and some related questions*, Infinite and Finite Sets II,
609--627, states that an r-uniform hypergraph admits a k-coloring
with every color on every edge when each edge meets at most
k^(r-1)/(4*(k-1)^r) other edges. Neither linearity nor a simple
intersection condition is required. Its proof applies the local
lemma to the event that an edge misses some color. The original
statement and proof are available in the
[author's paper archive](https://users.renyi.hu/~p_erdos/1975-34.pdf).

Under the same actual-cover and guard assumptions, fix one root
table and choose eight matching primes per actual owner. Use as
its candidate numerical donors all products of four
through seven of these primes. Each bank has

$$
\binom84+\binom85+\binom86+\binom87=162
\tag{DA10}
$$

members. If another bank meets it, the shared product contains a
four-prime subset of the first owner's eight primes. For each of
the seventy such subsets, the actual four-prime bound allows at
most thirteen other owners. Thus the edge-intersection degree is
at most 910. The exact integer inequality

$$
4\cdot15\cdot910\cdot14^{162}<15^{162}
\tag{DA11}
$$

meets the published criterion for fifteen colors. Interpret a color
as one of five safe old words and three child digits. Each numerical
donor receives one color and the cofactor phase prescribed by the
same root table. Each owner's entire safe stripped trace then has
a containing output at every required word and child. Selecting
one witness per required color per owner and coalescing shared
outputs uses at most fifteen times the number of owners. A proper
subset product omits a prime of size at least five, so the output
sum is at most 81*sum_i m_i. The global all-q deletion budget applies
when the used donors lie in P0; deleting just the selected owners
does not in general pay that output count.

The actual incidence supplier and the finite uniform-coloring
application have exact Lean checks. The latter constructs the
uniform law on colorings, proves independence from every collection
of nonneighbor events by splitting disjoint coordinate sets, and
bounds the missing-color probability by a union bound. It directly
applies an existing finite symmetric local-lemma formalization in the pinned
[atlas-lean source](https://github.com/facebookresearch/atlas-lean/blob/0b121a198307b6153181f5a1d9145dcda2f7bfee/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean),
using its exp(1)*p*(D+1) criterion. The exact fifteen-color,
162-candidate, degree-910 instance also compiles, using exp(1)<3
and rational arithmetic. The general adapter allows indexed finite
banks of size at least the threshold; equal bank sizes and linearity
are not required. A combined actual-source check supplies the
eight-prime banks, proves their 162-member stock and degree-910
bound, and produces one coloring of numerical divisors. Every
selected owner has a matching divisor of each of the fifteen
colors. No new proof of the local lemma is claimed.

The full eight-match repair and paid noncoverage implication also
have one complete actual-source Lean check. Choose one witness
donor for each owner and color, then take their numerical image B.
For each d in B choose one actual owner furnishing it. If another
owner furnishes the same d, unique prime factorization identifies
its prime support. Both literal residues match the same phase table
on that support, so they agree modulo d. Thus one CRT output per
numerical donor uses its single assigned safe root and serves every
owner that selected it. There is no overwrite of an earlier phase.

The coalesced bank has |B| at most 15|I|. Every witness donor uses
at most seven of an owner's at least eight matching primes, so
5d is at most that owner's cofactor. Summing over witness slots,
then bounding the image sum by the slot sum, gives

$$
\sum_{d\in B}27d\le81\sum_i m_i.
\tag{DA15}
$$

The fixed family covers the entire selected safe stripped union,
including lower rows. The paid noncoverage implication holds for
every q at least 28. It only needs count-then-sum minimality, no
original modulus divisible by 27, some original divisible by nine,
and some original divisible by q. No primality or height-one
condition on q, common period, prime-pool cap, explicit divisor
closure or separately supplied guard disjointness is required.

Minimality supplies actual moduli three and nine by the singleton
replacement argument. Their classes are disjoint: if the nine-class
were contained in the three-class, deleting the former would lower
the count. For every used numerical donor d, minimality likewise
supplies the actual label q*d. Distinct d give distinct actual
q-bearing originals, even when q is composite. Let D be all the
actual q-bearing originals. Then the exact bank payment is

$$
|B|\le|D|,\qquad
27\sum_{d\in B}d<\sum_{j\in D}n_j.
\tag{DA16}
$$

If B is nonempty, use q at least 28 and the injection of q*d labels
into D. If B is empty, the nonempty D and positivity of all original
moduli give the strict inequality. This counts actual labels rather
than assuming that numerical divisors have been stocked. In the
q=113 height-one branch it specializes to the P0 budget.

There is a direct actual-source formulation without a preselected
owner family. For one fixed phase function phi and each q-bearing
original i, put

$$
R_i(\phi)=\{p:p\text{ prime},\ p\ne3,\ p\mid n_i/q,
\ a_i\equiv\phi_p\pmod p\}.
\tag{DA17}
$$

Apply the eight-match construction to all actual q-bearing originals
with at least eight such matches, using their actual quotient n_i/q.
The checked conclusion is

$$
\forall\phi\quad\exists x\in E_q\quad
\forall i\quad
\bigl(q\mid n_i\ \text{and}\ x\equiv a_i\pmod{n_i/q}\bigr)
\Longrightarrow |R_i(\phi)|\le7,
\tag{DA18}
$$

where E_q is the literal complement of all q-free originals. At this
same x, at least one actual q-bearing original contains x even before
stripping q. Thus the conclusion has an actual serving owner and does
not arise from an empty residual. The complete DA16--DA18 application
compiles with standard axioms and default proof budgets. Its literal
residues and quotient labels come from F; the phase table is one
fixed parameter. The quantifier order is
one fixed phi followed by a witness x; no common witness for every
phase table is asserted.

This restriction does not prove that the selected source traces
cover E0. That source-wide implication remains missing. One cannot
replace a fixed root table by a new table at each uncovered point
and then unite the incompatible assignments of shared numerical
donors.

## Two residues per prime allow one shared twelve-match repair

Fix a finite prime pool P of size at most 27, excluding three, and
one nonempty palette with at most two residues at each prime in P. The two
values may coincide. Count a match for owner i only at a prime in
P dividing its actual cofactor, where its literal residue equals
one palette value. Palettes are fixed jointly before constructing
any output; different coordinates may use different palette entries.

Under the same actual minimal-cover, no27, nine-bearing and q-bearing
conditions, with q at least 28, select actual owners with at least
twelve matches. There is one shared repair of their full safe
q-stripped union. It can preserve an existing family of outputs
27d whenever those old numerical donors are coprime to three, have
actual labels q*d, and at most 31 have four or more distinct prime factors. Their residues
are not changed. The three-hit prime-and-anchor block described
above satisfies the stock condition in its stated 27-prime branch.

Choose twelve matching primes S_i for each selected owner. A fixed
four-subset and a fixed tuple of palette phases identify at most
fourteen actual owners by DA9. There are at most sixteen phase
tuples per four-subset. Double counting the owner/four-subset
incidences therefore gives

$$
|I|\binom{12}{4}\le14\cdot16\binom{27}{4},
\qquad |I|\le7941.
\tag{DA19}
$$

This counts the actual original slots across every row and old word.
It does not count hypothetical independently chosen sources. Thus
there are at most 15*7941=119115 owner/safe-root demands.

For each owner use products of four, five or six primes from S_i
as random candidates. Remove the fixed occupied old bank. Before
removal the respective layers have 495, 792 and 924 distinct
numerical products. Subtracting 31 separately from each layer gives
the conservative simultaneous lower bounds 464, 761 and 893.
For every numerical donor in the union of these banks, independently
choose one safe root modulo 27 and one of the two palette entries
at each of its prime factors. CRT turns that single choice into
one output modulo 27d.

A donor with t prime factors serves any compatible owner/root demand
with probability at least 1/(15*2^t). Repeated palette values cause
no difficulty: the proof can recognize just one suitable bit vector.
Different demands need not be independent. For a single demand,
its distinct numerical candidates have independent choices. Hence
the total expected number of missing demands is at most

$$
119115\left(\frac{239}{240}\right)^{464}
\left(\frac{479}{480}\right)^{761}
\left(\frac{959}{960}\right)^{893}<1385.
\tag{DA20}
$$

An exact first-moment argument supplies one common assignment with
at most 1384 missing demands. The rational inequality in DA20 is
checked without rounding.

Reserve the products of seven through eleven primes from each S_i.
Before excluding the old bank, every owner has

$$
\binom{12}{7}+\binom{12}{8}+\binom{12}{9}
+\binom{12}{10}+\binom{12}{11}=1585
\tag{DA21}
$$

such numerical divisors, leaving at least 1554. Unique prime
factorization separates this reserve from every random bank, even
across different owners. All reserve labels are also unoccupied by
the old repair. Since fewer than 1554 demands remain, the existing
finite matching theorem assigns them distinct reserve labels. Give
each its required safe root and the literal phase of its owner.
This changes no old or random output.

The resulting assignment serves every owner at all fifteen safe
roots. A donor divides its owner's cofactor, so service covers the
whole cofactor class at that root, not just one sampled point.
Consequently it covers all of the owner's safe q-stripped trace,
including lower rows. Every new donor is an actual cofactor divisor;
minimality supplies its q*d label. The whole old/random/reserve bank
is therefore paid by DA16. Unused donors can be assigned arbitrary
residues without invalidating coverage or this full-bank budget.

In particular, a fixed palette's twelve-match sector cannot cover
E_q. If an old repair is retained, its target together with that
sector still cannot cover E_q. The missing point is common to both
failures. Taking the old bank empty gives the necessary source law

$$
\forall A\quad\exists x\in E_q\quad\forall i\quad
\bigl(q\mid n_i\ \text{and}\ x\equiv a_i\pmod{n_i/q}\bigr)
\Longrightarrow
\#\{p\in P:p\mid n_i/q,\ a_i\bmod p\in A_p\}\le11.
\tag{DA22}
$$

The count in DA22 is restricted to the stated pool P. In the
113-height-one branch one may take P to be the prime support of W;
it then includes every possible cofactor-prime match. Choosing
A_p from the residues of two fixed actual points permits all
coordinatewise mixtures of those points. Thus this palette result
is different from selecting just two complete phase tables.
It provides no assertion that a fixed palette sector covers E_q.

The full actual-source construction and its DA22 specialization
compile with standard axioms and default proof budgets. The
old-bank version supplies the same witness x outside every old
output, and at least one actual q-bearing original covers x before
stripping q.

## A small family of incompatible cofactor classes can be kept in the old bank

Retain the actual minimal-cover, no27, nine-bearing and q-bearing
hypotheses of DA22, with q at least 28. Select at most nineteen
actual q-bearing originals. For each selected original choose a
positive cofactor m_i with q*m_i dividing its original numerical
modulus, and keep that original's literal residue a_i. Assume m_i
has at least twelve distinct prime factors other than three.
The selected phases need not agree with each other. These twelve
prime factors need not lie in the palette's pool P; that pool
restricts only the later palette-match count.

Choose twelve such primes S_i. Products of zero, one, two or three
members of S_i give a numerical donor bank of size

$$
1+\binom{12}{1}+\binom{12}{2}+\binom{12}{3}=299.
\tag{DA23}
$$

Unique prime factorization makes these products distinct, including
the empty product one. There are at most 19*15=285 demands, one for
each selected original and each safe root modulo 27. Each demand
has 299 available donors. The existing finite matching theorem
therefore chooses a distinct numerical donor for every demand:
for any nonempty demand subset, its union contains one whole
299-element list, more than the total number of demands.

For demand (i,v), give its chosen donor d the CRT output

$$
x\equiv v\pmod{27},\qquad x\equiv a_i\pmod d.
\tag{DA24}
$$

Because d divides m_i, this covers every point of the entire
cofactor class [a_i] modulo m_i at that safe root. Donors are
coprime to three, and numerical labels 27d are distinct. Every
q*d divides an actual original and is a nonunit, so actual divisor
closure supplies the corresponding original label. These outputs
form an admissible old bank for DA22, with zero cofactors having
four or more distinct prime factors. Full all-q deletion pays for
that bank by DA16. Unused donors may receive arbitrary residues;
the same full-bank payment includes them.

Consequently, for any one fixed binary palette on the stated prime
pool, DA22 supplies one actual residual point x which simultaneously
lies outside all nineteen selected cofactor classes and has at most
eleven palette matches in every serving q-stripped original. The
point is safe because it avoids the actual pure 3 and 9 originals.
If it belonged to one selected cofactor class, DA24 would put it in
an old output, contradicting the same witness's avoidance of the
old bank.

This applies to incompatible literal phases and does not identify
cofactor projection with the original stripped trace. When the
original modulus is 3^r*q*m_i, the whole cofactor cylinder can be
larger than that trace; the construction covers this larger cylinder
at all safe roots. In particular, a family of at most nineteen such
cylinders cannot cover the exact residual E_q. No existence of a
nineteen-cylinder subcover of E_q has been proved.

The sufficient global obligation can be weakened accordingly. For a
fixed palette A, let H_A be the union of the actual q-stripped classes
with at least twelve matches in P. If J is any family of at most
nineteen eligible actual cofactor classes as above, the same-point
conclusion is

$$
E_q\setminus\left(H_A\cup\bigcup_{j\in J}[a_j]_{m_j}\right)
\ne\varnothing.
\tag{DA25}
$$

A contradiction would therefore follow from one fixed palette and
one such J covering E_q minus H_A. Covering all of E_q by J is not
needed. This extraction is not supplied by the known fixed lower-owner
cover PC66--PC68: that cover bounds multiplicity at each numerical
cofactor by two, but neither its total size nor the required twelve
prime factors. Restricting a complete color cover to E_q minus H_A
preserves coverage of that sector. It need not preserve an original
private point, since the private region's intersection with that
sector has not been shown nonempty.

The argument is an application of the existing finite matching,
prime-product, CRT and actual old-bank results. It supplies a
stronger interface consequence, not a new matching theorem.
The shared construction and the actual same-point specialization
compile with standard axioms and default proof budgets.

## Joint divisor inventories also constrain lower rows

Fix one actual count-then-sum-minimal odd distinct cover, with no
original divisible by 27 and with some original divisible by nine.
Let q be at least 28. For a positive odd d coprime to three, with
at least fifteen divisors, define the exact ancestor residual

$$
E_d=\{b\bmod d:\ b\not\equiv a_j\pmod{n_j}
                   \text{ whenever }n_j\mid d\}.
\tag{DA26}
$$

All ancestors in DA26 belong to the same original cover. This is a
residual on the divisor cut d, not the full all-q deletion hole E_q.
No product structure or lower density for E_q is inferred from it.

Let U be any finite set of positive integers such that q*d*u is an
actual original numerical label for every u in U. Distinct u give
distinct actual labels. The literal residue of each such original,
reduced modulo d, belongs to E_d. Indeed, if its phase agreed with
an ancestor n_j dividing d, its entire class would be contained in
that ancestor's class. The labels are different because
n_j is at most d, whereas q*d*u is greater than d. This contradicts
minimality of the original class count.

For each one phase modulo d, DA9 bounds the number of these actual
originals by fourteen. Counting the same numerical inventory over
its actual phases therefore gives

$$
|U|\le14|E_d|\le14d.
\tag{DA27}
$$

This argument retains the actual phases and every ancestor guard;
it does not optimize a separate phase distribution for each owner.

In particular, take any finite family of actual original labels

$$
n_i=3^{r_i}q m_i,
\qquad 3\nmid m_i,\qquad d\mid m_i.
$$

Numerical divisor closure supplies the complete joint inventory

$$
U=\bigcup_i\{3^a e:0\le a\le r_i,\ e\mid m_i/d\}.
\tag{DA28}
$$

Every u in this union supplies one actual label q*d*u, so DA27
applies directly. The union deduplicates equal numerical labels;
it is neither the sum of separate inventory sizes nor the divisor
set of a least common multiple presumed to be an original modulus.
Rows zero and one are included. No actual top label 9*q*m_i is
required, unlike the top-row inventory used in RA4.

The joint actual-label supplier, ancestor-phase containment and
finite-fiber bound compile together with standard axioms and
default proof budgets. They reuse divisor replacement, original
private points, DA9 and finite counting; this is not a new
finite-fiber theorem. The pointwise lower-color count still does
not force a common divisor and a joint inventory violating DA27.

## Low-support service and fixed-bank escape do not force large cofactors

Use the prescribed coordinate mask M from Report864 PC69: each of
27 prime coordinates takes the values zero and one; roots congruent
to two modulo three carry the whole binary cube, while roots four
and seven modulo nine carry only the all-zero point. No identity
between M and an actual retained-family residual is assumed.

Keep the two lower owners at each coordinate. Partition fifteen of
the coordinates into five disjoint triangles. For every edge {p,t},
add two owners with cofactor p*t: a row-zero owner at phase 00, and
a row-one owner at phase 11 with ternary root two. There are
2*27+2*15=84 owners, which can be assigned distinct colors among
113 labels. At every source point the coordinate owners supply
27 active owners. Every binary triangle has an equal-valued edge,
so the five triangles supply at least five more. At the all-zero
source points the row-zero edge owners are active. Thus every
source point has at least 32 distinct serving owners.

Each cofactor occurs twice and has at most two distinct prime
factors. Its divisor count is at most four, so none supplies either
a twelve-prime cofactor or a divisor with fifteen divisors. The
cofactor divisor bank explicitly declared for this control is

$$
P_{\triangle}=\{1\}\cup\{\text{the 27 coordinate primes}\}
                 \cup\{\text{the 15 triangle edge products}\},
\qquad |P_{\triangle}|=43.
\tag{DA29}
$$

This is the numerical divisor closure of these cofactors. It is
not a construction of the original-label divisor closure of an
actual minimal whole cover.

Even allowing one arbitrary fixed output of label 27d for every
d in this bank cannot cover M. It suffices to consider the nine
roots congruent to two modulo three in a period of 27. The unit
donor occupies at most one root. A single isolated-coordinate
output cannot cover both values of that coordinate. For one
triangle at one root, let P and E count its assigned prime and
edge donors. Covering its complete three-bit cube requires

$$
2P+E\ge5.
\tag{DA30}
$$

The entire triangle has only weight 2*3+3=9 across all roots,
since every numerical donor has one fixed root. It cannot cover
two roots completely. If a union of independent-component
cylinders covers a whole product, at least one component is
covered completely: otherwise combine one escape from each
component. The five triangles and the unit donor can therefore
cover at most six of the nine roots completely.

Consequently, for every fixed assignment of all bank outputs,
there is one source point escaping every output while still
having at least 32 active owners. Every owner's palette count
is at most two, and every cofactor has at most two owners.
The finite coordinate statement, including this same witness,
the three-bit cost and the fixed-root occupancy bound, is
Lean-checked with standard axioms and default proof budgets.
Absent phases and every possible binary singleton or pair phase
are included in the codes. Interpreting the coordinates as
prime products and integer residue classes uses the usual CRT
identification; that integer application is not separately
compiled in this check.

Thus 32-color lower service, multiplicity at most two, low support,
and escape from every fixed output assignment of this declared
bank do not imply the large-cofactor candidates needed by DA25
or a nonempty inventory to which DA27 applies. The control does
not supply all the required complete original color families,
identify M with their exact q-free residual, or realize global
count-then-sum minimality. Those actual joint conditions remain
available to a closing argument. Adding these owners also does
not inherit the original PC69 two-output prefix impossibility.

## Ancestor residuals do not supply unrestricted continuation

The phases counted in DA27 and points in the all-q deletion residual
have different roles. Every actual q*d*u label has its own phase in
E_d by its private witness. An arbitrary point x in E_q also reduces
to E_d when q does not divide d: every actual ancestor n_j dividing d
is then q-free. No primality of q is needed. DA28 imposes no such
condition on d, so this second projection cannot be inferred there
without the extra hypothesis.

For positive d and D with d dividing D, the source-preserving transport is given by
[Report385, Section232](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#232-lifting-an-interface-turns-a-small-quotient-payment-into-a-new-hole-set).
With reduction pi modulo d and each A_j taken modulo D, it reads

$$
E_D=\pi^{-1}(E_d)\setminus
       \bigcup_{n_j\mid D,\ n_j\nmid d}A_j.
$$

In particular, the reduction from E_D to E_d need not be onto.
The existing complete nonunit-divisor family of 735 in
[Section235](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#235-a-finite-nine-support-control-beats-the-internal-hole-mass)
has distinct odd labels and a private point for every class.
Its E_49 has 41 elements and contains 0, but all fifteen lifts of 0
modulo 735 are covered. In this eleven-class family, 13 remains a hole.
A scoped exact Lean check verifies these finite claims and the
projection condition above with standard axioms and default budgets.
This reuses the existing control; it is not a counterexample to a
minimal whole cover or a new density theorem.

Thus numerical divisor closure, private witnesses and the separate
ancestor inventories do not justify an induction preserving every
residual phase. A closing argument must control the actual joint
removal set under these transports, or supply a legal replacement
for it. DA27 alone bounds the labels divisible by q*d; no bound has
been obtained here for all the newly internal classes, including
those whose gcd with d is a proper divisor of d.

## External covering theorems retain their stated hypotheses

The official comments for Nagy--Pach--Tomon,
[*Irredundant hyperplane covers*, arXiv:2205.03389v2](https://arxiv.org/abs/2205.03389v2),
state: "There is a mistake in the proof of the main result, more
specifically in the proof of Claim 4.5, Section 4.2. This invalidates
most of the paper". The advertised index bound
$|G:\bigcap_i H_i|=2^{O(k)}$ is therefore not an established supplier
for the present argument. This notice does not say that every statement
in the paper is false.

The earlier paper by the same authors,
[*Additive bases, coset covers, and non-vanishing linear maps*,
arXiv:2111.13658v1](https://arxiv.org/abs/2111.13658v1), Theorem 1.2,
is a different result. Its $\exp(O(k\log\log k))$ index bound concerns
an irredundant coset cover of a whole abelian group. It does not provide the
nineteen-cylinder extraction on the nonproduct residual required
by DA25. BBMST's bounded-reuse mechanism likewise retains the
one-exploration-tree adapter described in Report385, Section247.

## Fixed-color completions need their own minimality check

Global minimal unsatisfiability does not make every fixed-color completion minimal with the same retained formula. A Boolean control has retained clauses \(R=\{x,y\}\) and moving clauses \((Q\ne0)\lor\neg x\), \((Q\ne1)\lor\neg y\). The full four-clause formula is unsatisfiable, and deleting each clause in the displayed order admits, respectively, the assignments \((Q,x,y)=(0,0,1),(1,1,0),(0,1,1),(1,1,1)\). It is therefore minimally unsatisfiable. At \(Q=0\), however, the completion reduces to \(x\land y\land\neg x\), and the retained clause \(y\) is dispensable; at \(Q=1\), it reduces to \(x\land y\land\neg y\), and \(x\) is dispensable.

Consequently, applying a minimal-unsatisfiable classification separately to all color completions while keeping one common retained formula requires an additional essentiality argument. This Boolean control refutes only that general inference; it is not an actual odd congruence-cover construction. The four-clause statement and both dispensable retained clauses were checked by Lean with default proof budgets and the standard `propext` axiom, using only finite Boolean decision procedures. The check is transient and adds no canonical Lean declaration.

## A missing enclosure bounds the actual joint inventory more sharply

Retain one actual count-minimal odd distinct whole cover F. Let d>1 be
an actual original label, let q>1, and let U be a finite set of positive
integers such that every qdu, u in U, is an actual original label. Write
P_d for the complete private region of the original d-class. Suppose
an odd nonunit e is absent from the original numerical inventory and
one residue class [w]_e contains all of P_d. Then

$$
|U|\le |E_d|.
$$

This is the actual-inventory application of Report385 DR4--DR6, with a
specified missing enclosure in place of the full private hull. It needs
neither the no-27 branch, a lower bound of 28 on q, nor modulus-sum
minimality. Those conditions remain part of the separate fourteen-per-
phase bound in DA26--DA28.

For clarity, the reduction preserves the actual whole cover. If two
selected descendants have the same phase modulo d, change the d-class
to that phase and replace the first descendant by [w]_e. Every point
private to d is covered by the replacement. Every other old d-point
has another original owner. The new d-class covers both descendants,
so the second descendant is redundant and can be deleted. The missing
odd nonunit e keeps all labels legal and distinct. This contradicts
count minimality. Hence the selected descendant phases are distinct.
Every such phase belongs to E_d by the original owner's private point,
and distinct u give distinct actual labels qdu, proving the bound.

Equivalently, if |U|>|E_d|, every odd nonunit modulus admitting a single
residue class enclosing all of P_d must already be an original label.
Taking the existing complete private hull Gamma_d as that modulus is
Report385's conclusion that Gamma_d is present. It does not imply
Gamma_d>d: Gamma_d may equal the already present parent d. No missing
complete-private-region enclosure has been obtained from the current
whole-cover hypotheses.

A scoped transient Lean application checks the actual replacement,
the phase injection, and the qdu inventory bound above directly on
OddDistinctCoveringSystem, reusing the existing private-point and
redundant-owner deletion results. It is an exact check of the reused
DR mechanism, not a new general theorem or a proof of hull growth.

## Joining the actual-source pointwise bounds

The PC62--PC65 count admits an exact composition that retains its
arithmetic premises. Let F be one whole odd distinct cover, minimal
first in count and then in modulus sum, with no modulus divisible by
27. Suppose every actual modulus divides 113R, with (113,R)=1.
Fix x in the complement E_113 of every original not divisible by 113.

For a packet M of actual top originals 9*113*m_i, assume all old
words agree with x modulo 9 and each owner has two distinct matching
primes in a common pool P of at most 27 primes: a_i is congruent
to x modulo each selected prime. The existing actual
prime-cut supplier and frozen graph density theorem give

$$
2|M|\le3|P|\le81,\qquad |M|\le40.
\tag{DA31}
$$

For the actual pure-prime-power packet J, keep the PC62 indexing of
27 prime axes, all at least five. Each label is 9*113*p^a with a>=1, and its stripped
class contains this same x modulo 9*p^a. On the first four axes,
actual deep descendants a>=2 are bounded by two, and numerical
label distinctness allows at most one a=1 owner. The next three
axes retain the explicit exponent bound a<=2; the last twenty
retain a<=1. Therefore

$$
|J|\le4\cdot3+3\cdot2+20=38.
\tag{DA32}
$$

The phase condition here is modulo the whole p^a, not merely p.
The exponent envelope remains an explicit premise; this composition
does not prove it for arbitrary odd covers.

Require the actual classification: every original divisible by 9*113
whose stripped class contains x belongs to M or J, apart from the
unit-cofactor labels 113,339,1017. CRT supplies every one of the 113
literal colors at this same x. Let C_unit be the set of colors of
all actual unit-cofactor originals. These labels contribute at most
three colors. Taking images under the actual color map consequently
gives

$$
\#\left(\{a_i\bmod113:
  113\mid n_i,\ 9\nmid n_i,\ x\equiv a_i\pmod{n_i/113}\}
  \setminus C_{\rm unit}\right)
\ge113-40-38-3=32.
\tag{DA33}
$$

The exact composition derives both packet bounds and the 113-color
service from the stated whole-cover data, rather than assuming the
numbers 40,38,113. It explicitly retains the exponent bounds and the
exhaustive top classification. Candidate subfamilies without that
classification do not suffice. The packet sets need not be disjoint;
the upper union bound has the required direction.

This verifies the existing pointwise conclusion under its declared
conditions. It does not produce 32 fixed complete lower-color covers
or a permanent numerical-donor assignment. All constituent checks and
the combined statement compile with default proof budgets and only
the standard three axioms. They remain transient applications of the
existing suppliers, not new canonical declarations.

## Repeated cofactors inside a literal color

Report869 already supplies a sufficient coherent-color condition:
for each of the fifteen safe roots r modulo 27, choose a subfamily
of one actual complete color that covers X_z, where z=r modulo 9,
and require the numerical cofactors of all selected occurrences to
be globally distinct. The outputs 27m_i then cover the exact residual
and satisfy the existing payment theorem. Disjoint cofactor sets
between selected colors alone are insufficient: qm,3qm,9qm can
repeat the same cofactor within a color.

Fix a prime q>3 of height one, with every actual modulus dividing
qR and (q,R)=1. For moving originals write n_i=q*3^(r_i)*m_i,
where r_i is the actual ternary valuation, r_i<=2, and 3 does not
divide m_i. Let x be a complete private point of original i.
Then x belongs to the exact q-free residual. Any original j of the
same literal q-color whose stripped class contains x must equal i:
combining the congruences modulo q and n_j/q would otherwise make
j cover the original private point as well.

Hence every same-color subfamily covering the complete X_z must
retain i whenever its private region meets the old word z modulo 9.
In particular, if two distinct originals have the same color and
cofactor, and both private regions meet the same word z, every such
complete slice subcover must contain both. Its cofactor map cannot
be injective. This is a conditional obstruction; no assertion is
made that such a pair must occur in an actual minimal cover.

In this situation the two residues modulo the shared m must differ.
Otherwise the two private points would agree modulo 9m, because
(9,m)=1. The stripped modulus of either owner divides 9m, so it
would also serve the other's private point. The obstruction thus
lies in different ancestor-phase fibers. Same-phase capacity bounds
do not by themselves separate these private-word sets.

Scoped Lean applications verify the actual private-point projection,
its necessity in a complete color slice, and the distinct-phase
consequence. The general exact check permits arbitrary row labels;
the numerical-cofactor interpretation here additionally uses the
explicit factorization and ternary-coprimality conditions above.
Count minimality supplies each owner's private point, but not a
separation of the private words of repeated-cofactor owners.

A weaker sufficient condition than distinct m_i is already available
from the donor-matching interface in Reports870 and872: choose a
globally distinct divisor d_i of each selected occurrence's m_i.
The literal phase projected modulo d_i and output 27d_i cover that
occurrence's whole slice. All shared demands must satisfy the joint
Hall inequalities; separate choices per color do not establish them.
This leaves the same actual-source allocation obligation, without
requiring the stronger cofactor-disjointness condition.

## Minimal divisor-allocation failures have small row deficits

Retain one specified finite family of selected occurrences with an
injective map to actual original slots. Distinct selected colors at
different safe roots, and no repeated original within one root, are
one way to ensure this injectivity. Existence of a complete slice
selection with these properties remains an obligation.

Let B be a finite ideal of positive numerical divisors containing
every selected cofactor, with every qd, d in B, an actual original
label. In the existing joint Hall criterion, suppose J is an
inclusion-minimal deficient divisor ideal contained in B. Put

$$
N(J)=\#\{i:m_i\in J\},\qquad
\delta=N(J)-|J|>0.
$$

Minimality means N(K)<=|K| for every proper divisor ideal K contained
in J. If m is maximal in J under divisibility, removing m leaves a
divisor ideal. Let k_m count selected originals with cofactor m.
Then

$$
N(J)=N(J\setminus\{m\})+k_m,
\qquad k_m\ge\delta+1.
\tag{DA34}
$$

If all selected actual labels have the form q*3^a*m with 0<=a<h,
distinctness of original numerical moduli makes the row map on each
cofactor fiber injective. Consequently

$$
1\le\delta<h,\qquad
\delta+1\le k_m\le h
\quad\text{for every maximal }m\in J.
\tag{DA35}
$$

With three rows the deficit is one or two. If it is two, every
maximal cofactor has all three selected row labels, including an
actual 9qm original. The deficit-two condition therefore supplies
the actual-top-label premise of the existing inventory bound at
every maximal cofactor; that bound's other hypotheses still apply.
Deficit one alone establishes neither this premise nor the absence
of a top owner. With only the two lower rows the deficit is one
and every maximal cofactor occurs exactly twice. These statements
have scoped Lean checks directly on injectively selected actual
originals, using default proof budgets and the standard three axioms.
They reuse finite cardinality and the numerical-label injection.

Neither repeated labels nor a deficit of two makes their phases,
colors or private old words equal. In particular, existence of the
actual 9qm label licenses its individual inventory bounds; it does
not put different maximal owners through one common point and so
does not by itself license a same-point packet capacity bound.

This locates minimal allocation failures without repairing them.
If an ancestor is q-free, its full private region is outside E_q;
the complete-color cover on E_q does not constrain that region.
Report385 DP3's cross-cofactor payment requires full private-region
concentration as a separate input. A Hall deficit does not supply
that input. DA27 and the missing-enclosure inventory inequality are
upper bounds, not lower bounds on available donor stock.

Report385 PH3--PH4 also retains the complete private hull's period
constraint. For a nonempty full private region, its periodicity by
Q implies that any single congruence class containing it has modulus
dividing Q: apply the class to a private point and that point plus Q.
Thus an original system of ternary height two cannot place a parent's
entire private region inside a single new 27d or 81d class. Such a
repair needs the full prefix forest or another established joint
replacement. The missing bridge remains an actual-source joint
matching, compatible shared output, or fully paid parent exchange.

## A private-region repair for one complete cofactor fiber

There is a local sufficient condition that rules out a special
case of the three-row deficit in DA35. It does not require a
complete color to share one original cofactor phase.

In a count-minimal actual cover, two distinct original moduli
which are comparable by divisibility have disjoint classes.
Otherwise their intersection would make the larger-modulus class
a subset of the smaller one, contradicting its private point.
The original labels q*3^a*m for a fixed numerical m are comparable.
Consequently, deleting any collection of these slots leaves exactly
the union of their complete private regions. This is the disjoint
family case of Report385 PH1--PH2 and PI10; no such identity is
asserted for an arbitrary family of overlapping classes.

Suppose the actual three slots qm,3qm,9qm occur, q>=7, the same
cover is count-then-sum-minimal, and no original modulus is divisible
by 27. Suppose all three complete private regions lie in one old
word z modulo 9. Let d divide m, suppose their three literal residues
are congruent to one beta modulo d, and suppose d has three distinct
positive divisors t_0,t_1,t_2.

For each child c in {0,1,2}, use the new modulus 27t_c with residue
specified by z+9c modulo 27 (using z modulo 9) and beta modulo t_c.
The actual labels and no27 imply that m, hence t_c, is coprime to
three. CRT therefore supplies these output classes. Every private
point lies in one child and satisfies its divisor phase, so these
three outputs cover the true joint deletion hole. They are distinct
odd nonunit moduli, all fresh by no27. Keeping all other classes
and making this three-for-three replacement gives

$$
\sum_{c=0}^2 27t_c\le81m<13qm=qm+3qm+9qm,
$$

contradicting sum minimality. A scoped Lean check constructs the
actual replacement cover and verifies its count, distinctness and
cost, using only the standard three axioms and default proof budgets.
The hypotheses involve every private point in the original F,
not a chosen representative or only one restricted trace.

Thus a deficit-two maximal cofactor with three rows cannot also
have this private-word concentration and this common divisor phase.
DA35 alone provides neither condition. The local contradiction does
not produce a joint allocation for all fifteen roots.

## Actual stock phases and fixed transverse color covers

Keep one actual count-then-sum-minimal whole cover F, q=113,
a common period qM with (q,M)=1, no original divisible by 27,
and the actual modulus-three and modulus-nine guards in distinct
modulus-three phases. For d dividing the q-free, three-free part
of M, assume d has at least fifteen positive divisors. Write E_q
for the exact residual of the q-free originals modulo M, and set

$$
S_d=\pi_{M,d}(E_q).
$$

Every actual q-bearing original whose modulus is divisible by d
has its own fixed residue modulo d in S_d. Indeed, its private
point misses every q-free original. Reduction modulo M preserves
that fact, and reduction modulo d gives its own phase. This uses
a private point of that actual original, not a phase inherited
from the larger original that caused its divisor label to exist.
It requires no assertion that the projection E_q to the ancestor
residual E_d is surjective; generally only S_d contained in E_d
is available.

Let U be a finite set of numerical labels such that every qdu,
for u in U, occurs among the actual originals. Numerical
distinctness embeds U into those originals. DA9 bounds the number
of such originals at any one d-phase by fourteen, hence for every
finite phase set T_d containing S_d,

$$
|U|\le14|S_d|\le14|T_d|.
$$

In particular U may be the joint divisor stock of several
originals: repeated labels are counted once, each label keeps its
actual residue, and actual divisor closure supplies membership.
The inequality becomes useful only after a separate upper bound
on the supported phase set; there is no such universal small bound
established here.

There is also a uniform statement across an entire fixed fiber.
For b in S_d, let V_d(b) be the literal colors of all actual
originals whose modulus is divisible by qd and whose residue is b
modulo d. DA9 gives |V_d(b)| at most fourteen. For every fixed
color c outside V_d(b), its owners whose stripped modulus is not
divisible by d cover the entire exact fiber

$$
E_q(b)=\{x\in E_q:x\equiv b\pmod d\}.
$$

Thus at least ninety-nine fixed literal colors give complete
transverse covers of that one fiber. The exceptional set depends
on b, not on the point x inside the fiber. To see the uniformity,
take any x in the fiber and its actual owner of color c, supplied
by whole-cover CRT. If that owner's stripped modulus were
divisible by d, its phase would be b and c would belong to V_d(b).
For the actual factorization q*3^r*m with (3,d)=1, transverse here
is equivalent to d not dividing m. No disjointness, independent
donor assignment, or common choice of one owner across the fiber
is asserted.

The actual phase-support statement, its equality with the exact
finite residual projection, the inventory bound, and the fixed
ninety-nine-color fiber coverage have scoped exact Lean checks
using the existing private-point projection, DA9 capacity and
complete-color supplier. They use only the standard three axioms.
They are reuse consequences, not newly retained canonical theorem
wrappers, and do not supply the missing joint fifteen-root repair.

The relation-size input can use an existing joint bound without
assuming independence. Atserias, Grohe and Marx, *Size Bounds and
Query Plans for Relational Joins*, [arXiv:1711.03860v1, Section 3.1,
Lemma 2](https://arxiv.org/abs/1711.03860v1), gives

$$
|\Join_K S_K|\le\prod_K |S_K|^{\lambda_K}
$$

for finite relations on common named attributes and nonnegative
fractional edge-cover weights. In the present coordinates, use all
CRT prime-power digits of d as attributes; a cut at gcd(d,K)
retains exactly its prefix digits. Every digit must receive total
weight at least one. A missing digit requires an additional full
domain relation, with its actual alphabet size retained. Empty
relations give an empty join directly. Projected cut relations can
lose compatibility in discarded coordinates, so their join is only
an outer approximation to the common supported phases. The lemma
therefore supplies an upper-bound interface, not a contraction by
itself. No new effective bound on these actual relation sizes has
been supplied. This is literature reuse; the joint cardinality
inequality and its CRT application are not additional Lean claims.

## A matroidal Helly interface retains a missing geometric hypothesis

Kalai and Meshulam, *A topological colorful Helly theorem*,
Advances in Mathematics 191 (2005), 305--311,
[Theorem 1.6](https://math.huji.ac.il/~kalai/leray.pdf)
([DOI](https://doi.org/10.1016/j.aim.2004.03.009)), proves the following:
if a finite simplicial complex K is d-Leray over the rationals and
contains the independent-set complex of a matroid M on the same ground
set I, then there is a face T of K with rank_M(I minus T) at most d.
The statement is also reproduced as Theorem 1.3 in Kim and Lew,
[arXiv:2305.12360v1](https://arxiv.org/html/2305.12360v1).

For one actual source X=E_q, let A_i be each original owner's exact
q-stripped trace in X, and define

$$
K=\{S\subseteq I:\exists x\in X\quad
                     \forall i\in S,\ x\notin A_i\}.
$$

These are precisely the families which fail to cover the source.
Let M be the divisor-donor transversal matroid. If no independent
family covers X, then M is contained in K. The cited theorem would
then give one uncovered point x whose active owners have donor rank
at most d: choose x missed by T, so every active owner lies outside T.

In the three-row setting, the owners active at any one point are
partitioned into three independent sets by row, using each owner's
own cofactor as its numerical donor. Thus the already established
113-color service gives active donor rank at least 38. A proof that
this particular K is d-Leray for some d at most 37 would therefore
supply one independent complete cover. No such Leray bound has been
obtained; a list of 27 prime directions is not a proof of this
topological condition. The external theorem and this conditional
application are literature-based, not a Lean formalization of
simplicial homology or the Kalai--Meshulam theorem.

The actual private points give a concrete condition that this route
must respect. For any one complete literal color family C, count
minimality and private-point projection show that every proper
subfamily S of C misses a point of the whole E_q. The full C covers
E_q, so the induced noncover complex on C is exactly the family of
proper subsets of C. This finite equivalence has a scoped Lean check
using the existing actual private-point result, standard axioms and
default proof budgets. It concerns the whole E_q; it does not say
that every old-word slice retains every owner, or that adjoining C
to the entire retained family gives a minimally unsatisfiable whole
formula.

For a color family of size at least two, that induced complex is a
simplex boundary with nonzero reduced rational homology in degree
|C|-2. Consequently d-Lerayness requires d at least |C|-1. In
particular the proposed d at most 37 route would require every
complete color family to have size at most 38. That color-size bound
has not been established. This last homological consequence uses
the standard simplex-boundary computation; it is not part of the
scoped Lean check.

Actual divisor closure can instead force large color families. If a
count-then-sum-minimal cover contains the actual label 9*113*m,
with m coprime to three and at least s distinct prime factors, then
every label 113*d for d dividing 9m is an actual original. These
labels are distinct, and their number is

$$
\tau(9m)=3\tau(m)\ge 3\,2^s.
$$

They retain their actual literal colors; no residues are reassigned.
Pigeonhole counting over the 113 colors gives a complete color family
of size at least the ceiling of 3*2^s/113. In particular s at least
eleven gives size at least 55, and s at least twelve gives size at
least 109. Together with the induced-boundary consequence these
force Leray number at least 54 and 108 respectively, excluding the
proposed d at most 37 route in these branches. The arithmetic
inventory, injection and color-count implications have a separate
scoped Lean check; the topological conclusion remains the standard
literature consequence. The whole-source boundary application
continues to require the common period 113R with (113,R)=1. The
inventory counting alone does not require that extra coprimality.
This argument uses one actual top label and its divisors, never a
least common multiple presumed to be an original.

There is a further target boundary in the all-color ground set.
Actual divisor closure supplies the original modulus q itself. Its
stripped modulus is one, so its singleton trace covers the whole
E_q and is independent using numerical donor one. Thus a single
independent complete cover is already available, and the conditional
Helly interface above supplies no missing certificate for that
target. Fifteen safe root copies still need one joint numerical
assignment: donor one can be used for only one root. Conversely,
failure to obtain such an original-trace certificate would not
exclude a legal repair: projected divisor outputs can cover more
than their original traces, and a divisor-one output already covers
its entire assigned safe root.

For the actual joint target, replace the ground set by root-owner
occurrences and replace X by the disjoint union of the fifteen
root-specific sources. Each occurrence covers only its own root
copy of the corresponding exact trace. Give all occurrences one
transversal matroid with the same numerical-divisor bank; its
independent sets are precisely jointly matchable demands. The
Kalai--Meshulam statement applies to the resulting noncover complex
under its own Leray hypothesis. At a point (r,x), the active owners
are in root r, so the previous rank lower bound remains 38. The
single q owner now covers only one root, and its fifteen copies
cannot share donor one in an independent set.

The joint Leray hypothesis is stronger than separate hypotheses for
each root. Choose a minimal same-color cover D_z of each nonempty
old-word slice, using the empty set for an empty slice. The existing
private-slice necessity result implies that every owner in a
complete whole-source color C occurs in at least one D_z: a private
point is in some safe word. Consequently the sum of their sizes is
at least |C|. The five safe words are obtained from the existing
fifteen-safe-root count by an explicit product equivalence with
three copies per word. Three copies per safe word have disjoint source
supports. The union of their minimal covers is a minimal cover of
the disjoint source union, so the joint noncover complex contains an
induced simplex boundary with at least 3|C| vertices. Its Leray
number is therefore at least 3|C|-1. The finite bridge has a scoped
Lean check: Mathlib finite minimality supplies each D_z, actual
private-point projection proves their union is exactly C, and the
noncover predicate on the selected joint occurrence set J is proved
equivalent to being a proper subset of J. It also proves the exact
cardinality |J|=3 sum_z |D_z| and the actual-source consequence
|J| at least 42 when s is at least nine. Empty slices require no
extra assumption. Standard simplex-boundary homology then gives the
Leray inequality; that topology is not part of the Lean check.

For example, nine distinct prime factors in an actual top cofactor
give at least 1536 actual q-bearing labels and hence some color of
size at least fourteen, forcing joint Leray number at least 41.
This excludes the proposed d at most 37 joint certificate in that
branch. It neither excludes all uses of matroidal Helly with stronger
active-rank information nor excludes a repair using the larger
projected divisor-output sets.

## The universal original label obstructs source cocircuit elimination

The source-spanning matroid route has an additional necessary condition
on the full original-owner ground set. Let q=113, let E_q be the exact
q-free residual, and let

$$
D_x=\{i:q\mid n_i,\ x\equiv a_i\pmod{n_i/q}\}.
$$

For any declared source X contained in E_q, use the clutter of
inclusion-minimal actual neighborhoods

$$
\mathcal H_X=\min_{\subseteq}\{D_x:x\in X\}.
$$

The elimination condition under consideration is

$$
H_1,H_2\in\mathcal H_X,\quad H_1\ne H_2,\quad e\in H_1\cap H_2
\quad\Longrightarrow\quad
\exists H_3\in\mathcal H_X:\
H_3\subseteq(H_1\cup H_2)\setminus\{e\}.
\tag{CE}
$$

This is a condition on neighborhoods of the actual source, not the
exchange property of the donor matroid. The finite circuit
characterization, applied to the dual, is the usual matroid
interpretation of this condition. The existing source-spanning
sufficient route still requires this source-side premise; no matroid
intersection theorem is reproved here.

Actual divisor closure supplies an original g with n_g=113 as soon
as an actual q-bearing top label is supplied. Its stripped modulus
is one. Consequently g belongs to every D_x and every member of
\mathcal H_X. If H_1 and H_2 were distinct minimal neighborhoods,
applying (CE) with e=g would demand a minimal neighborhood not
containing g, a contradiction. Conversely, a clutter with at most
one member satisfies (CE) vacuously. Thus on this full ground set,

$$
\boxed{\quad
(\mathrm{CE})\quad\Longleftrightarrow\quad
|\mathcal H_X|\le1.
\quad}
$$

For a nonempty source, finite owner cardinality guarantees the
existence of a minimal actual neighborhood. For an empty source,
there are none; this case is retained.

This obstruction can be connected to actual private points without
assuming every owner is active on every old word. Put
X_z=E_q\cap\{x:x\equiv z\pmod9\}. If (CE) holds on X_z, every
inclusion-minimal complete subcover of X_z drawn from q-bearing
original owners has cardinality at most one. To see the finite interface, choose a minimal neighborhood H.
A complete subcover meets H at some owner j. Every actual neighborhood
contains a minimal neighborhood and therefore contains H by
uniqueness. Thus j alone covers X_z, and minimality removes every
other member of the subcover. An empty slice has the empty minimal
cover.

Now retain the actual count-then-sum-minimal cover hypotheses:
all moduli divide 113R with (113,R)=1, no original modulus is divisible
by 27, and an actual label is 9*113*m with (3,m)=1. The actual 3 and 9
guards leave five safe old words. Fix one complete actual literal
color C, and use the already checked minimal slice subcovers D_z.
Actual private-point necessity gives

$$
C=\bigcup_{z\text{ safe}}D_z,
\qquad
|C|\le\sum_{z\text{ safe}}|D_z|.
$$

If all five safe source slices satisfied (CE), the singleton bound
would give

$$
\boxed{\quad |C|\le5\quad\text{for every actual literal color }C.\quad}
$$

The existing actual top-label inventory excludes this necessary
condition when m has at least eight distinct prime factors. It
supplies at least

$$
3\,2^8=768
$$

actual q-bearing labels, partitioned into 113 actual literal colors.
Some color has at least seven owners. Therefore at least one safe
old-word source fails (CE). The exact Lean conclusion identifies
actual 3 and 9 guard owners, a safe word z relative to their actual
residues, and failure of (CE) on the actual X_z. It does not supply
a prescribed mask or an unrelated finite counterexample.

Scoped Lean applications verify universal q-owner membership,
(CE) equivalence with uniqueness of minimal actual neighborhoods,
the minimal slice-cover bound, the five-word color bound, and the
actual eight-prime-factor obstruction. They reuse Mathlib finite
minimality, the actual complete-color supplier, private-point
projection, actual divisor closure and guard separation, and the
existing top-label inventory. They compile at default budgets with
only propext, Classical.choice and Quot.sound. Matroid circuit
characterization and the external matroid-intersection implication
are not newly formalized here. Relevant existing Mathlib interfaces
for the parallel source-spanning interpretation are
Matroid.isBase_iff_minimal_spanning and
Matroid.IsBase.ncard_eq_ncard_of_isBase: under a representation of
source coverage as spanning in the same matroid, a singleton complete
cover forces every minimal spanning cover to have at most one member.

The scope is the original-owner ground set containing the actual
q owner. Deleting that owner's literal color, changing the available
owners, or replacing exact original traces by larger divisor-output
sets changes the neighborhood system; the result does not settle
those modified problems. It also does not exclude a joint repair
when source coverage has no matroid representation. In the remaining
small-inventory branches, source elimination remains an additional
unverified condition, not a conclusion of the three-row donor bound.

## Actual private points obstruct the unmodified source-degree certificate

Fix one actual count-then-sum-minimal odd distinct covering system F.
Assume every original modulus divides 113R, with (113,R)=1. The source
ground set consists of its actual 113-bearing original owners. The three-row donor applications additionally assume no original
modulus divisible by 27; the five-safe-word statements use the actual
modulus-3 and modulus-9 guards in distinct modulus-3 phases.

Király, Lau and Singh, *Degree bounded matroids and submodular flows*,
[Theorem 2](https://real.mtak.hu/19505/1/kiraly_lau_singh_final.pdf),
provides a basis satisfying every one-sided integer lower degree bound up to
an additive loss of Delta minus one. Here Delta is the maximum number of
constraint hyperedges containing a ground element. Section 3 starts from a
feasible fractional base vector; its proof does not require a pre-existing
integral solution satisfying all degree constraints. The original theorem
and its algorithm are reused, not re-proved or claimed as Lean results.

For the actual original-owner ground set, let D_x be the q-bearing owners
whose literal q-stripped class contains x. Retain the distinct
inclusion-minimal D_x. Three-row donor colorability gives a fractional base
vector with every coordinate at least one third. The 113 actual complete
colors therefore make the uniform integer lower bound 37 feasible.
The theorem's guarantee reaches one only if Delta is at most 37.
For the direct fifteen-root occurrence ground set, the 45 row/root pieces
give only the uniform integer lower bound two, so the corresponding
sufficient condition is Delta_occ at most two.

There is an actual obstruction on this unchanged ground set. Divisor
closure supplies the original owner g of modulus 113. Its stripped class
has modulus one, so g belongs to every source neighborhood, and hence to
every minimal source neighborhood. Its degree is exactly the total number
of those distinct minimal neighborhoods, and attains the maximum degree.

For any complete literal color C on the whole residual E_113, actual
private-point projection forces at least |C| distinct minimal neighborhoods.
For each i in C, take its actual private witness x_i and minimize D_(x_i)
by inclusion. The resulting neighborhood still covers some source point,
so it meets C. Its intersection with C is exactly {i}. The resulting
neighborhoods are distinct. Consequently

$$
\Delta\ge |C|.
$$

The same argument applies to any inclusion-minimal cover D_z of one
old-word slice X_z, drawn from the 113-bearing original owners.
The existing private-point/minimal-slice result gives

$$
|D_z|\le\Delta_z,
\qquad
|C|\le\sum_{z\text{ safe}}|D_z|
       \le\sum_{z\text{ safe}}\Delta_z.
$$

There are five safe old words. Thus Delta_z at most k on all five slices
would force every complete literal color to have size at most 5k.
These implications have exact scoped Lean checks using finite minimal
extraction, actual private points, and the previously checked divisor stock.

In particular, suppose one actual top modulus is 9*113*m, with m coprime
to three and at least s distinct prime factors. The existing divisor-stock
result supplies a color of size at least the ceiling of 3*2^s/113.
At s at least eleven this gives Delta at least 55 on the whole source,
excluding the proposed Delta at most 37 certificate. Under the additional
no27 and actual 3/9-guard hypotheses above, s at least nine gives a color
of size at least fourteen.
Some safe old-word slice therefore has Delta_z at least three. Each of
its three root occurrences has the same source hypergraph with its own
root tag, so the direct joint fifteen-root certificate Delta_occ at most
two fails. At s at least eleven and twelve the same calculation gives
some slice with Delta_z at least eleven and twenty-two respectively.

This obstruction survives exact compression by positive hitting
constraints on the same owner ground set. If a finite hypergraph K
satisfies, for every owner subset S,

$$
S\text{ covers }X
\quad\Longleftrightarrow\quad
S\cap G\ne\varnothing\text{ for every }G\in K,
$$

then K contains every original minimal source neighborhood. Its vertex
degrees cannot be smaller than those of the minimal-neighborhood
hypergraph. This finite implication also has an exact scoped Lean check.
It applies to arbitrary such K, not just deletion of duplicate constraints.

DA9's bound fourteen counts owners sharing a fixed divisor phase. It does
not count source neighborhoods containing one owner. The ninety-nine
fixed transverse colors cover a specified phase fiber but provide no
bound on the number of distinct minimal neighborhoods in that fiber.
In particular the universal modulus-113 owner remains transverse for
any nonunit divisor cut. The two incidence parameters cannot be exchanged.

These statements exclude the displayed small-Delta certificate on the
unchanged original-owner ground set in the specified inventory branches.
They do not exclude fixing the universal owner to one root, deleting its
color elsewhere, contracting paid donors, changing to legal output
occurrences, or using additional matroid-dependent constraints. Those
operations change the source hypergraph or the feasibility contract and
require a new proof. Nor does failure of this sufficient certificate
assert failure of the desired fifteen-root repair. One whole-source
cover alone is already supplied by the modulus-113 owner and donor one.

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
