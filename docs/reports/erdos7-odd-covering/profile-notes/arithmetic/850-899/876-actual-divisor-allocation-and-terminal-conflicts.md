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
