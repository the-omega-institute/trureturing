# Eight shallow anchors permit independent choices between arbitrary ternary references

A normalized conditional-source comparison and a two-fibre support certificate
give a restricted original-family noncoverage result. Other old-only classes,
including arbitrarily high pure3 and pure5 powers, are unrestricted. These are
ordinary mathematical deductions and exact rational checks, not Lean
certification or a resolution of unrestricted Erdős #7.

## Statement and original-family scope

Let P={3,5,7,11,13,17,19}. Consider a finite original family of residue classes
with pairwise distinct odd numerical moduli greater than one, supported on
P union {23,29}. Its old-only subfamily contains

    0 mod3, 1 mod9, 4 mod27,
    0 mod5, 1 mod25, 2 mod15,
    31 mod45, 16 mod75.                         (NP1)

There is no restriction on other old-only classes. In particular original
pure3^e classes for e>=4 and pure5^e classes for e>=3 are permitted with arbitrary
phases, subject only to numerical distinctness.

There are two fixed integer centres a,b agreeing at every nonternary
precision used by the original later old cofactors. There is no restriction
on their ternary positions or on their common nonternary residues. At each
full original later label d*23^j*29^k, j+k>0, its old
residue is fixed once as either a mod d or b mod d. Different full labels
choose independently. All new-coordinate residues and finite heights are
arbitrary.

Using the same-source construction and bounds of [report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md), this
original family has Haar survivor mass greater than 1/80000000000 and hence
cannot cover the integers. The new calculation uses [report481](481-individual-mixed-budgets-strengthen-two-fibre-certificates.md)'s individual
mixed-budget pair inequality. The source construction is attributed to Michael Schroeder's *Nine Prime
Divisors in Odd Distinct Covering Systems*, edition1.0.1. Its source identity
and arbitrary-height verification boundary remain in the [library
entry](../../../../../Library/Arith/schroeder2026nine.md); the cited reports
supply the same-process bounds and the fixed-label pair proof.

## One source and the enlarged eight-cylinder anchor

Choose one finite legal completion of the old-only family and one charged
source process supplied by report467. Its old live measure nu satisfies

    nu(1)>=m7=7235955529/450000000000,
    nu<=(27/2)H,

and starts from Haar on its actual completed3--5 anchor. Every full-history
normalized kernel at 7,11,13,17,19 has the corresponding Haar density cap

    3/2, 5/3, 3/2, 2, 9/5.                    (NP2)

The same actual source supplies the mass lower bound, density bound and
conditional caps. The eight original classes (NP1) are legal selected
classes and retained in the source completion; its initial anchor therefore
lies inside A8, the complement of those eight classes alone.

For an upper estimate enlarge the initial measure to H restricted to A8 and
remove all later deletion indicators. Keep the same full-history normalized
kernels wherever originally defined and extend them by Haar on additional
histories if needed. Haar is admissible because every cap is at least one.
Positivity of the kernels implies that this enlarged comparison dominates
the actual old live source on every event used below.

Crucially, no deep pure3 or pure5 exclusion is subtracted from A8. Their
positions and mutual overlaps do not enter this upper bound. No infinitely
completed physical source, chosen pure-tail column, or limiting completion
argument is required for the new step.

## Exact initial masses and adaptive conditional rows

Take fixed p-adic reference paths extending the original finite centre
prefixes. The nonternary paths can use a common continuation beyond every
needed original precision. This does not assert equality of distinct
ordinary integers at all infinite precisions.

First treat centres in the two remaining ternary roots, exchanging their
names so a=2 mod3 and b=1 mod3. Only these roots survive the class0 mod3.
The other centre cases are reduced below. Write u=v3+1>=2 in a matching root
and k=v5+1 relative to the common5 reference. The fixed prefix instance
a=17 mod27, b=25 mod27, a=b=3 mod25 supplies the recorded node values; the
whole prefix domain is then checked with the same support tree. Every allowed residue pair modulo
27 and25 has Haar mass1/675. If its coordinate cell contains the reference,
deeper valuation shells have exact masses (p-1)/p^f for factor f, and a
tail f>=J+1 has mass p^(-J). A cell not containing the reference has one
fixed valuation. These rules determine every initial profile mass exactly.

At a later prime p with density cap Cp, the conditional probabilities of
factor f bins and their final tail obey

    r_f<=min(1,Cp*(p-1)/p^f),
    r_tail<=min(1,Cp/p^J),
    all r>=0, sum r=1.                         (NP3)

These are constraints on every entire earlier history. Averaging them
within a valuation profile preserves both each cap and row normalization.
The hidden earlier digits are not assumed independent.

For nonnegative child upper payoffs, a row's exact maximum is obtained by
sorting the payoffs downward and filling each capacity until total mass one
has been allocated. An exchange of mass from a smaller payoff to a larger
unsaturated payoff proves this maximization rule. It applies uniformly at
each full history, so recursive application is an upper bound for every
admissible adaptive source kernel, not just a selected product law.

## Fixed-label pair inequalities

A terminal old profile has root b, ternary factor u, and six nonternary
factors f=(f5,f7,f11,f13,f17,f19). Put Q=u*product(f). This is the full
two-centre union inventory at that point. Q<=19 gives an actual later fibre
survivor mass at least1/77.

For opposite-root profiles (u,f),(v,g), set

    Qx=u*product(f), Qy=v*product(g),
    N=Qx+Qy-min(u-1,v-1)*product_i min(f_i,g_i). (NP4)

The subtracted term counts shared nonternary divisors paired with positive
ternary exponents matching the opposite centres. Exponent zero retains both
points in the activity sum. The formula permits different nonternary profiles.
Each original full label still has one fixed centre choice for both points.

Define

    ax=min(22,Qx), ay=min(22,Qy),
    bx=min(28,Qx), by=min(28,Qy),
    A=min(N,ax+ay), B=min(N,bx+by),
    I=[max(0,A-ay),min(ax,A)],
    J=[max(0,B-by),min(bx,B)],
    rx=(22-t)(28-z), ry=(22-A+t)(28-B+z).

The exact pair capacity numerator from report481 is

    K=min_(t in I,z in J) max(0,rx-Qx,ry-Qy,rx+ry-N).           (NP5)

Here N<=Qx+Qy is supplied by the original-label inventory. Report481 proves
that the minimum is attained on an edge and can be found among at most28
exact rational candidates. Its ordinary original-family implication is

    s(x)+s(y)>=K/616,                          (NP6)

for any actual points in the two profiles. The numerical relaxation is not
asserted to be an arithmetic realization.

## Finite support certificate with exact unlimited tails

Retain ternary factors2<=u<=12. All factors u>=13 are allowed to survive
freely for the upper calculation. For the fixed prefix instance their total
A8 mass is exactly

    tail3=32/13286025.

For each retained u, initial quinary factors with u*k>38 are likewise given
payoff1, with fixed-instance exact total mass

    tail5=33008533907464/10136432647705078125.

At later primes retain factors only while current load remains<=38; their
complete remaining Haar tail receives payoff1. No infinite-depth mass is
dropped. Terminal loads<20 receive payoff0. A terminal load20--38 receives
payoff0 if its profile has been excluded in a support branch and1 otherwise.
The uniform row maximization in (NP3) computes each branch's exact upper
bound.

Use only the edges appearing in the retained certificate; their minimum K
is verified below. For a complete bipartite group of these edges between
profile sets L and R, a support without such edges must omit all of L or all
of R. The
certificate retains both possibilities as children. Every checked edge is
from (NP4)--(NP5), with the same fixed original selector interpretation.

The standalone verifier reconstructs the anchor and all rows, checks every
support split, checks the exact masks and upper value at every node, rejects
pending or unreachable nodes, and verifies the following complete result:

    2282 profiles,
    4492 normalized conditional rows,
    3501 disjunction-tree nodes,
    1751 accepted terminal cases,
    51431 checked cross-edge occurrences.

The maximum terminal upper bound is

    U=13530362084729802525722239237409731006113773442855176051085643442
      /841453987724678813030011126035327051417778569660355684928876953125
     =0.01607974087961289...,

and exact arithmetic verifies

    U<16079741/1000000000<m7.

This is an upper bound, not a claim to have determined the exact maximum
over all adaptive kernels and independent supports. Such exact optimality
is unnecessary for the strict inequality against m7.

The same support tree covers every reference position in the two remaining
ternary roots. There are9 choices for a mod27,9 for b mod27, and25 for their
common5 reference mod25:2025 configurations. They produce24 distinct pairs
of exact initial weight vectors. The conditional rows and all pair budgets
are independent of these positions. All2282 possible retained terminal
profiles are already present; a change of initial weights enables no omitted
profile. For each of the24 weight signatures, re-evaluating all1751 terminal
support cases gives a value at most the same U. This is42024 exact rational
leaf comparisons, with no choice of a favorable leaf for a new reference.

The initial masses are reconstructed from the210 literal survivors modulo675
of the eight original classes. Each reference-root partition consists of its
retained bins, complete ternary tail, and disjoint quinary overflow; its
masses sum to the literal root mass. Since the anchor only reads3-depth3 and
5-depth2, arbitrary deeper reference digits do not change these masses.
No tree transport or movement of an original class is needed.

The minimum K over all edges actually used in the certificate is4/3.
It is explicitly computed edge by edge; no same-profile minimum is applied
to edges whose nonternary profiles differ.

Acceptance depends only on exact row maximization and exhaustive support
disjunctions. No numerical solver or optimization-producing code is imported
by the verifier.

## Quantitative transfer to original uncovered integers

Let s(x) be the actual original23/29 surviving fibre Haar mass. In the actual
old live set define

    T={x:s(x)<1/924}.

No point of T has Q<=19. Two points of T cannot occupy the endpoints of a
certificate edge: their fibre masses would sum to less than1/462, whereas
K>=4/3 in (NP6) gives at least1/462. Thus T has the edge-free support property
used in every exhaustive branch. Null-mass profiles can be omitted without
affecting the estimate.

Comparison by the one enlarged adaptive source gives nu(T)<=U. Consequently

    nu({s>=1/924})>=delta=m7-U>0.

Its exact value is

    delta=690594100072110292293330858230605124768207607274922429435583437
          /4308244417150355522713656965300874503259026276661021106835850000000000
         =0.00000016029594266355407... .

Use nu<=(27/2)H and integrate the actual later Haar fibre. The original full
survivor mass is at least

    delta/[(27/2)*924]=delta/12474
      =690594100072110292293330858230605124768207607274922429435583437
       /53741040859533534790330156985163108553653093775069577286670392900000000000
      >1/80000000000.                          (NP7)

Since the original family is finite, its survivor set is a union of cells
in its finite CRT period. Positive mass supplies an uncovered integer.

## All ternary positions under the same original-anchor hypothesis

The opposite-root calculation covers one centre in root1 and the other in
root2, with every shallower and deeper reference position just described.
There are two remaining cases.

* If a=b mod3, [report478](478-independent-center-choices-with-one-varying-old-coordinate.md)
  applies with the only possibly differing old coordinate q=3. It allows
  each full original label to choose its centre independently and gives
  original Haar survivor mass greater than1/15592500.
* If the two centres have different ternary roots and one, say a, lies in
  root0, every later class using a and having3|d is already covered by the
  original0 mod3 class. Remove these redundant later classes. Every remaining
  later class shares the other centre b modulo its old cofactor: for3|d this
  follows from the retained choice, and for3 not dividing d it follows from
  the common nonternary prefixes. [Report473](473-a-finite-query-certificate-removes-the-coherent-cofactor-height-bound.md)
  gives original Haar survivor mass at least449287056937/6056623125000000000.
  Removing these redundant classes changes no original survivor.

Both bounds exceed1/80000000000. Together with the opposite-root certificate
they prove the stated arbitrary-ternary-reference conclusion. These are
separate scope reductions by existing ordinary results, not extra claims
proved by scanning the2025 reference prefixes.

## Exact replay and remaining restrictions

The [standalone verifier](../../frontier/cover-geometry/fixed_anchor_two_fibre.py)
replays the [support certificate](../../frontier/cover-geometry/fixed_anchor_two_fibre_certificate.json)
and reproduces the [exact result data](../../frontier/cover-geometry/fixed_anchor_two_fibre.json).
From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fixed_anchor_two_fibre.py
```

The default command verifies the retained result data without modifying it.
Use `--output PATH` to generate the result, `--input-dir DIR` to relocate the
source inputs, or `--certificate PATH` to select a support certificate.
The two numerical source inputs have identities:

* query_stoploss_completion.json:44f871684942eb7dceb37c55880c9f9a49244d8bdd60134670ad80d10a3c587d;
* common_law_mass_tail.json:3781704377f2ca6234ed55f3eff1a37d2f8665a3810b02c694aebdc2fc063cb4.

The remaining hypotheses are the eight original shallow classes, common
nonternary centre prefixes through the actual later-cofactor precisions, two
allowed centres per full later label, and support within the first nine odd
primes. Arbitrary other shallow anchor layouts, unrestricted independent old
phases, and arbitrary growing prime cores have not been reduced to this
situation.
The result imposes no absence restriction on higher original pure3/5 classes.
Source construction and source inequalities are ordinary proof inputs with
the cited attribution and boundaries; the exact checker does not establish
them from their numerical values, and does not run Lean.
