[Index](../../marked_head_profile.md) · [Actual mixed-centre interface](413-an-actual-mixed-centre-and-four-ternary-tails-admit-one-law.md) · [Concentrated centre](414-same-projection-transport-controls-concentrated-sharp-sources.md) · [Prefix-local transport](417-prefix-local-disagreement-extends-the-same-law-to-height-seven.md) · [Fast-decay obstruction](419-nonuniform-root-weights-cannot-repair-fast-child-laws.md)

# An arbitrary-centre interface and a common law on the fast-decay obstruction sources

The actual sharp sources S_K of report 419 admit one supported probability
with original independent-phase squared-load cost strictly below 2t_K at
every K>=3. A height-independent mixture works for every K>=4; a retained
exact rational law handles K=3. The margin is uniformly greater than 1/13.
Thus 419's obstruction to uniformly fast conditional child laws does not
obstruct these sources themselves.

The general sufficient interface used here allows arbitrary row imbalance
inside its central pair components. It requires actual full/pair laws with
the root pattern and prefix bounds stated below, together with a sufficiently
small full-law row-relabel budget. Those conditions have not been extracted
from arbitrary admissibility. This is ordinary analysis with exact finite
controls, not Lean certification or a resolution of unrestricted Erdős #7.

## One actual law before every original phase

Write points as (r,y), with r in {1,2,3,4} and y in Z/7^K, and read the
seven-adic digits lowest first. Original labels are all divisors 7^j and
5*7^j, for 0<=j<=K, including 1 and 5. Every label keeps its own independent
phase. Put

    t_K = 3-(K+2)3^-K,
    Gamma_K(nu) = max_(all original phases) E_nu ell^2.

Fix K>=1 and an actual source S. Suppose S supports these four probabilities:

* A full probability mu with root columns 0,...,4 each of mass 1/5, and
  mu(Y=u mod 7^j)<=5^-j for every specified prefix, 1<=j<=K.
* For each B in {23,24,34}, a probability eta_B supported on rows in B.
  Its root columns are {0} union B, each with mass 1/3. In a private root
  column r in B, all its mass is in row r. Its central component may use
  its two allowed rows in any proportions. Every specified prefix has
  eta_B-mass at most 3^-j.

All statements concern these same supplied probabilities. The trees, their
row choices, and their laws are selected before adversarial phases. In
particular no child law is optimized separately for a phase-dependent load.

Define the single common probability

    alpha=50/113,       b=21/113,
    nu=alpha*mu+b*(eta_23+eta_24+eta_34).             (S1)

It is normalized because alpha+3b=1, and remains supported on S. Define the
actual full-law disagreement profile

    D_j = max_u mu(row != 1, Y=u mod 7^j),          0<=j<=K.

Then the general interface gives

    Gamma_K(nu)
      <= 446/113
         + sum_(j=2)^K (2j+1)[(50/113)5^-j+(189/113)3^-j]
         + (150/113) sum_(j=0)^K (2j+1)D_j.        (S2)

An empty tail sum is zero. The reference part has the uniform bound

    446/113 + (50/113)(11/40) + 189/113
      = 2595/452 < 6.                             (S3)

No row cap or balance condition on the central eta_B components occurs in
S2. The budget D_j and the actual component hypotheses still matter.

## The arbitrary-centre root square

Keep the y coordinate of every mu point and change its row to 1; call the
result mu_bar. Leave all three pair laws unchanged and define nu_bar by S1.
This reference probability need not lie on S. Only the actual nu is claimed
as a supported solution; the reference is connected to it by an explicit
same-y coupling.

The root table of nu_bar is completely specified except for three masses:

    nu_bar(row 1, column c) = 10/113,    c=0,...,4;
    nu_bar(row r, column r) = 14/113,    r=2,3,4;
    nu_bar(row r, column 0) = d_r,      r=2,3,4.

Since row r occurs in only two pair components,

    0<=d_r<=14/113,      d_2+d_3+d_4=21/113.        (S4)

This polygon is the convex hull of the six permutations of (14,7,0)/113.
For a fixed original layout its expected root square is linear in d, so
it suffices to bound those six actual root tables. Row permutations among
2,3,4, accompanied by their private-column permutations, preserve the root
game. For the representative d=(14,7,0)/113, the entries below are 113 times
the maximum over the independent pure and mixed columns. The row index is
the phase at modulus 5, and the column index is the row of the phase at 35:

    (446  446  425  425)
    (368  416  360  360)
    (333  353  374  325)
    (305  318  297  353).

These finite values follow directly from the literal root expression

    sum_(r,y) q_(r,y)
      (1+[r=a]+[y=c]+[r=s and y=d])^2.              (S5)

Here a,s range over all five row residues and c,d over all seven column
residues; an absent row or column can only remove indicators. There are
5*7*5*7=1,225 original layouts per vertex. The retained program checks all
7,350 layouts, also comparing S5 with literal CRT residues at 1,5,7,35.
Thus every centre marginal in S4 has root cost at most 446/113.

## Higher-depth labels and the row-relabel error

For nu_bar, at depth j its pure-prefix mass is at most

    alpha*5^-j + (1-alpha)*3^-j.

Its row-1 prefix mass is at most alpha*5^-j; every other row belongs to
two pair components, giving at most 2b*3^-j. For j>=2,
alpha*5^-j<=2b*3^-j. In the literal squared-load expansion, the ordered
depth pairs with maximum depth j number 2j+1. Of the four label types
PP,PQ,QP,QQ, the first uses a pure-prefix cap and the other three use a
row-prefix cap. Every nonempty intersection is a cylinder at its literal
LCM, even when the original phases are independently chosen. Their total
contribution is therefore at most

    (2j+1)[alpha*5^-j + ((1-alpha)+6b)*3^-j]
      = (2j+1)[(50/113)5^-j+(189/113)3^-j].         (S6)

Combining the original four-label root square with S6 proves S2 for the
reference law without its final error term. The infinite sums used in S3
are sum_(j>=2)(2j+1)5^-j=11/40 and
sum_(j>=2)(2j+1)3^-j=1.

For the same-y coupling mu -> mu_bar, pure/pure indicators never change.
Each of the other three label-pair types can change only on a row-disagreement
point in one specified prefix at its maximal depth. Its probability is at
most D_j. Consequently, for every original layout simultaneously,

    |E_mu ell^2-E_mu_bar ell^2|
      <=3 sum_(j=0)^K (2j+1)D_j.                  (S7)

This is the prefix-local transport lemma of 417 applied to the actual
coupling (r,1,y). Multiplying S7 by alpha proves S2. No pair row is changed.

## The actual S_K sources fulfill the interface

For K>=3 put h=K-1. In root column zero use 414's actual concentrated
sharp source R_h; in column r=1,...,4 use 407's clean star-r source of
height h, with dominant row 1. This is exactly S_K of 419, with 5^K+2
points, its full standard five-tree, and all six pair-ternary trees.

Select mu uniformly on that full five-tree, choosing the smaller actual
row at either duplicated projection leaf. For each B in {23,24,34},
select the lexicographically first actual pair-ternary tree, also choosing
the smaller allowed row at a multiply labelled leaf. These are the existing
deterministic tree constructors, applied to S_K itself.

For B not containing 1, the only good root children are the admissible
centre and the two private children in B. Each private child has its actual
row-r ternary tree, so the selected pair probability has precisely the
root pattern required above. Complete uniform trees give all the pure-prefix
caps. This verifies S1 on actual support, without imposing five-decay on
the normalized conditional laws of nu.

The selected full mu has the exact disagreement profile

    D_0=(70*3^(K-3)-7)/5^K,
    D_1=(25*3^(K-3)-7)/5^K,
    D_j=max(5*3^(K-j-1),(5*3^(K-j)-7)/2)/5^K,  2<=j<K,
    D_K=5^-K.                                    (S8)

For D_0, the central non-row-1 count is 25*3^(h-2)-7 and each of the
three non-row-1 private stars contributes 5*3^(h-1); the row-1 star
contributes zero. At depth one the central count is the largest. Below
it, the central prefix counts are those of 417, while each private star
has at most 5*3^(K-j-1) such leaves in a prefix. At the last depth a
selected leaf contributes one. These counts establish S8 at every height;
the program also checks them against the actual constructed laws.

In particular,

    D_0 <= (70/27)(3/5)^K,
    D_1 <= (25/27)(3/5)^K,
    D_j <= (5/2)3^-j(3/5)^K,              2<=j<=K.

Since the weighted ternary sum from depth two is one, S7 yields

    (150/113) sum_j(2j+1)D_j
      <=(10625/1017)(3/5)^K.                     (S9)

The fixed actual probability S1 therefore satisfies

    Gamma_K(nu) <=2595/452+(10625/1017)(3/5)^K.

At K=8 its margin below the actual finite target is

    2t_8-[2595/452+(10625/1017)(3/5)^8]
      =148881233/1853482500 > 1/13.              (S10)

This margin strictly increases thereafter: (3/5)^K decreases and
(K+2)3^-K decreases. Thus the same fixed coefficients work for every K>=8.

## Exact finite completion at heights three through seven

For any one actual probability nu define, at depth j,

    p_j(u)=nu(Y=u mod 7^j),
    q_(j,r)(u)=nu(row=r,Y=u mod 7^j),
    A_(j,r)=max_u[p_j(u)+q_(j,r)(u)],
    Z_(j,r)=max_u q_(j,r)(u),
    B_j=max_r[A_(j,r)+2Z_(j,r)].

These exact profiles give the sufficient all-phase upper bound

    Gamma_K(nu)<=sum_(j=0)^K(2j+1)B_j.            (S11)

Here is a direct proof, including different mixed rows. Write P_i,Q_i for
the pure and mixed indicators at depth i. For i<=j let r,s be the mixed
rows at i,j. Their depth-pair product has expectation at most

    E[(P_i+Q_i)(P_j+Q_j)]
      <=A_(j,r)+(1+[r=s])Z_(j,s).

The first two terms involving P_j fit its one specified prefix and give
A_(j,r); the terms involving Q_j give Z_(j,s), with the Q_i Q_j term
zero when the rows differ. If r=s this is at most B_j. If r!=s and
Z_(j,s)<=Z_(j,r), use A_(j,r)+2Z_(j,r). Otherwise put P=max_u p_j(u):
the inequalities A_(j,r)<=P+Z_(j,r) and A_(j,s)>=P give
A_(j,r)+Z_(j,s)<=A_(j,s)+2Z_(j,s). A row-zero phase has an empty mixed
event and is dominated by any actual-row phase with the same prefix.
Finally there are 2j+1 ordered depth pairs with maximum j. This proves S11
for the same law and all independently selected original phases.

For K=4,...,7 use exactly S1 with the deterministic actual components above.
For K=3 use the 98-point rational law retained in the accompanying JSON,
with positive integer weights summing to 2,246. The finite results are:

| K | Actual probability | Exact upper in S11 | Margin below 2t_K |
|---|---|---|---|
| 3 | Retained rational law | 5856/1123 | 12584/30321 |
| 4 | S1 | 17488/3051 | 122/1017 |
| 5 | S1 | 733456/127125 | 593188/3432375 |
| 6 | S1 | 876619/151875 | 93893/455625 |
| 7 | S1 | 494841743/85809375 | 19308257/85809375 |

Every displayed margin exceeds 1/13. The retained height-three probability
is checked by exact rational arithmetic against the literal S_3 source;
the verification requires no optimizer or numerical tolerance. The fixed
recipe itself is not claimed to pass S11 at K=3. No value in this table is
claimed to be the source minimax or the exact original-phase maximum.

Combining the finite table with S10 gives one pre-phase selection rule on
all S_K, K>=3, with a uniform margin greater than 1/13.

## The profile surrogate loses information and needs cross-depth compensation

Even optimizing the whole S11 profile is not equivalent to optimizing
the original layout cost. Consider the existing seven-point type-B root
source, with columns translated by minus one from report 392:

    R={(1,0),(2,1),(2,2),(3,1),(3,3),(4,1),(4,4)}.

Every pair of rows has three projected columns, and the full projection
has five, so R satisfies all seven admissibility conditions at height one.
For an arbitrary supported law write x=nu(1,0), y_r=nu(r,1), z_r=nu(r,r)
for r=2,3,4, and Y=sum_r y_r, Z=sum_r z_r. Thus x+Y+Z=1.
Put b=B_1. The definition of B_1 gives, without any symmetry assumption,

    4x<=b,       4z_r<=b,       Y+y_r+2z_r<=b.

Summing the last three inequalities gives 4Y+2Z<=3b. Consequently

    1=x+Y+Z <= b/4+3b/4+Z/2 <= 11b/8.

The minimum possible B_1 is therefore at least 8/11. The actual law

    x=2/11,       y_r=1/11,       z_r=2/11

has B_0=20/11 and B_1=8/11, attaining this bound. Moreover every law
has B_0=1+3 max_r nu(row r)>=2-x. Together with x<=b/4 and b>=8/11,
this proves

    B_0+3B_1 >= 2+(11/4)b >= 4.

The displayed law also attains four. Thus the two exact profile minima are

    min_nu B_1=8/11>2/3,       min_nu(B_0+3B_1)=4.

The root gain 2-B_0=2/11 exactly compensates the weighted depth-one
excess 3(B_1-2/3)=2/11. Requiring B_j<=2*3^-j separately would therefore
reject an admissible source that satisfies the weighted target 2t_1=4.
This obstruction persists at every height: attach all seven-ary tails,
R_K={(r,c+7t):(r,c) in R, 0<=t<7^(K-1)}. These sources are admissible,
and every supported law has a root marginal on R with B_1>=8/11.

[Report 392, section 2](392-root-optimal-laws-do-not-tensorize-the-full-layout-bound.md)
already proves that the original root minimax on this same source is
631/166. Translating the columns transports every original independent
phase and preserves both objectives. Hence the optimized profile bound
has the exact excess 4-631/166=33/166 over the true minimax. The point of
this example is the failure of separate depth targets and of profile
tightness; it does not refute the weighted profile target or the desired
original-layout inequality.

## Relation to the existing interfaces

Report 419 excludes all root mixtures with uniformly faster-than-ternary
conditional tails on these same actual S_K. S1 retains genuine ternary
pair components and therefore does not satisfy that obstructed condition.
Its success concerns the original phase game; it is not a repair of the
fast-decay interface.

Report 413 supplies a different sufficient recipe with a normalized
five-decaying centre whose row cap is at most 18/65. In the new fixed law,
the central column has mass 31/113, and its conditional row-1 mass is

    (10/31)[1-(25*3^(K-3)-7)/5^(K-1)] ->10/31>18/65.

Thus the new selected centre law does not meet that row-cap hypothesis
at sufficiently large heights. This comparison is between the selected
interfaces and probabilities; it does not exclude another successful
probability furnished by a different theorem on the same source.

The reusable advance over 414/418 is the arbitrary-centre pair interface
with a verified full-law disagreement budget, and its all-height consumer
on 419's single-+2/four-clean family. The extraction of this interface or
another sufficient law from every admissible sharp source remains open.

## Reusable verification

[`single_surplus_source_common_law.py`](../../frontier/cover-geometry/single_surplus_source_common_law.py)
validates actual component support, normalization, root conditions and
every pure-prefix cap; computes the actual full-law disagreement profile;
and checks the general bound and the finite laws. Its public helpers include
`verify_interface`, `profile_bound`, `actual_components`,
`actual_profile_formula`, and `analytic_bound`.
The seven-point control reuses the existing type-B source and checks the
attaining profile; the universal lower bounds follow from the inequalities
above, not from testing one probability.

[`single_surplus_source_height_three.json`](../../frontier/cover-geometry/single_surplus_source_height_three.json)
contains only the exact height-three probability and its profile upper bound.
The reusable verifier rejects unsupported points, incorrect weights,
incorrect root geometry, missing prefix decay, and a false stored upper bound.
It uses explicit exceptions, with the same checks active under `-O`.

From the repository root:

    python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/single_surplus_source_common_law.py
    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/single_surplus_source_common_law.py

The finite checks establish actual correspondence with the constructors
and the original layout game. The unbounded-height conclusion follows from
the counting, transport and monotonicity arguments above.
