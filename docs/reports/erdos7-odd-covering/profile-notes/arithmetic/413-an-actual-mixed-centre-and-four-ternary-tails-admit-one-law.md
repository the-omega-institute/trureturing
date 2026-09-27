[Index](../../marked_head_profile.md) · [Recursive source](401-a-recursive-minimum-source-has-one-law-at-every-height.md) · [Row concentration](407-limits-of-stationary-row-mixtures-and-finite-signature-summaries.md) · [Five-tree criterion](412-a-sharper-five-tree-law-crosses-the-ternary-root-obstruction.md)

# An actual five-decaying centre and four monochromatic ternary tails

Ordinary analytic result and exact research constructor; no Lean claim.
This is a sufficient class of actual supported common laws for the
original finite game of report 400. It does not derive this class from
arbitrary admissibility, and does not decide unrestricted Erdős #7.

The root identity and literal-LCM shell expansion are reused from 398,
401 and 408. The new synthesis is the supported five-column law with a
five-decaying mixed centre and four separately supplied monochromatic
ternary tails, including the parameter choice below. No capability
signature is treated as an actual monochromatic-tree witness.

## Actual hypotheses and one common probability

Fix K>=2, h=K-1 and an actual source R in {1,2,3,4} times Z/7^K.
Use five distinct root columns c_0,c_1,...,c_4; their numerical labels
and the private-row names may be permuted. Assume:

* Column c_0 supports an actual probability eta on its height-h tail.
  Every specified pure seven-adic tail prefix of depth j has eta-mass
  at most 5^-j, for 1<=j<=h.
* Write a=max_r eta(row r). For the principal theorem assume
  1/4<=a<=18/65. The lower bound is automatic for a four-row probability.
* For each r=1,...,4, the actual cell (row r, column c_r) contains a
  complete ternary tail tree T_r of height h. These four actual trees
  may differ arbitrarily, and need not share digit sets.

There is no additional uniformity requirement on eta. In particular,
it need not be the uniform law on one labelled five-tree. Its support
may use multiple rows over the same projected leaf and may mix
different five-trees. All its required prefix masses belong to that
one actual probability.

The simplest common-law recipe uses the same integer weights at every
height and for every source satisfying these actual conditions:

    alpha=65/197,   p=33/197,   alpha+4p=1.

Put mass alpha on eta in column c_0 and mass p on the uniform law of
T_r in its private row/column cell, for each r. Call the resulting
actual supported probability nu. It is fixed before the phases at
all divisors d|5*7^K are independently selected. No phase coupling or
shared-centre restriction is imposed on the adversary.

Let

    t_K=sum_(j=0)^K (2j+1)3^-j=3-(K+2)3^-K,
    Gamma_(1,K)(nu)=max_(a_d) E_nu (sum_(d|5*7^K) 1_(x=a_d mod d))^2.

Then this fixed-weight law satisfies

    Gamma_(1,K)(nu)
       <=6-(54-195a)/197-396(K+2)/(197*3^K),
    2t_K-Gamma_(1,K)(nu)
       >=(54-195a)/197+2(K+2)/(197*3^K)>0.

In particular, discarding the first nonnegative gain gives the source
independent finite-height margin 2(K+2)/(197*3^K). These are actual
supported probabilities on the stated source, not independent
optimizers for individual divisor labels.

## A parameterized form and its finite-height comparison

More generally, choose any declared row cap A with

    a<=A<=18/65,

and set

    alpha=7/(19+8A),   p=(3+2A)/(19+8A).

The same construction gives

    Gamma_(1,K)(nu)
      <= (324+209A)/(57+24A)-3alpha(A-a)-12p(K+2)3^-K,
    2t_K-Gamma_(1,K)(nu)
      >= (18-65A)/(57+24A)+3alpha(A-a)
           +(8A-2)/(19+8A)*(K+2)3^-K > 0.

The fixed integer recipe above is A=18/65. Using the actual maximum
A=a instead gives

    alpha=7/(19+8a),   p=(3+2a)/(19+8a),   alpha+4p=1.

Then

    Gamma_(1,K)(nu) <= U_K(a)
      := (324+209a)/(57+24a) - 12p(K+2)3^-K,

and the exact certified target margin is

    2t_K-U_K(a)
      = (18-65a)/(57+24a)
          + (8a-2)/(19+8a) * (K+2)3^-K > 0.

Both summands are nonnegative on the stated interval. At a=1/4 the
first is 1/36. At a=18/65 the second is strictly positive for every
finite K. They cannot both vanish. Thus the same source law beats
the finite target at every allowed height; no limit-only comparison
is used. At a=1/4 its certified margin is exactly 1/36 for every K.

## The original four-label root square

Write a_r=eta(row r), so beta_r=p+alpha*a_r. The central cell in row r
has mass alpha*a_r, and its private cell has mass p. The central column
mass is alpha and every private column mass is p.

For arbitrary phases at divisors 5,7,35, selecting row u, column v and
joint cell (s,d), the expectation of the four-label root square,
including divisor one, is exactly

    1+3beta_u+3C_v+2q_(u,v)
       +(3+2[u=s]+2[v=d])q_(s,d).

Let q=alpha*a and beta_max=p+q. The maximum is

    g=1+3beta_max+12p=1+15p+3alpha*a.

For completeness, the root cases retain the common row/column data:

| Mixed cell type | Pure column type | Upper bound apart from 1+3beta_max |
|---|---|---|
| private | private | 12p |
| private | central | 3alpha+2q+5p |
| central | central | 3alpha+9q |
| central | private | 5p+5q |

For A=a our parameter choice gives 3alpha+2q=7p exactly. Also

    3alpha+9q<=12p  iff  a<=5/13,
    5q<=7p         iff  a<=1.

Both hold on a<=18/65. In particular q<=p. Empty columns or cells
only remove the corresponding terms and satisfy the same bound;
for an empty mixed cell use 3alpha+2p<=12p. Row-zero phases vanish
and replacing them by an actual row can only increase the load.
Finally choose a row attaining a and its private pure and mixed
column. This gives g, proving the claimed exact root maximum for
every actual eta under these conditions.

For a declared cap A>=a, the same inequalities hold with q<=alpha*A;
the exact root maximum still uses the actual a. Its value is less
than the A-based expression by 3alpha(A-a). All higher-depth caps
are unchanged, proving the parameterized and fixed-weight versions.

## The higher-depth budget belongs to the same law

At total depth j>=2, a prefix belongs either to the central column,
where its pure and joint masses are at most alpha*5^{1-j}, or to a
private column, where they are at most p*3^{1-j}. The latter statement
uses the uniform probability on the actual complete ternary tree.

Since

    alpha/p=7/(3+2a),
    5/3 <= alpha/p <= 25/9,

throughout the stated interval, the common pure and joint cap is

    alpha/5,              j=2;
    p*3^{1-j},            j>=3.

The j>=3 comparison follows from the j=3 inequality and gains a factor
3/5 at every following depth. In the literal square expansion, every
nonempty intersection is a cylinder at its original LCM. There are
2j+1 ordered exponent pairs at maximum seven-adic depth j, with one
pure/pure and three row-constrained types. Thus all independently
chosen original phases obey

    Gamma_(1,K)(nu)
      <= g + 4alpha + 4p*sum_(j=3)^K (2j+1)3^{1-j}
       = g + 4alpha + 12p(t_K-23/9)
       = U_K(a).

When K=2 the displayed sum is empty and t_2=23/9 exactly. The formula
therefore includes the bottom height without inserting fictitious
deeper levels.

## A simpler fixed-weight alternative

Under the same actual support and prefix assumptions, suppose instead

    a <= 4/15+(2/15)(K+2)3^-K.

This threshold is below 1/3 for every K>=2. Set alpha=5/17 and p=3/17.
The same root cases give exact g=(62+15a)/17. Every depth j>=2 now
has common pure/joint cap p*3^{1-j}, because alpha/5=p/3. Therefore

    Gamma_(1,K)(nu) <= U_K^simple(a)
      := (36t_K+15a-10)/17,
    2t_K-U_K^simple(a)
       = (4-15a+2(K+2)3^-K)/17 >=0.

In particular a<=4/15 gives a strict finite-height margin for every
K>=2. The optimized law extends the height-independent sufficient
row cap to 18/65>4/15. It does not dominate the simple law at every
finite height. Either probability may be selected after examining
the actual source data and before seeing the adversarial phases.

## Applying the result to the concentrated clean-star sharp sources

This application reuses the construction in 407 section 2 and the
sharp-minimum source in 401; the concentration obstruction itself is
not a new result.

At height K>=2 put h=K-1. Take the 401 source R_h in root column zero.
In column r=1,...,4 place 407's clean star-r source of height h, with
dominant row one. In each of those clean stars, the centre row r
contains the actual standard ternary tree {0,1,2}^h.

The source has (5^h+2)+4*5^h=5^K+2 actual row/leaves, and its projection
is exactly the standard full five-tree. Each row pair has its two
corresponding private good children and the admissible central child,
so all six pair-ternary conditions hold. Report 400 gives sharpness.

In the central source choose the uniform five-tree projection, and
split its one triply labelled leaf equally over its three actual rows.
Then every pure prefix has exact mass 5^-j and

    a_K=1/4+5^{-(K-1)}/12 <=4/15.

Both constructors therefore apply to this same actual family. For
the simple law,

    U_K^simple(a_K)
      =407/68-(36/17)(K+2)3^-K+5^{2-K}/68,
    2t_K-U_K^simple(a_K)
      =1/68+(2/17)(K+2)3^-K-5^{2-K}/68 >1/68.

The last inequality follows from 8(K+2)5^{K-2}>3^K for K>=2. It holds
at K=2 and its left/right ratio strictly increases.

This family defeats every 412 uniform full-five selection once K>=3:
its projection has exactly 5^K leaves, so every full-five selection
uses them all. The four clean columns force

    beta_1 >=4/5-(3/5)(3/5)^{K-2},   M_1=1/5,
    beta_1+3M_1 >=7/5-(3/5)(3/5)^{K-2}.

At K=3 this lower bound is 26/25>c_3=10144/10125; for K>=4 it is at
least 148/125>11/10>c_K. The new supported law succeeds by changing
the probability on the same source, rather than trying another
uniform full-five labelling.

An optional family-wide choice uses the simple law at K=2,3 and the
optimized law at K>=4. Its certified margin exceeds 1/40 at every
height: the first two exact margins are 8/153 and 77/2295. For K>=4,
a_K<=1/4+1/1500=94/375, so the optimized first margin term is at least
(18-65*(94/375))/(57+24*(94/375))=640/23631>1/40, and its second term
is nonnegative. This choice is made solely from K before any phases.

## Remaining extraction boundary

A clean star-r capability signature does not imply a monochromatic
row-r ternary tree. Already at height one, row counts 2,1,1,1 have
that star signature but only two leaves in the centre row. Consequently
the actual T_r witnesses in this theorem cannot be replaced by the
finite signatures in 403 or 407. Nor does arbitrary sharp-minimum
admissibility supply the required central probability eta. Extracting
these actual structures, or constructing another suitable law without
them, remains an independent obligation.

## Exact research program

The program [ternary_private_common_law.py](../../frontier/cover-geometry/ternary_private_common_law.py) exposes:

* make_common_law: validates actual central support, rational masses,
  every five-decay prefix cap, the selected finite row threshold,
  all four actual complete ternary trees, and distinct root columns;
  then returns one actual common probability. In optimized mode,
  parameter_cap=18/65 selects the fixed 65/197,33/197 recipe; leaving
  the parameter cap unspecified uses the actual central row maximum.
* verify_common_law: reconstructs that probability, exhausts all 1225
  independent root phase choices including absent rows/columns, and
  checks every actual deeper pure and joint prefix mass against the
  same-law shell bound.

Controls include the concentrated sharp source at K=2,3,4,5 in both
modes and with the fixed integer weights, different actual central
five-trees and private ternary trees
at K=2,3,4, the optimized a=18/65 boundary, and equality at the simple
finite-height row threshold. Nineteen invalid inputs are rejected with
explicit checks active under python -O. Normal and -I -S -B -O outputs
match exactly. These finite controls validate implementation and
examples; the arbitrary-height claim is the analytic proof above.

Run the exact controls from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/ternary_private_common_law.py
```
