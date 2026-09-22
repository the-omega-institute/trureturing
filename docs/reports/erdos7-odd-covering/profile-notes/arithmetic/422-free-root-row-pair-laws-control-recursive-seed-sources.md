[Index](../../marked_head_profile.md) · [Clean signatures](407-limits-of-stationary-row-mixtures-and-finite-signature-summaries.md) · [Mixed-centre interface](413-an-actual-mixed-centre-and-four-ternary-tails-admit-one-law.md) · [Prefix-local transport](417-prefix-local-disagreement-extends-the-same-law-to-height-seven.md) · [Fast-decay obstruction](419-nonuniform-root-weights-cannot-repair-fast-child-laws.md) · [Monochromatic private-root interface](421-single-surplus-sources-admit-a-common-law-beyond-fast-decay.md)

# Full/pair prefix caps control a common law without prescribed root geometry

Full and pair probabilities need no prescribed relationship between their
root columns. Their pure-prefix caps alone give a reference root upper
bound of four, even with arbitrary allocation between the two permitted
rows of every pair. The fixed coefficients

    alpha=5/11,       b=2/11,       alpha+3b=1

give a reference root-plus-tail ceiling 507/88<6, together with the same
explicit full-law row-relabel error used in 417 and 421.

Every admissible source supplies the full and pair components required by
this bound; its additional quantitative condition is the actual full-law
disagreement budget. This enlarged interface has an all-height consumer beyond 421's
private-row requirements. A recursive (2,1,1,1) seed construction gives
sharp admissible sources with no possible three-private-row capacity
matching, and on which every five-decaying conditional-root mixture fails
once K>=6. Nevertheless the new fixed probability succeeds for every K>=3,
with a uniform target margin greater than 1/20.

The fixed mixture architecture nevertheless fails on an existing height-one
seven-point source: its optimum over all four reference rows and all
permitted components is 49/11, exceeding the target four by 5/11.

These are ordinary analytic results with exact finite controls. They are
not Lean-certified, and do not prove a common-law theorem for arbitrary
admissible sources or decide unrestricted Erdős #7.

## Actual component hypotheses and the general bound

Work on rows {1,2,3,4} and seven-adic coordinates y mod 7^K, K>=1, with
lowest digits first. For one actual probability nu let

    Gamma_K(nu)=max_(all original phases) E_nu ell^2,
    ell=sum_(d|5*7^K) 1_(x=a_d mod d),
    t_K=3-(K+2)3^-K.

Divisors 1 and 5 are included, and every original divisor keeps its own
independently selected phase. Suppose an actual source S supports:

* A probability mu with mu(Y=u mod 7^j)<=5^-j for every specified
  prefix, 1<=j<=K.
* For each B in {23,24,34}, a probability eta_B supported on the rows in B,
  with every specified depth-j prefix of mass at most 3^-j.

There is no prescribed root-column support, no equality requirement for
root-column masses, and no restriction on the allocation between the two
allowed rows of eta_B. Each probability is supplied on
actual support before all phases are selected. Define one common law

    nu=(5/11)mu+(2/11)(eta_23+eta_24+eta_34),       (R1)

and the actual full-law disagreement profile

    D_j=max_u mu(row != 1,Y=u mod 7^j),  0<=j<=K.

Then

    Gamma_K(nu)
      <=4+sum_(j=2)^K(2j+1)[(5/11)5^-j+(18/11)3^-j]
         +(15/11)sum_(j=0)^K(2j+1)D_j.            (R2)

The reference part in R2 is bounded uniformly by

    4+(5/11)(11/40)+18/11=507/88.                 (R3)

Admissibility supplies actual uniform full-five and pair-ternary tree
probabilities with these prefix caps. It does not by itself supply the
small disagreement budget needed to beat the finite target through R2.

## A sharp uniform reference root bound from the caps alone

Move each mu point (r,y) to (1,y), obtaining mu_bar, and leave all eta_B
unchanged. Define nu_bar by R1 with mu_bar. This is a comparison probability;
nu is the supported probability on the actual source. The two are joined
by the explicit same-y coupling on their full components.

For a root layout write

    f(r,y)=(1+[r=a]+[y=c]+[r=s and y=d])^2,        (R4)

where a,s range over all five row residues and c,d over all seven column
residues. For seven numbers v_y, let Top_q(v) be the sum of their q
largest values. A normalized probability with each root-column mass at
most 1/q has expectation at most Top_q(v)/q: shifting mass from a smaller
value to an unsaturated larger one cannot decrease the expectation.
The full root marginal has cap 1/5, and each pair root marginal has cap
1/3. Maximizing the row choice within a pair before applying this column
bound gives, for each fixed layout,

    E_nu_bar f
      <=(1/11)Top_5((f(1,y))_(y=0)^6)
        +(2/33)sum_(B in {23,24,34})
                    Top_3((max_(r in B) f(r,y))_(y=0)^6).       (R5)

The maximization in R5 is a uniform bound on all supplied probabilities;
the actual components are not replaced after observing the layout. Its
finite root bound is attained over the allowed root allocations by using
the five best full columns, the three best columns for each pair, and an
allowed maximizing row in each selected pair cell.

For a direct calculation, let t,u be distinct rows from {2,3,4}. Let A
denote the top-five full average and P the average of the three top-three
pair averages. The five possible actual-row cases have simultaneous bounds:

| Row phases (a,s) | A | P | (5/11)A+(6/11)P |
|---|---|---|---|
| (1,1) | 32/5 | 2 | 4 |
| (1,t) | 5 | 28/9 | 131/33 |
| (t,1) | 13/5 | 40/9 | 119/33 |
| (t,t) | 8/5 | 6 | 4 |
| (t,u) | 8/5 | 5 | 114/33 |

Each displayed pair A,P is attained when c=d. For example, in the (1,t)
case the full costs are one 9 and six 4's, giving A=5. Two pairs contain t:
their three selected costs are 9,1,1; the third pair has costs 4,1,1.
This gives P=(11+11+6)/9=28/9. If c!=d, the first two selected triples
become 4,4,1, while the third is unchanged. In the five row cases in the
table's order, the separated-column values (A,P) are respectively

    (6,2), (5,8/3), (11/5,40/9), (8/5,50/9), (8/5,43/9).

They follow from the same four indicators in R4: there are at most two
exceptional columns, with the other columns at the constant row cost.
Each is coordinatewise bounded by its coincident-column pair in the table.
These cases prove R5<=4 without relying on enumeration.

For a,s in {1,2,3,4}, maximizing R5 over the independently selected c,d
gives this table, multiplied by 33:

    (132  131  131  131)
    (119  132  114  114)
    (119  114  132  114)
    (119  114  114  132).

Row-zero mixed phases vanish and are dominated by an actual-row phase
with the same prefix. Every one of the seven columns is included. The program
checks all 1,225 original layouts via their literal CRT phases at
1,5,7,35, constructs an attaining root allocation for R5 for each layout,
and verifies the displayed maximum four. Thus four is the sharp uniform
upper bound over the permitted reference root marginals.

This uniform maximum does not assert equality for every fixed reference
probability, and it is not a bound of four on the original unrelabelled
nu. The latter receives its explicit transport error in R2.

## Higher depths and the same actual coupling

At depth j the reference law has pure-prefix bound

    (5/11)5^-j+(6/11)3^-j.

Row 1 has prefix bound (5/11)5^-j. Every other row lies in only two pair
components, giving row-prefix bound (4/11)3^-j. For j>=2 the latter also
dominates the row-1 bound. At maximum depth j there are 2j+1 ordered depth
pairs; pure/pure intersections use the pure bound, and the other three
label types use the row bound. The original LCM expansion therefore gives

    (2j+1)[(5/11)5^-j+(18/11)3^-j].               (R6)

This reasoning allows all original phases independently. The pair laws
used at every depth are the same probabilities appearing in R1.

For the coupling (r,y)->(1,y) of mu and mu_bar, pure/pure terms do not
change. Each other label-pair term can change only on a disagreement
point in one specified maximal-depth prefix. The prefix-local lemma of
417 gives, simultaneously for every layout,

    |E_mu ell^2-E_mu_bar ell^2|
      <=3 sum_(j=0)^K(2j+1)D_j.

Multiplying by 5/11 proves R2. Only the full component is relabelled;
all pair row allocations remain actual and unchanged.

The selected coefficient is also optimal for this particular robust
root-plus-geometric-tail bound. With a general full weight alpha and
equal pair weights (1-alpha)/3, the higher-depth comparison used above
is valid for 0<=alpha<=50/77. The two root layouts centered respectively
at (row 1,column 0) and (row 2,column 0), with row allocation maximized
as in R5, give the two affine lower bounds on that proposed total ceiling:

    5+(67/40)alpha,       9-(57/8)alpha.

Their maximum is minimized where they meet, at alpha=5/11, with value
507/88. R5 and R6 attain that upper bound on the reference ceiling.
This is an optimization of the stated estimate, not of the actual-source
minimax or of all probability constructions.

## Admissibility supplies the components without a root-extraction condition

In an arbitrary admissible source, select any actual labelled complete
five-ary projection tree for mu and give its leaves equal mass. For each
B in {23,24,34}, independently select an actual pair-supported ternary
tree and give its leaves equal mass. The seven tree conditions of report
400 provide all four selections, and uniform tree probabilities give
the required prefix caps. They may use different root columns and
different deeper digit trees. They are then combined once, before phases,
using R1. Any selected full law with a sufficiently small actual D_j
budget proves the target through R2.

Thus neither monochromatic private tails, capacity matching, nor a star
pattern of clean root signatures is needed for the general interface.
The remaining quantitative extraction problem is to find an appropriate
full law or another sufficient comparison when its disagreement budget
is large. General admissibility alone is not claimed to settle that problem.

## A recursive seed source beyond the private-row interface

For each i in {1,2,3,4}, let (a,b,c) be the other rows in increasing order.
At tail height one label the five columns 0,...,4 by

    (i,i,a,b,c).                                  (R7)

For h>=1, construct C_(i,h+1) from three copies of C_(i,h) in columns
0,1,2 and pure-row-1 complete five-trees in columns 3,4. This uses the
(2,1,1,1) seed already noted in 413 and the concentration recursion of
407. Explicitly, for a digit word of length h, use R7 at the final digit
if all preceding digits lie in {0,1,2}; otherwise assign row 1.

Every C_(i,h) is clean with 5^h points and full projection F_h. At height
one, a pair containing i has three leaves and any other pair has two,
so the signature is star-i. Three continuing copies preserve this
signature at every higher node, regardless of the other two children.

For K>=3, h=K-1, put the unchanged actual R_h of 414 in root column zero,
and C_(i,h) in column i. Call the resulting source S_tilde_K. It has
5^K+2 points. Each pair has the central good child and its two private
star children; its full projection is F_K. It is therefore admissible
and sharp minimum by 400.

Select mu by the existing uniform five-tree constructor, taking the smaller
actual row at duplicated leaves, and select eta_23,eta_24,eta_34 by the
existing least-good-child uniform ternary-tree constructor. These fixed
actual probabilities fulfill R1. In a private child, eta_B in fact assigns
2/3 of its conditional mass to its own row and 1/3 to the other row of B;
the general theorem does not need this additional ratio.

## Exact disagreement profile and all large heights

The full-law profile of S_tilde_K is exactly

    D_0=(70*3^(K-3)-7)/5^K,
    D_1=(25*3^(K-3)-7)/5^K,
    D_j=max(5*3^(K-j-1),(5*3^(K-j)-7)/2)/5^K,   2<=j<K,
    D_K=5^-K.                                     (R8)

The four new clean children have respectively 3,4,4,4 non-row-1 seed
leaves, each multiplied by 3^(h-1). Their combined count is therefore
15*3^(h-1), the same total as in 421. The unchanged centre contributes
25*3^(h-2)-7, proving D_0, and dominates any individual new clean child,
proving D_1.

Below the root, a new outer clean child contributes at most
4*3^(K-j-1) non-row-1 leaves per prefix. The centre is still 414's R_h:
its own internal original clean-star children contribute the term
5*3^(K-j-1), and its exceptional branches contribute
(5*3^(K-j)-7)/2. Thus the maximum in R8 remains necessary. For example,
at K=3 the prefixes y=21 and y=28 at depth two lie in the centre's
internal private columns and each contain five non-row-1 leaves, giving
D_2=5/125, although a new outer clean prefix contains at most four.
The final depth has one selected point per projected leaf. These counts
establish the all-height formula, which is also checked on the actual
constructed probabilities at K=3,...,7.

As in 421,

    D_0<=(70/27)(3/5)^K,
    D_1<=(25/27)(3/5)^K,
    D_j<=(5/2)3^-j(3/5)^K,   2<=j<=K.

Since sum_(j>=2)(2j+1)3^-j=1, R2 gives the simpler bound

    Gamma_K(nu)<=507/88+(2125/198)(3/5)^K.         (R9)

At K=8 its margin below the actual finite target is

    2t_8-[507/88+(2125/198)(3/5)^8]
      =99823733/1804275000>1/20.                 (R10)

The margin increases thereafter: both (3/5)^K and (K+2)3^-K decrease.
Thus the same fixed law R1 succeeds for every K>=8.

## Exact completion at the remaining heights

Use the sufficient profile bound S11 of 421 for the same actual nu:

    A_(j,r)=max_u[nu(Y=u mod 7^j)+nu(row=r,Y=u mod 7^j)],
    Z_(j,r)=max_u nu(row=r,Y=u mod 7^j),
    B_j=max_r[A_(j,r)+2Z_(j,r)],
    Gamma_K(nu)<=sum_j(2j+1)B_j.

The all-independent-phase proof of that bound is retained in 421. No
optimizer or approximate certificate is needed here; the probabilities
are generated by the same fixed constructors at every height.

| K | Exact sufficient profile upper | Margin below 2t_K |
|---|---|---|
| 3 | 13271/2475 | 1987/7425 |
| 4 | 601363/111375 | 50387/111375 |
| 5 | 203039/37125 | 158149/334125 |
| 6 | 27503599/5011875 | 819217/1670625 |
| 7 | 688102709/125296875 | 62647291/125296875 |

Each margin exceeds 1/20. Together with R10, this proves the same actual
fixed recipe on every S_tilde_K, K>=3, with a uniform margin greater than
1/20. The table contains sufficient upper bounds, not asserted exact
values of Gamma_K or source minimax values.

## Why the older private-row and five-decay interfaces cannot supply this law

For a tail projection A define its ternary prefix capacity to be the
largest subprobability mass supported on A with absolute prefix caps
3^-j, including root mass at most one. This is the support-indicator
specialization of the existing laminar-capacity optimization in
[problem 54](../../problem-details/54-depth-profile-head-laws-with-unrestricted-original-tails.md).
The finite-tree recurrence is

    C_0(A)=1_(A nonempty),
    C_h(A)=min(1,(1/3)sum_c C_(h-1)(A_c)).         (R11)

Indeed each child can carry at most one third of its normalized capacity;
the child subprobabilities can be combined and, if needed, scaled to the
root cap. Thus C_h(A)=1 is equivalent to the existence of a normalized
supported prefix-capped probability. No new foundational capacity theorem
is claimed. Absence of a monochromatic ternary tree alone would not imply
capacity below one; R11 checks the stronger probability condition.

For h>=2, the four clean children have these row capacities:

    (1  1/3  1/3  1/3)
    (1  2/3  1/3  1/3)
    (1  1/3  2/3  1/3)
    (1  1/3  1/3  2/3).                          (R12)

At height one the capacities are the row counts divided by three,
truncated at one. For a non-row-1 set, the three continuing copies in
R11 preserve that value forever. Row 1 gains 2/3 from the other two
children and has capacity one from height two onward. This proves R12.

The only capacity-one row in any clean column is row 1. Including the
one exceptional central column, the graph of capacity-one joint cells
therefore has matching number at most two. The older 421 interface needs
three distinct private columns in three distinct private rows, each
carrying a normalized ternary prefix-capped conditional probability.
It would give a matching of size three. Hence no choice of probabilities,
root-column order or row names can fulfill that older interface on these
sources. R1 succeeds by keeping pair-supported mass in both rows.

These sources also retain the fast-decay obstruction. In the centre the
number of non-row-1 projection leaves is 25*3^(h-2)-7; in the new clean
children it is respectively 3*3^(h-1) and 4*3^(h-1). The central count
dominates. Every normalized child law with prefix caps 5^-j must be uniform
on the 5^h projected leaves; splitting duplicated central leaves cannot
change its row-1 mass. Thus every mixture of such child laws, with arbitrary
root weights, has row-1 mass at least

    1-delta_h,       delta_h=(25*3^(h-2)-7)/5^h.

The same fixed centered-layout average used in 419 gives the actual
original-phase lower bound

    Gamma_K >=(4-3delta_h)sum_(j=0)^K(2j+1)5^-j
             >=307459328/48828125>6>2t_K,         K>=6.          (R13)

This excludes the stated family of five-decaying conditional laws, not
the actual sources. Their successful fixed law R1 is already proved above.

## A sharp height-one boundary for the fixed mixture architecture

Use the existing type-B source from 390 and 398, also used in 392 and
421 after the stated column relabelling:

    R={(1,0),(2,1),(2,2),(3,1),(3,3),(4,1),(4,4)}.

Its five-column projection and its three-column projection on every pair
of rows make it admissible at K=1. For each reference row a in {1,2,3,4},
allow arbitrary actual component probabilities satisfying the hypotheses
of this report: mu has column cap 1/5, and eta_B has column cap 1/3 for
each two-element subset B of {1,2,3,4}\{a}. Retain the fixed weights
5/11 and 2/11, and choose all components before the original phases.
Then the exact restricted optimum is

    min_(a,mu,(eta_B)) Gamma_1((5/11)mu+(2/11)sum_B eta_B)
      =49/11=4+5/11.                              (R14)

This is a lower bound on the actual phase cost of every law in that
architecture, independently of the sufficient transport estimate R2.

Write p_1=(1,0) and p_r=(r,r) for r=2,3,4 for the four private points,
and y_r=nu(r,1) for the three shared-column masses. Normalization and the
caps force mu to give each of its five available columns mass 1/5, and
each eta_B to give each of its three available columns mass 1/3. Each
private point in a non-reference row occurs in exactly two selected pair
components. Consequently every permitted mixture satisfies

    nu(p_a)=1/11,       nu(p_r)=7/33 for r!=a,
    y_2+y_3+y_4=3/11,
    y_a<=1/11 when a!=1.                          (R15)

The last inequality holds because the reference row receives no pair
component. The centered original layout at a spoke private point p_r
has phases (0,r,r,r) at divisors (1,5,7,35), and its expectation is

    1+15nu(p_r)+3y_r.                            (R16)

If a=1, average R16 over the three spokes. R15 makes this average exactly
49/11. If a is a spoke, average over the other two spokes. Their shared
mass is at least 3/11-1/11=2/11, so this average is at least

    1+15(7/33)+(3/2)(2/11)=49/11.

The maximum over all original layouts dominates either average, proving
R14's lower bound for every reference and every permitted component.

For attainment, keep the forced column masses and split every shared
pair column equally between its available rows. If a=1, split mu's
shared-column mass equally over rows 2,3,4; otherwise put that mass in
row a. The resulting actual law has y_2=y_3=y_4=1/11 and the private
masses in R15. Substitution in the full root expansion TB4 of 390 gives,
after maximizing all other phases, the following maxima by the modulus-5
row phase 0,1,2,3,4, multiplied by 33:

    a=1:  (89, 98, 147, 147, 147),
    a=2:  (89,138, 107, 147, 147).

The cases a=3,4 are permutations of the spoke rows and their private
columns. Thus each attaining law has full original-layout maximum
147/33=49/11, completing R14. The program checks all 1,225 original
layouts for each of the four laws. It also checks the lower-bound
averages on all 42 vertices of the component polytope: three choices
for mu's shared row and independent endpoint choices for each shared
two-row pair column. The universal lower bound is the analytic argument
R15--R16; no numerical optimizer is used in the retained check.

This height-one obstruction concerns the fixed weights and the three
pairs excluding a single reference row. It does not contradict the
K>=3 recursive-seed consumer above or exclude an arbitrary supported law.
Indeed [392](392-root-optimal-laws-do-not-tensorize-the-full-layout-bound.md)
already proves the unrestricted optimum on this same source is
631/166<4. The architecture obstruction does not decide Erdős #7.

## Reusable program and verification

[`free_root_row_pair_law.py`](../../frontier/cover-geometry/free_root_row_pair_law.py)
reuses the actual central source and tree selectors from 414, the exact
same-y transport from 417, the source-level comparison from 419, and the
profile verifier from 421. It adds the enlarged component validator,
the recursive seed sources, the exact root calculation and the all-height
bound. It retains no solver transcripts, duplicate probability fixtures
or approximate optimization data.

Its checks include all 1,225 robust root layouts, another 1,225 literal
layouts on an actual generic law with unprescribed component root columns,
the seven source trees and capacity matrices at K=3,...,7, actual support
and every component prefix cap, the exact disagreement profile, all finite
margins, the height-eight threshold, and malformed-input controls. The
root calculation also checks the two crossing affine lines and all 17
distinct root-plus-tail expressions at alpha=5/11.
The separate architecture boundary check verifies all 42 component
vertices and 4,900 original layouts for the four attaining laws in R14.

From the repository root:

    python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/free_root_row_pair_law.py
    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/free_root_row_pair_law.py

All checks use exact rational arithmetic and explicit exceptions. The
unbounded-height claims follow from R7--R13 and their counting and
monotonicity proofs, not from finite enumeration.
