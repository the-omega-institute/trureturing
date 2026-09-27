[Index](../../marked_head_profile.md) · [Literal-layout duality](400-literal-layout-mixtures-and-exact-tree-rank-duality.md) · [Actual prefix-cap interface](422-free-root-row-pair-laws-control-recursive-seed-sources.md)

# Full and all six pair cap laws have an exact laminar dual

The architecture consisting of one full-five cap law and all six
row-pair ternary cap laws, with freely chosen convex weights, has an
exact finite dual on each actual admissible source. For a mixture of
complete original layouts, its value is the least of seven minimum
average prices. Each minimum is obtained by a greedy laminar basis and
also by a threshold integral of the existing prefix capacity.

This characterizes the entire component polytopes, including choices
that are not uniform laws on complete trees. It supplies a certificate
for an architecture obstruction if all seven minimum prices exceed
the target. A rational height-two certificate also shows a strict loss
relative to an unrestricted supported probability, even with all
component choices and weights free. Its lower bound is below the
default target: no default-target obstruction or universal upper bound
is established here. These are ordinary mathematical deductions and
exact research certificates, not Lean certification or a resolution
of unrestricted Erdős #7.

## 1. One actual source, with every component choice available

Fix `K>=1` and an actual source

    S subset {1,2,3,4} x Z/7^K.

As in report 400, assume that its full projection contains a complete
five-ary tree of depth `K`, and each of its six row-pair projections
contains a complete ternary tree of depth `K`. All trees and prefixes
read the lowest digit first. Three active rows are permitted.

For a row set `B` and `b` equal to five for all four rows or three for
a row pair, define the complete cap polytope

    P_(B,b)(S) = { eta in Delta(S intersect (B x Y)) :
                     eta(Y == u mod 7^j) <= b^-j
                     for every 0<=j<=K and every u mod 7^j }.       (PC1)

The tree premises ensure that all seven polytopes are nonempty. They
do not prescribe a tree or a probability in any component. Let

    C(S) = conv( P_(all,5)(S) union union_(|B|=2) P_(B,3)(S) ).    (PC2)

Equivalently, choose one actual law from each nonempty polytope and
seven nonnegative weights summing to one, then form their common
probability. Zero weights are allowed. The laws and weights depend on
`S,K` and are fixed before the layout phases are chosen.

Let `A_K` be the finite set of all layouts giving one independent
literal phase at each original divisor

    1,5,7,35,...,7^K,5*7^K.

For `a in A_K`, write `c_a(p)=ell_a(p)^2` for its complete squared
load, including divisor one. Phases selecting row zero are allowed.
The restricted game is

    V_C(S) = min_(nu in C(S)) max_(a in A_K) E_nu c_a.             (PC3)

This is at least the unrestricted supported-law value of report 400;
equality is not assumed.

## 2. Prefix capacity, integral bases, and complete trees

For any finite set `E` of actual points in rows `B`, let `kappa_b(E)`
be the greatest mass of a nonnegative subprobability supported on `E`
obeying every absolute cap `b^-j`, including total mass at most one.
Only its projection to `Y` matters: different rows at the same leaf
share its cap. For a projection `L`, put

    kappa_b(empty)=0,
    kappa_b({0})=1                                  at height zero,
    kappa_b(L)=min(1, (1/b) sum_(d=0)^6 kappa_b(L_d)) otherwise,  (PC4)

where `L_d={z:d+7z in L}` has height one less.

**Proof of PC4.** Restriction to child `d`, followed by multiplication
of its mass by `b`, obeys the height-`K-1` caps. Thus child `d` can
carry at most `kappa_b(L_d)/b`, and the root has cap one. Conversely,
take maximizing child subprobabilities and scale some of them down
if their total exceeds one. This attains the displayed minimum. ∎

Multiplying the masses in PC1 by `b^K` gives the laminar constraints

    x_p>=0,  sum_p x_p=b^K,
    sum_(p:Y(p)==u mod 7^j) x_p <= b^(K-j).                      (PC5)

Their vertices are incidence vectors of sets `I` with `b^K` points
and the displayed integer bounds. In particular, at most one point
of `I` uses each `Y` leaf. These are bases of a laminar matroid;
their uniform laws, of mass `b^-K` per point, are precisely the
vertices of PC1.

One direct integrality proof sends `b^K` units of flow from the root
down the prefix tree, with capacity `b^(K-j)` on the edge into each
depth-`j` prefix and a final choice among its actual row labels.
Every capacity and the required flow are integers. The integral-flow
polytope projects onto PC5, so PC5 is the convex hull of these
integer incidence vectors. The same argument without the full-flow
equality shows that `b^K kappa_b(E)` is the largest size of an
independent set contained in `E`.

The distinction from complete trees is strict. At `K=2,b=3`, take

    L={0,7,1,8,2,9,3,10,4}.                                    (PC6)

Its five root children contain `2,2,2,2,1` leaves. Uniform mass `1/9`
on these nine leaves satisfies both positive-depth caps and has
capacity one. No root child contains three leaves, so `L` contains
no complete ternary tree of depth two. Thus tree existence implies
cap feasibility, but the converse is false. Even when the actual
source is admissible, restricting its allowed components to uniform
complete trees would change PC2.

Absolute prefix caps also differ from a transition bound at every
node. If an actual parent prefix `u` has depth `h` and positive mass,
then a descendant prefix `v` of depth `h+j` inherits the bound

    eta(v | u) = eta(v)/eta(u) <= b^(-(h+j))/eta(u).              (PC6a)

The right side equals `b^-j` when the parent cap is saturated; it is
larger when the parent mass is smaller. In PC6, conditioning the
uniform law on a two-leaf child gives conditional leaf mass `1/2`,
which exceeds `1/3`. Any recursive use of these laws must transport
the actual parent probability and the resulting conditional budget.

## 3. Exact minimum price by greedy selection and thresholds

Fix any real price function `f` on the same source `S`. Define

    G_(B,b)(f;S) = min_(eta in P_(B,b)(S)) E_eta f.                (PC7)

Sort the points of `S intersect (B x Y)` by increasing price. Accept
a point whenever adding it preserves every integer cap in PC5;
continue until `b^K` points have been accepted. The resulting basis
`I` satisfies

    G_(B,b)(f;S) = b^-K sum_(p in I) f(p).                       (PC8)

For completeness, these laminar independent sets satisfy exchange.
If independent `I,J` have `|I|<|J|` and every point of `J\I` is blocked
from addition to `I`, cover the blocked points by inclusion-maximal
prefix sets saturated by `I`. They are disjoint. In each such set,
`J` has at most as many points as `I`; outside their union every
point of `J` belongs to `I`. This contradicts `|J|>|I|`. Consequently
every independent set extends to a basis, and greedy selection at
each price threshold takes the full rank of that threshold set.

More explicitly, let `t_1<...<t_m` be the distinct prices in these
allowed rows, and let

    E_i={p in S intersect (B x Y): f(p)<=t_i}.

Then

    G_(B,b)(f;S)
      = t_m - sum_(i=1)^(m-1) (t_(i+1)-t_i) kappa_b(E_i).       (PC9)

Indeed every feasible probability has the threshold expansion
`E_eta f=t_m-sum_i(t_(i+1)-t_i)eta(E_i)`, and
`eta(E_i)<=kappa_b(E_i)`. Greedy has exactly
`b^K kappa_b(E_i)` selected points in each threshold set and reaches
all these bounds simultaneously. This proves PC8 and PC9, including
signed prices and tied prices. For nonnegative `f`, PC9 is also
`integral_0^infty [1-kappa_b({f<=t})] dt`.

For a fixed source, report 400's unrestricted inner minimum is
`min_(p in S) f(p)`; its tree-rank statistic arises only after
maximizing over admissible sources. PC9 instead pays the average
price of a full cap basis. Neither the Boolean complete-tree test
nor one threshold alone can replace this weighted capacity expression.

## 4. The exact architecture criterion

For a probability `theta` on the **complete** layouts `A_K`, put

    f_theta(p)=sum_(a in A_K) theta_a c_a(p),
    H_S(theta)=min_(B,b) G_(B,b)(f_theta;S),                     (PC10)

where the minimum runs over exactly the seven families in PC2.
Then

    V_C(S)=max_(theta in Delta(A_K)) H_S(theta).                 (PC11)

**Proof.** All sets are finite-dimensional nonempty compact
polytopes. Finite minimax applied to the cap bases and complete
layouts interchanges the minimum and maximum in PC3. Minimizing
the resulting linear price over a convex hull of seven polytopes
equals the least of its seven component minima. PC7--PC10 identify
these minima exactly. ∎

In particular, with `T_K=6-2(K+2)/3^K`, the following are equivalent:

1. There exists **one** `nu in C(S)` with `E_nu c_a<=T_K` for every
   complete original layout `a`.
2. For every probability `theta` on all complete original layouts,
   at least one of the seven values in PC9 is at most `T_K`.

The component witnessing condition 2 may depend on `theta`. This is
a dual certificate of condition 1; it does not permit the actual
probability in condition 1 to depend on the subsequently chosen
phases. The whole price vector must come from the same actual
layout mixture. Independent choices of per-depth maxima or unrelated
phase marginals are not authorized by PC11.

Since the costs and all cap constraints are rational, an obstruction
`V_C(S)>T_K` has a rational layout-mixture witness with all seven
minima strictly above `T_K`. Rational mixtures suffice also when
testing the universal condition: they are dense, and `H_S` is
continuous as a minimum of finitely many linear basis prices. A
failed inequality therefore persists on a rational mixture. The
seven greedy minima verify such an obstruction against **all** cap
components and **all** convex weights. They do not imply that every
unrestricted probability on `S` fails.

Thus a uniform all-source proof by this architecture requires PC9
to satisfy condition 2 for every height and every actual admissible
source. Establishing that weighted capacity inequality, or finding
an admissible source and rational complete-layout mixture violating
all seven values, remains unresolved here. Checking finitely many
chosen mixtures below the target establishes neither alternative.

## 5. A strict loss relative to unrestricted probabilities

Use the existing 27-point height-two source underlying
`recursive_minimum_source_common_law.law(2)`:

    S = {(r,0):1<=r<=3}
        union {(r,7r):1<=r<=4}
        union {(r,r+7d):1<=r<=4, 0<=d<=4}.                      (PC12)

Its five root columns each have five projected leaves. For a pair
`{r,s}`, root column zero contains the three distinct leaves
`0,7r,7s`, and private columns `r,s` each contain five leaves. Hence
the full five-tree and all six pair ternary trees exist on this
same source.

Here is one rational distribution on 23 complete layouts. For each
`r=1,2,3,4` and `d=0,...,4`, take the aligned layout centered at the
actual CRT point `(r,r+7d)`. Give each such layout weight `611/23020`
when `r<=3`, and `971/23020` when `r=4`. Add, for each `r=1,2,3`,
the independent phase tuple

    (a_1,a_5,a_7,a_35,a_49,a_245)
      = (0,r,0,r,0,56r)                                       (PC13)

with weight `3000/23020`. The weights sum to one. In PC13 the
modulus-seven phase is in root column zero, whereas the modulus-35
phase is in private root column `r`; this is a legal independent
layout, with no imposed common prefix.

The resulting exact point prices are as follows. The last column
also defines one unrestricted comparison probability `nu` on `S`.

| Actual points | Number | `4604 f_theta(p)` | `10000 nu(p)` |
| --- | ---: | ---: | ---: |
| `(r,0)`, `r<=3` | 3 | 25037 | 280 |
| `(r,7r)`, `r<=3` | 3 | 19037 | 530 |
| `(4,28)` | 1 | 12917 | 575 |
| `(r,r+7d)`, `r<=3` | 15 | 21013 | 348 |
| `(4,4+7d)` | 5 | 23053 | 355 |

All seven component minima equal

    G_(B,b)(f_theta;S) = 21021/4604.                            (PC14)

For the full component, the 25 distinct projected leaves force mass
`1/25` at every leaf, and the three row choices at leaf zero have
equal price. For any pair, its three root columns force mass `1/3`
in each. Column zero has exactly three distinct projected leaves,
each therefore of mass `1/9`; the points in each private column
have equal price. Substitution in the displayed table proves PC14
for every permitted component, without prescribing its remaining
choices. Consequently PC11 gives `V_C(S)>=21021/4604`.

The comparison masses in the table sum to one. Exact enumeration
of all 1225 root layouts, followed by joint maximization of the two
independent depth-two phases, gives

    Gamma_2(nu)=4549/1000 < 21021/4604,
    21021/4604-4549/1000 = 19351/1151000 > 0.                    (PC15)

The aligned layout with phase tuple `(0,1,1,1,1,1)` attains this
comparison maximum. Report 423's existing integer root/gain
enumerator and the independent original-label tree DP both compute
PC15 from the displayed integer masses. The enumeration formula is
exact: after fixing a root layout with loads `l_p`, the two remaining
phases contribute

    A_u + B_(r,v) + 2 w_(r,v) 1_(u=v),
    A_u=sum_(p:Y(p)=u) w_p(2l_p+1),
    B_(r,v)=w_(r,v)(2l_(r,v)+1),                               (PC16)

in addition to the root square. Every pure phase `u` is considered;
every mixed phase meeting the support is considered, and a phase
missing the support cannot improve these nonnegative gains. Thus
all complete original layouts are covered, not just aligned ones.

This proves that free weights and all six pair families do not make
the architecture equivalent to unrestricted supported laws. It does
not assert that PC14 is the exact architecture optimum, and it does
not refute the default comparison: both displayed values are below
`T_2=46/9`. The all-source target condition of section 4 remains the
required unresolved inequality.

## 6. Exact interface and provenance

[`prefix_cap_architecture_duality.py`](../../frontier/cover-geometry/prefix_cap_architecture_duality.py)
provides `prefix_capacity`, `cap_minimum`, and
`audit_architecture_dual`. The first directly reuses report 422's
ternary capacity routine; the last reuses report 400's literal
original-divisor evaluator, layout validation, target, and Boolean
tree predicates. Its input is an actual source and one explicit
rational mixture of complete layouts. It does not optimize over
all layout mixtures and does not report an upper certificate when
the returned lower bound is below the target.

The default controls compare greedy and threshold integration with
exhaustive bases under every binary price on a small carrier with
parallel row labels, also check signed rational prices and height
zero, verify PC6, and reuse report 400's constant-price mixture to
check strict versus equality and custom versus default targets.
They also verify the 23-layout price table, all seven minima in
PC14, and both independent exact computations in PC15.
Malformed sources, prices, and layout mixtures are rejected with
checks that remain active under `-O`.

Run from the repository root:

    python3 docs/reports/erdos7-odd-covering/frontier/cover-geometry/prefix_cap_architecture_duality.py
    python3 -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/prefix_cap_architecture_duality.py

The mathematical content is a `repo-derived` specialization of
established finite minimax, integral flow, and laminar-matroid
arguments. The laminar independent-set definition above agrees
with Fife and Oxley, *Laminar matroids*, European Journal of
Combinatorics (2017),
[doi:10.1016/j.ejc.2017.01.002](https://doi.org/10.1016/j.ejc.2017.01.002),
[arXiv:1606.08354v1](https://arxiv.org/abs/1606.08354v1), opening
definition. No claim of a new matroid or minimax theorem is made.
