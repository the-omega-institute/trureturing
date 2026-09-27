# Joint four-point budgets exclude what no fixed weight can

A single common pair of pure-axis deletion vectors cannot satisfy all mixed
budgets for the four profiles below if every survivor fraction is at most
1/3696. An exact rational certificate proves this with179 nodes and90 Farkas
leaves. Yet every fixed nonnegative weighted objective has a nonpositive
minimum on the same axis relaxation. The exclusion therefore requires the
joint constraints; choosing a different minimizing axis pair for each weight
loses it.

The48 eligible orbit edges also defeat every deletion-only repair of the
specific high-mass support retained in
[report501](501-complete-weighted-boundaries-cut-a-binary-obstruction.md):
its maximum repaired mass is0.016056462251103278..., below its threshold m7.
This is an optimum among subsets of that fixed support, not a global upper
bound over all supports. The earlier fractional witness survives all48 edges.
The results are ordinary mathematics and exact rational computation. No Lean
verification or unrestricted Erdős#7 conclusion is asserted.

## One common four-point problem

Use new primes23 and29, old primes3,5,7,11,13,17,19, and the same split/common
chart as reports501–503. The ordered profiles and middle-chart indices are

| Index | Profile |
| ---: | --- |
| 2782 | (3,2,2,1,2,1,1) |
| 2784 | (3,2,2,2,1,1,1) |
| 13607 | (-3,-2,2,2,2,1,1) |
| 14355 | (-3,0,-2,2,2,1,1) |

Each profile supplies two labelled exponent boxes, one for each common old
centre. Their union has45 distinct numerical old labels. For label d let
A_d,B_d be its four membership bits and define

    N(w)=sum_d max(w dot A_d,w dot B_d),  w>=0,
    P={v>=0 : w dot v<=N(w) for all w>=0},
    P_a=P intersect [0,a]^4.                              (J1)

The complete101-direction description from
[report502](502-complete-weighted-inventories-do-not-realize-one-selector-family.md)
applies. The singleton capacities are(24,24,28,24); examples of other
capacities are N(1,2,1,2)=110 and N(1,1,1,3)=115. The consumer independently
regenerates the101 rays and every capacity. It also checks these masks against
the simultaneous literal old CRT points and centres retained in
[report503](503-integer-selectors-strengthen-capped-budgets-but-axis-limits-survive.md).

For any one original family within this declared two-centre interface, put

    t_i=22 times pure23 union deletion fraction,
    u_i=28 times pure29 union deletion fraction,
    R_i=(22-t_i)(28-u_i).

Fractions are on full uniform new-coordinate fibres. Pure deletions act on
separate new coordinates, so their surviving product has fraction R_i/616.
Let y_i be616 times the mixed union deletion inside that product, and s_i its
remaining survivor fraction. The same family, selectors and phases give

    t in P_22,  u in P_28,  y in P,  R-y=616s.             (J2)

Each complete numerical label has one old selector and one common new phase
across all tested points. Geometric sums and the union bound give all J2
budgets; overlap only decreases union deletion. No actual joint phase
realization is assumed for arbitrary points of the relaxed polytopes.

With theta=1/3696, if all s_i<=theta then616theta=1/6 implies

    w dot R<=N(w)+sum(w)/6  for every w>=0.                (J3)

The certificate proves that no t in P_22 and u in P_28 satisfy J3 for all101
rays simultaneously. Therefore

    max_i s_i>1/3696.                                    (J4)

Old-only classes are not included in s_i. To regard these as full original
survivor fibres, the tested old points must also avoid all old-only classes.
That premise belongs to the actual old source and is not supplied by J4.
Other charts, unrestricted old residues and additional prime directions need
their own valid bridge; this certificate does not remove those hypotheses.

## Why the finite rational tree is a proof

The root covers [0,22]^4 in the t variables. At a box [l,h], a positive
violation w dot l>N(w) excludes the entire box. Otherwise each axis budget
and t>=l permit the upper tightening

    H_i=min(h_i, min_(w_i>0)
                       (N(w)-sum_(j!=i)w_j l_j)/w_i).     (J5)

Discarding t coordinates above H loses no feasible point. A split at an
interior midpoint has both closed children, whose union covers [l,H].
Shared boundary points are retained.

Since u_i<=28 and t_i<=H_i,

    (22-H_i)(28-u_i)<=(22-t_i)(28-u_i).

Any feasible t,u in the box must consequently satisfy the linear system

    u in P_28,
    -sum_i w_i(22-H_i)u_i
       <=N(w)+sum(w)/6-28 sum_i w_i(22-H_i)               (J6)

for each of the101 rays. At every leaf the certificate supplies rational
multipliers lambda>=0 for the rows Au<=b of J6 and the axis constraints,
with

    lambda A=0,  lambda b<0.                              (J7)

Their nonnegative weighted sum would give0<=lambda b<0. Thus that entire
box contains no feasible axis pair. Exact parent/child endpoints and unique
reachable node indices certify that all root points have been handled;
solver completion flags play no role.

The retained tree has89 splits,90 Farkas leaves,54 upper-bound tightenings,
maximum depth14 and maximum box denominator128. It has no empty-axis leaves.
The least negative certificate right-hand side is-10/87. This number depends
on multiplier normalization and is not asserted as a survivor margin.

This method also has a useful general completeness boundary. If the closed
joint feasible set is empty, compactness and continuity give a uniform positive
violation over P_22 times P_28. A sufficiently fine finite rational box cover
then preserves a violation in J6, and rational linear alternatives give finite
leaf certificates. A conclusion that only excludes strict interior feasibility,
while allowing boundary solutions, does not justify the same finite-termination
claim. The retained explicit tree needs no termination assumption.

## Every fixed weight fails on this same input

Here are two feasible points of the axis relaxation:

| Pair | t | u | R=(22-t)(28-u) |
| --- | --- | --- | --- |
| A | (12,14,22,22) | (24,24,0,0) | (40,32,0,0) |
| B | (22,22,16,13) | (0,0,24,24) | (0,0,24,36) |

The consumer checks all101 axis inequalities and caps for each. Their
residual mean

    Rbar=(R_A+R_B)/2=(20,16,12,18)                         (J8)

satisfies every complete mixed budget, so Rbar lies in P. For any fixed
nonnegative real weight w,

    min(w dot R_A-N(w), w dot R_B-N(w))
       <=w dot Rbar-N(w)<=0.                              (J9)

Thus no fixed weight gives a positive uniform lower bound on this axis
relaxation. This includes weights outside the101 basic rays. Completeness
of the ray description, rather than a finite search over candidate weights,
is what extends J9 to all nonnegative real w.

The difference is the order of quantifiers:

    for every axis pair, some budget is violated;
    there is no single fixed weight that excludes every axis pair.

Taking a mean in residual space need not produce the residual of a common
feasible axis pair. J8 therefore does not contradict joint infeasibility.
The two axis points are only relaxation witnesses; no simultaneous original
phase realization is required for the fixed-weight impossibility claim.

## Transport to bad-profile support

Suppose actual bad profiles b_i from the same original family have their
labelled A/B boxes contained respectively in the four certificate boxes.
For every numerical label each actual activation mask is coordinatewise
smaller, giving

    N_b(w)<=N_certificate(w)  for every w>=0.

Their actual t,u,y then satisfy the certificate's relaxed budgets. If all
four actual survivor fractions were at most theta, J3 would contradict the
tree. This proves the edge constraint on the upward closure of the actual
strict-bad profile set. The chosen underlying actual profiles may repeat.
It does not require that an auxiliary positive-weight chart point itself be
occupied by the completed source.

Permuting the three split coordinates, the four common coordinates and
simultaneously exchanging the two centres preserves ordered membership
patterns under a bijection of labelled exponent tuples. Only images lying
in the declared chart are used: a zero ternary entry is excluded. There are
192 eligible transformations and48 distinct four-point edges. The consumer
reconstructs the literal membership-pattern multiset for every image.
Auxiliary source weights are recomputed at their actual chart positions;
the combinatorial symmetry does not assert weight invariance.

## Exact effect on the fixed report501 support

Report501 retains15797 middle profiles and all Q>=39 overflow. Its auxiliary
mass is0.01615007258449842..., exceeding

    m7=7235955529/450000000000=0.01607990117555555....

Exactly seven new edges lie inside that support. Any upward subset satisfying
them must delete at least one endpoint of each, together with its selected
ancestors. The complete4^7=16384 endpoint choices produce14100 distinct
removal unions. Exact shell weights give the minimum loss

    1223226848/13067220291125=0.0000936103333951....        (J10)

It is attained by deleting

    12707,12713,12715,13596,13600,13601,13607.

The repaired support has15790 middle profiles and mass

    0.016056462251103278...,

below m7 by0.00002343892445227794.... Every candidate endpoint's selected
ancestor closure is just itself. The consumer nevertheless reconstructs
all16858 middle order arrows and88764 overflow arrows, and verifies the
repaired support against all1656 old triples and48 new quadruples. Previously
verified pair exclusions are inherited under taking a subset.

Every feasible deletion-only repair contains one of the enumerated endpoint
unions; weights are nonnegative. Hence J10 proves the best possible mass
within the fixed support. It does not cover replacing removed points by
previously excluded profiles. A new global support may still exceed m7.
Indeed the report495 fractional cover witness satisfies every new edge:
its doubled cover sums have multiplicities2:6,3:18,4:18,5:6.

The next source-bound obligation is a global bound over all admissible
supports, or a stronger constraint using original joint phase realizability.
Defeating one retained obstruction is partial progress, not that bound.

## Reproduction

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/four_point_joint_budget.py

The adjacent certificate retains exact boxes, row multipliers and the two
axis witnesses. The standard-library consumer regenerates capacities from
literal labels, checks the whole tree, rebuilds the chart orbit and evaluates
the complete fixed-support deletion problem. The adjacent result retains
exact fractions and all leaf and orbit data. Default execution compares this
result; --output writes a newly computed result. No exploratory solver is
needed to replay the certificate.
