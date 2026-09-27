# Ten directions completely describe three-point weighted budgets

For three tested points, the complete nonnegative weighted inventory family
from [report497](497-weighted-inventories-retain-more-than-all-subset-budgets.md)
has a finite exact description. It suffices to check the seven nonzero0/1
subset directions and the three permutations of(1,1,2). No further weight
direction can strengthen this particular three-point budget system.

This is completeness of the weighted necessary inequalities, not completeness
of an arithmetic realization model. It supplies no new global source-mass
bound or unrestricted Erdos#7 conclusion. The result below is an ordinary
general proof, accompanied by an exact finite sign certificate; no new Lean
verification is claimed.

## General finite-label statement

Let D be any finite label set. At each d choose two arbitrary membership
vectors A_d,B_d in{0,1}^3 and a nonnegative real coefficient lambda_d.
For w in the nonnegative real orthant define

    N(w)=sum_(d in D) lambda_d max(w dot A_d,w dot B_d).

The arithmetic inventory has lambda_d=1; nonnegative coefficients permit
weighted finite inventories without changing the proof. Let

    R=({0,1}^3 minus{(0,0,0)}) union{(1,1,2),(1,2,1),(2,1,1)}.

For every real three-vector v,

    [w dot v<=N(w) for every w>=0]
       iff [r dot v<=N(r) for every r in R].                (T1)

The same direction set applies separately to the true t,u,c vectors from
report497. Their physical nonnegativity and axis caps are additional
conditions; T1 itself does not require v>=0.

## Two explicit cones after sorting the weights

Sort the three coordinates of w as0<=x<=y<=z. If z>=x+y, then

    (x,y,z)=x(1,1,2)+(y-x)(0,1,1)+(z-x-y)(0,0,1).          (T2)

If z<=x+y, then

    (x,y,z)=(x+y-z)(1,1,1)+(z-y)(1,1,2)+(y-x)(0,1,1).      (T3)

Every coefficient is nonnegative in its stated region. Permuting the
coordinates back gives twelve cones, two for each coordinate ordering.
They cover the whole nonnegative orthant. Equal coordinates, z=x+y and
the zero vector are included; overlaps on faces cause no problem.
Every generating ray belongs to R.

The key fact is stronger than conical coverage: N is linear on each of
these cones. Without that fact, subadditivity alone would give the wrong
direction for the desired implication.

## A single label has a common maximizing selector on each cone

Fix A,B in{0,1}^3 and put delta=A-B in{-1,0,1}^3. For sorted nonnegative
weights, the possible comparisons delta dot(x,y,z) reduce to sums of
nonnegative coordinates, differences of two ordered coordinates, and sums
of two coordinates minus the remaining one. The ordering fixes the signs
of the first two kinds. Of the third kind, only x+y-z can change sign;
the split between T2 and T3 fixes it.

Thus delta dot w has a consistent weak sign on each cone. Equivalently,
either A or B maximizes the dot product on every generating ray of that
cone. Ties are allowed. For a conical decomposition w=sum_j a_j r_j with
a_j>=0, choose this one common maximizing selector. Then

    max(w dot A,w dot B)
      =sum_j a_j max(r_j dot A,r_j dot B).                  (T4)

Sum T4 over the finite labels with their nonnegative coefficients:

    N(w)=sum_j a_j N(r_j).                                 (T5)

If the ten inequalities hold, linearity of the dot product now gives

    w dot v=sum_j a_j(r_j dot v)
            <=sum_j a_j N(r_j)=N(w).

This proves the reverse implication of T1; the forward implication follows
by selecting those ten nonnegative weights. The proof covers all real
weights directly, not merely sampled rational or bounded integer weights.

## Exact finite certificate and the computational consequence

The consumer checks the decomposition identities symbolically as integer
matrix products. It verifies a common maximizing selector for all64
Boolean pairs(A,B) on all12 cones, for768 complete checks, and also checks
that no ternary comparison normal changes sign across the rays of a cone.

As an independent finite description of the same directions, it enumerates
all13 ternary hyperplane normals modulo sign. The78 independent pairs
produce42 nonnegative ray intersections counting repetitions; primitive
normalization gives exactly the ten elements of R. The ordinary proof of
coverage uses T2/T3, so the enumeration alone is not asked to establish
coverage of an unbounded real domain.

For example,(1,2,2) is not an additional direction: it decomposes as
(1,1,1)+(0,1,1) within the same triangle cone, so its inequality follows
by T5. For arbitrary three-point inventories, one therefore needs at most
three extra rows beyond all subset rows to obtain every nonnegative
weighted axis constraint. The same is true for the mixed-deletion vector.

Applied to the arithmetic relaxation, this makes its weighted domain finite
and exact at the level of these necessary inequalities. It does not enforce
simultaneous arithmetic realization of t,u,c, original new-prime phases,
or any other relations omitted by their separate budgets. The bilinear
axis minimum from report497 still uses just the total mixed budget unless
an additional optimization argument explicitly incorporates the others.

Nor does T1 show that every triple already checked attains the strongest
global mass bound. It completes one specified representation, leaving
larger point sets and additional original-label relations as separate
proof obligations.

Reproduce with:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/three_point_weighted_inventory_complete_directions.py

The standard-library consumer retains the ten rays, their normal witnesses,
the twelve cones and all common-selector choices. It checks the adjacent
JSON without importing a solver, sampling a weight grid or relying on an
optimization status.
