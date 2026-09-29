# An actual prefix blocks every source reweighting of the scalar five-axis bound

For the explicit fifteen-original family below, every supported probability
has nonunit query mean at least273/125. The existing five-axis scalar
product-union certificate requires a mean below55427/25575. Its
probability-capped support-function relaxation also gives no positive
retention, on any reweighted subsource. These statements concern one
sufficient certificate, not an odd cover or unrestricted Erdős#7.
The proof and finite certificate are ordinary mathematics, not new Lean.

## 1. An actual family and all supported probabilities

Take Q0=3^3*5^2*7=4725 and these distinct numerical originals:

    (3,0), (5,0), (7,0), (9,4), (15,1), (21,1),
    (25,3), (27,2), (35,9), (45,37), (63,52),
    (105,4), (175,13), (315,124), (945,19).

A pair means(modulus, forbidden residue); phases are fixed once globally.
Their least common multiple is4725. They leave1081 actual residues R.
The free query interface includes ALL23 nonunit divisors of4725, including
the eight numerical labels absent from this original family. For any
probability mu supported on R, define

    c(mu)=sum_(1<d|4725) max_(a mod d) mu{x:x=a mod d}.

This is the maximum mean of a complete nonunit query. Each numerical query
slot has one freely chosen phase; every term is measured on the SAME mu.
No restriction to uniform, row-constant, product or bounded-density sources
is imposed.

## 2. A pointwise rational dual certificate

The [exact certificate](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_full357_scalar_dual_certificate.json)
gives89 positive integer coefficients n_(d,a), with denominator10000.
They satisfy

    sum_a n_(d,a)<=10000                         for each numerical d,
    sum_d n_(d,x mod d)>=21840                   for EVERY x in R.

Consequently, for every supported probability,

    c(mu)>=sum_(d,a) (n_(d,a)/10000) mu{x:x=a mod d}
          =E_mu[sum_d n_(d,x mod d)/10000]
          >=21840/10000=273/125.                         (D1)

The first inequality uses nonnegativity and the separate per-label budgets.
The lower bound is a feasible dual certificate. No numerical LP optimality
is claimed or required.

The same statement holds for every nonnegative finite measure v on R:

    sum_d max_a v{x:x=a mod d}>=(273/125)||v||_1.        (D2)

For v=0 this is immediate; otherwise apply(D1) to v/||v||_1.

## 3. All finer core sources inherit the obstruction

Let Q be any finite3/5/7 carrier divisible by Q0. Keep the fifteen originals
and add any further distinct core originals. Every probability on the
actual fine survivors projects to a probability supported on R.
The fine complete-query interface includes all coarse numerical slots;
the other indicators are nonnegative. Its nonunit query norm is therefore
at least the norm of its coarse marginal, hence at least273/125.

This applies even when the source is chosen using all higher original
phases and when its conditional fine-digit weights are arbitrary. It is
not an obstruction confined to uniform fibre lifts. If a fine survivor
set is empty, it supports no probability and the statement makes no
existence claim for that set.

## 4. Exact failure of the declared scalar template

For P={11,13,17,19,23} at arbitrary finite heights, put z_p=1/(p-2).
The [same-source product-union bound](742-a-common-source-for-subsets-of-five-old-prime-heights.md)
with only one core nonunit query norm c gives retention lower bound

    delta(c)=c+2+sum_p z_p-(c+1)prod_p(1+z_p).

For these fixed outside caps, delta decreases with c and is positive iff

    c<55427/25575.

But(D1) gives

    273/125-55427/25575=2144/127875>0,
    delta(c)<=delta(273/125)=-2144/294525<0.

Thus no supported source makes this scalar sufficient criterion positive.
This does not claim that true retention is negative: the lower estimate
has failed. Different outside laws, actual marked constraints and overlap
information are not excluded.

## 5. The probability-capped relaxation still permits complete deletion

Set

    theta=prod_p(1+z_p)-1=155/357,
    beta=theta-sum_p z_p=3478/58905.

For a nonnegative measure v on R, the old-coordinate support-function
relaxation is

    R_old(v)=beta||v||_1+theta sum_d max_a v{x:x=a mod d}.

By(D2),

    R_old(v)>=(296669/294525)||v||_1>=||v||_1.

The [RC1/RC2 probability-cap construction](../../001-064/13-probability-capped-deletion-and-a-joint-observation-beyond-this-boundary.md)
for this declared support function is

    R_cap(v)=min_(0<=sigma<=v)[||v-sigma||_1+R_old(sigma)].

Every candidate is at least||v||_1; sigma=0 attains it. Hence

    R_cap(v)=||v||_1                                  (D3)

for every v, including every piece of a density-paid partition.

There is also an explicit relaxed field witness. Complete each dual row
to total10000. For a label with an original, place its deficit at the
original forbidden phase. For each of the eight missing labels, use phase0;
all eight labels are divisible by3, so their zero cylinders are already
excluded by(3,0). These fillers vanish at every point of R.

The completed rows are phase distributions of genuine complete FREE
queries. Their expected query field S(x) obeys S(x)>=273/125 everywhere.
Therefore beta+theta S(x)>=296669/294525>1 pointwise. The downward convex
hull of the relaxed fields, intersected with0<=r<=1, contains r=1.
This is a witness in the RELAXED field set. It supplies no outside CRT
originals realizing complete deletion. True phase-coupled deletion fields
can form a smaller set than this relaxation.

## 6. Replay and the remaining route

The [consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_full357_scalar_dual.py)
pins the [dual input](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_full357_scalar_dual_certificate.json),
enumerates all27*25*7 CRT triples, verifies injectivity and all1081 actual
survivors, checks every per-label coefficient budget and every pointwise
score, and recomputes all threshold and cap arithmetic. It also checks
that the chosen fillers contribute zero throughout R. The
[retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_full357_scalar_dual.json)
is compared with this complete replay; a stale result is rejected.

The obstruction justifies retaining more information than c. The
[marked same-source interface](../750-799/750-marked-boundaries-and-joint-deletion-updates.md)
keeps actual outside memberships and joint cylinder masses. Proving a
uniform positive continuation with those relations, or constructing a
different source method, remains a separate obligation.
