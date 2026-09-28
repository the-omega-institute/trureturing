# Shared support avoidance and the same star carrier pass the fixed depth-two comparison

The fixed depth-two comparison vertex that defeats the old mass/scalar
query interface admits a stronger certificate. With

    w=(8/25,3/10,19/100,0,19/100), t=6,

the new supported-source comparison has

    G(w)=4061237/37867500,
    R<=10.471201626283516... <21/2<566/49,
    (615/49-6)G(w)-H_star(w,6)>.1.                    (DS1)

This is a result for ONE specified relaxed star profile. It does not
assert that every height-two actual family reduces to that profile, or
that the profile is realized exactly by a finite family. The earlier DT7 obstruction concerns a weaker source/query bound and
remains valid on its stated interface. It is ordinary mathematics and exact
rational verification, not new Lean verification.

## 1. Exact profile, actual source conditions and shared inventories

Use Q=(5,7,11,13,17,19), the five retained ternary depth-two leaves
l=0,...,4, and root groups R0={0,1}, R1={2,3,4}. For each q the root and
leaf star owners are

    q:      5 7 11 13 17 19
    root:   1 0  0  0  0  0
    leaf:   3 1  0  1  1  0.

These are the comparison data in
[Report528 DT1](../500-549/528-surviving-fibre-credits-control-arbitrary-phases-at-ternary-height-one.md).
Let b_q=1/(q-2), c_q=(q-1)/(q-2), and

    beta_ql=b_q(1_{l in R_root(q)}+1_{l=leaf(q)}),
    m_ql=1-beta_ql, g_l(U)=product_{q outside U}m_ql.

Suppose an actual source's star deletion masses are bounded by this
profile. Let eta^act_ql be lambda_q restricted to the actual star
complement and a_ql its mass. Since a_ql>=m_ql>0, use the explicit
submeasure eta_ql=(m_ql/a_ql)eta^act_ql. It is supported on the actual
star complement, has mass m_ql, and is dominated by the actual pure-q
survivor law lambda_q. This construction works on a finite carrier.
Conditional on each positive-weight leaf the product structure remains.
Define one joint submeasure

    nu=sum_l w_l delta_l tensor product_q eta_ql,
    alpha=nu(U_actual), mu=nu restricted to U_actual / alpha.

The source, query and continuation all use this same supported law.
Thinning changes no original numerical label or phase; it only selects
a smaller measure on actual survivors. The bounds hold at every finite
query depth and retain the whole nonternary tail below.

For each full nonternary numerical cofactor d, the original labels
d,3d,9d are distinct. At each support D, complete their cap inventories
to b_D. The3d inventory chooses one root and the9d inventory one leaf;
these choices are shared across all retained leaves. Both choices may
be fractional mixtures after summing full exponent vectors. No original
label is paid at more than one root or leaf within its own inventory.

At a corner the five multiplicities form one of the ten vectors

    v^{r,s}_l=1+1_{l in R_r}+1_{l=s}, r=0,1, s=0,...,4. (DS2)

## 2. The signed support probability bridge on four leaves

On leaf l, normalized support-group caps are at most

    3 b_D / product_{q in D}m_ql, |D|>=2.

For leaves0,1,2,4 the minimum signed avoidance polynomial among all
coordinate subsets of cardinality<=4, at these maximum caps, is
respectively9/40,1/12,31/165,31/165. All are positive. Weight decrease
preserves these low-dimensional residuals. For six coordinates, a
positive full response forces every five-coordinate residual positive,
by the coordinate recurrence whose complementary supports have size<=4.
It then supplies all event-induced subgraph conditions by downward
closure. A nonpositive full response is a trivial lower bound. Thus
the SIGNED full response is a valid avoidance lower bound on these
four leaves. We choose w3=0; no probability bridge for leaf3 is assumed.

For a disjoint family of k supports, the coefficient is

    sum_l w_l g_l(U) product_{D in family}v_l^{r_D,s_D}.

It is separately affine in each root/leaf inventory, so extreme caps
use DS2. For even k choose the MINIMUM of these10^k values, and for
odd k choose the MAXIMUM, because that term is subtracted. This gives

    G(w)=sum_l w_l g_l(empty)
       +sum_{k=1}^3(-1)^k sum_U N(|U|,k)b_U E_k((w_l g_l(U))_l). (DS3)

N counts partitions with no singleton blocks. Ordered10^k choices may
be deduplicated into10,55,220 product vectors for k=1,2,3; no coefficient
vector is discarded without equality. Positive minima and negative
maxima of linear functions make G concave in w. Its k=1 term is exactly
the old DT1 union-bound comparison. For the weights in DS1, exact
evaluation gives alpha>=G=4061237/37867500>.1.

## 3. The query maximum stays inside the integral

Take an arbitrary complete finite query layout with ternary exponents
0,1,2. Its nonternary unit cofactor d=1 is INCLUDED. On each fixed leaf,
the standard labelled ordered-increment comparison applies to its
product carrier. The unnormalized auxiliary coordinate atoms are

    u_ql(0)=m_ql-c_q/q,
    u_ql(j)=c_q(q-1)q^(-j-1), j>=1.                  (DS4)

They are nonnegative. All positive-depth atoms agree across leaves;
only the zero-depth atom changes. Replacing each coordinate's cylinder
indicators by its common-uniform nested comparison preserves each
query's full exponent label and its actual ternary root/leaf choice.
Conditioning on all other coordinates leaves nonnegative coefficients,
so the convex hinge comparison can be iterated. This is an upper bound,
not an assertion that actual query phases coincide.

For one common exponent tuple J, let M(J)=product_q(1+J_q), the number
of visible nonternary divisors. The3d queries assign at most M such
labels across two roots; the9d queries assign at most M across five
leaves. Querying an excluded ternary location may be reassigned to a
retained location for this upper bound. Complete both budgets to M.

For that FIXED J the weighted sum of hinges is convex in both allocation
vectors. Its maximum over the product of their two simplices is at a
corner: all3d labels choose one root, and all9d labels choose one leaf.
Thus the ten possibilities in DS2 suffice AT THIS J.

Write E={q:J_q>=1}, and set

    a_l(E)=w_l product_{q outside E}(m_ql-c_q/q).

The positive-depth atom measure nu_E is common to every leaf. A valid
upper bound for the actual star-restricted hinge is

    H_star(w,t)=sum_E integral max_{r,s}
        sum_l a_l(E)[v_l^{r,s} M-t]_+ dnu_E.           (DS5)

The maximum is inside each E/M integral. The selected corner may vary
with J; this only enlarges the supremum over actual globally consistent
query layouts. Replacing DS5 by max_{r,s} integral would generally give
the wrong direction and is not used. DS5 is convex in w.

## 4. Full tails and exact finite evaluation

For M>=t every hinge in DS5 is linear, since v_l>=1. Its pointwise
maximum is

    M[sum_l a_l+max_r sum_{l in R_r}a_l+max_l a_l]-t sum_l a_l. (DS6)

The maximizers in DS6 may differ between supports E. For each E, its
complete positive-depth mass and first moment are

    nu_E(1)=product_{q in E}(c_q/q),
    integral M dnu_E=product_{q in E}(b_q+c_q/q).

These include every prime-power depth. Subtract the exact finitely many
product atoms M<t from those totals, evaluate DS6 on the remainder,
and evaluate the ten-way maximum separately at every small M<t. There
is no unbounded-depth truncation or exchange of max and integration.

Under the same normalized source mu,

    R_{v3<=2}(mu)<=t-1+H_star(w,t)/alpha
                  <=t-1+H_star(w,t)/G(w).

For the simple weights in DS1 and t6,

    H_star=3228200366246968137908865934995503816
           /5501562645075623704410944945818359375,
    (615/49-6)G-H_star
       =2548523432511439183713026082610425361
        /22006250580302494817643779783273437500 >1/10.

The resulting query bound is24713501153110400200110167810184968389
/2360139937624505529694940814040590625<21/2. It passes the actual
pure-conditioned23/29 continuation target566/49. This continuation
uses ternary query depth<=2, so it assumes the corresponding whole
original family has v3<=2; unrestricted later ternary exponents are
not silently admitted.

## 5. What has and has not been established

This establishes a new certificate at the specified DT profile, and
a conditional source theorem whenever actual star masks admit that
profile as a pointwise upper majorant. It does NOT prove that arbitrary
depth-two star assignments have such a majorant, that all their leaf
probability bridges hold, or that adaptive choices of w preserve a
global vertex reduction. Those are separate missing interfaces.

The [exact standard-library verifier](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_shared.py)
and its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_shared.json)
check the four-leaf probability premise and the displayed rational witness.
All checks remain active with optimization enabled; default replay also
rejects a stale retained result. Run from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_shared.py
```

Explicit nonsingleton set partitions, ordered10^k products, and a
complete linear first moment with low-load corrections independently
reproduce G, H_star and the positive score. These finite checks support
the arithmetic; the probability and query transport arguments are the
ones above. No optimization or optimality claim is required for this
rational feasible witness. DS5's maximizing corner can change within
an interval between integer thresholds, so negative integer evaluations
would not by themselves rule out all real thresholds.

## 6. One certificate for a whole actual star-mask box

This enlarges DS1's fixed input to a uniform sufficient condition on
actual masks. Keep its six q coordinates, five ternary leaves and root
groups. Let beta^DT_ql be the table's star budget. Let beta^act_ql be the
actual lambda_q-mass of the union of every source-live original3q^e
or9q^e blocker on leaf l, retaining every actual exponent and phase.

Assume only

    beta^act_ql <= beta^DT_ql+1/100
    for q=5,7,11,13,17,19 and l=0,1,2,4.              (BX1)

No condition is imposed on leaf3, whose chosen weight is zero. The
actual star masses may vary anywhere below these bounds; they need not
equal a polytope corner or use the DT table's exact root/leaf owners.

Let eta^act_ql=lambda_q restricted to the actual star complement and
let a_ql=eta^act_ql(1). Define the FIXED target mass

    m*_ql=1-beta^DT_ql-1/100.

By BX1, a_ql>=m*_ql>0 on every active leaf. On those leaves perform the
explicit finite measure thinning

    xi_ql=(m*_ql/a_ql) eta^act_ql.                    (BX2)

Set xi_ql=0 on the inactive leaf; its zero weight removes it from nu.
Then xi_ql has the target mass, is supported on actual star avoidance,
and is dominated by lambda_q on each active leaf. Its original cylinder caps have not
increased. The product structure conditional on each leaf is preserved.
This is valid even on a finite carrier; no existence of a set with a
prescribed irrational or fractional cardinality is needed.

Use ONE joint submeasure

    nu=sum_l w_l delta_l tensor product_q xi_ql,
    w=(8/25,3/10,19/100,0,19/100),

then restrict nu to avoidance of every remaining actual mixed original
and normalize only at the end. The source, query and continuation all
use this same supported law. There is no mixing of unrelated corner
carriers and no per-query choice of source.

Apply DS2--DS6 at the fixed target masses m*. The exact certificate
checks all positive-weight query zero atoms m*_ql-c_q/q>=0 and all four
leaf low-dimensional positivity conditions. The common root/leaf
inventory caps used in this calculation follow from the numerical-label
argument in Section1; the program does not inspect an input family.
At t=6 it gives

    G(m*,w)=.09056814572915926... >9/100,
    R(mu)<=11.210354392408519... <45/4<566/49,
    (615/49-6)G-H_star=.030853489359847955... >3/100.    (BX3)

Thus BX1 is a PROVED UNIFORM sufficient condition for the same actual
pure-conditioned23/29 continuation under the whole-family v3<=2
hypothesis. It allows arbitrary actual q phases and finite q heights.
Neither BX1 nor DS1 is claimed to cover the whole star polytope.

The same exact verifier checks this box certificate and retains the
four positive-leaf residual minima, all target masses, and the exact
source, hinge and continuation fractions. Independent explicit support
partitions and complete-tail evaluation reproduce those fractions.

## The precise remaining global interface

For one fixed w,t and an entire product cell of root/leaf budget vectors,
if its source probability bridge holds throughout and the joint score
is positive at every block vertex, separate concavity is a valid route
to a uniform result. Alternatively, BX2 supplies a direct actual-carrier
transport whenever a certified target has no more mass than the actual
carrier on each positive-weight leaf and coordinate.

It is NOT enough to certify a different weight vector at each unrelated
vertex. Supremums of concave functions need not be concave, and an
arithmetic convex decomposition of leaf masses need not lift to source
measures. For example, take two leaves with a common six-point uniform
base and an actual surviving five-point set on each leaf. The actual
mass vector(5/6,5/6) is the average of(2/3,1) and(1,2/3). Yet a corner
component dominated by the base and supported on the actual survivor
cannot have mass1 on either leaf. A nonnegative mixture cannot cancel
illegal support outside the actual carrier. Thus this proposed corner
transport already fails in a finite classical example.

Global progress therefore requires a certified cover of the actual
profile domain by common-weight cells or transportable targets, or a
new source construction that explicitly supplies the missing joint
measure. More positive isolated vertex calculations alone do not prove
that interface.
