# Weighted mixed budgets exclude old zero triples

The complete weighted inventory from
[report498](498-ten-directions-completely-describe-three-point-weighted-budgets.md)
also constrains mixed deletions. Using it in a fixed weighted objective
gives new three-point exclusions even without strengthening the old
seven-subset axis domains. One explicit triple satisfies every old pair
zero budget and has total-only triple minimum zero, but obeys

    2s1+7s2+4s3 >= 1/14.                                  (M1)

Consequently its three later-fibre survivor fractions cannot all be
strictly below theta for any 0<theta<=1/182, including the common
theta=1/3696. The retained certificate contains24 such new seed triples.
This is an ordinary uniform local proof with exact rational verification;
it is not a global source-mass bound, an arithmetic realization of the
relaxation, or new Lean verification.

## One fixed weighted objective retains the common selector

Fix a finite family in the same two-centre chart as
[report497](497-weighted-inventories-retain-more-than-all-subset-budgets.md).
Every complete original numerical label d*p^j*q^k has one fixed old-centre
selector, shared among all tested old points. The selector may differ
between complete labels, but is not selected anew at each point.
For the labelled old-divisor boxes A_i,B_i of n points and w_i>=0, put

    N(w)=sum_d max(sum_i w_i 1_Ai(d),sum_i w_i 1_Bi(d)).

Let a=p-1,b=q-1. If alpha_i,beta_i are actual pure-axis union deletion
fractions, and gamma_i is the sum of active mixed-cylinder Haar masses,
write t_i=a*alpha_i,u_i=b*beta_i,c_i=ab*gamma_i. The geometric-sum argument
of report497 applies to these same actual quantities simultaneously:

    w dot t<=N(w), w dot u<=N(w), w dot c<=N(w).            (M2)

For each i the pure-axis survivor is a Cartesian product. The union bound
for its subsequent mixed deletions gives

    ab*s_i >= [(a-t_i)(b-u_i)-c_i]_+
             >= (a-t_i)(b-u_i)-c_i.

Multiply by the fixed nonnegative w_i and use the mixed inequality M2:

    ab*sum_i w_i*s_i
      >= sum_i w_i(a-t_i)(b-u_i)-N(w).                    (M3)

Here s_i is survival of the later classes in full p/q Haar. It represents
full-family survival only when the tested old point also avoids all
old-only classes. Neither old-source independence nor jointly attainable
maximizers in the different N(w) inequalities are assumed.

For any chosen finite collection W of valid axis directions containing
the singleton directions, let

    P_h(W)={v:0<=v_i<=h, r dot v<=N(r) for r in W}.

The actual t,u belong to P_a(W),P_b(W). These nonempty compact polytopes
therefore give the sufficient local certificate

    k_w=min_(t in P_a(W),u in P_b(W))
          [sum_i w_i(a-t_i)(b-u_i)-N(w)],
    sum_i w_i*s_i >= k_w/(ab).                            (M4)

For this fixed w the objective is affine in either argument with the
other fixed. A minimizing pair can first move to a vertex of P_a(W)
and then to a vertex of P_b(W), without increasing the value. Thus all
vertex pairs suffice. This argument does not assert a vertex rule for
an objective with an additional optimized mixed allocation or pointwise
maximum inside the minimization.

Whenever k_w>=ab*theta*sum_i w_i>0, M4 excludes simultaneous strict
badness s_i<theta. The equality case is valid because badness is strict.

## A triple with a sharp numerator44

Use p=23,q=29 and the ordered profiles

    v1=(3,2,2,1,1,2,1),
    v2=(2,2,-2,2,1,2,1),
    v3=(-3,0,-2,2,1,2,1).

They are indices(2780,108,14353) in the declared20076-profile order.
The first three coordinates are split at3,5,7, with +f meaning(f,1),
-f meaning(1,f), and0 meaning(1,1). The last four coordinates are common
at11,13,17,19. There are40 literal old exponent labels in the union.
Their seven capacities, in binary-mask order, are

    (N1,N2,N12,N3,N13,N23,N123)=(24,20,42,24,38,40,56).

Take W to be only the seven nonempty subset directions. The exact
axis polytopes P22(W),P28(W) have13 and15 vertices. For w=(2,7,4),
literal evaluation gives N(w)=252, and all195 vertex pairs give

    min[2(22-t1)(28-u1)+7(22-t2)(28-u2)
                     +4(22-t3)(28-u3)-252]=44.

The minimum is attained at

    t=(16,18,22), u=(22,20,0),
    ((22-ti)(28-ui))_i=(36,32,0).

This proves M1, since44/616=1/14. Dividing by sum(w)=13 gives the
isolated strict-bad threshold1/182.

On the same axis domains the unweighted total-only expression has
minimum zero:

    min[sum_i(22-ti)(28-ui)-56]=0.

Every pair also has a feasible zero mixed-deletion budget. For pairs
(1,2),(1,3),(2,3), respectively, the consumer retains exact witnesses
for capacities(24,20,42),(24,24,38),(20,24,40). These are separate
relaxed feasibility statements; their witnesses are not asserted to
come from a single arithmetic family.

The weight274 is not an eleventh independent inventory direction.
In report498's complete mixed family,

    (2,7,4)=2(1,2,1)+2(0,1,1)+(0,1,0),
    N(2,7,4)=2*76+2*40+20=252.

These generators lie in one linearity cone of N. Even w=(1,2,1)
already has k_w=4 and supplies the same exclusion at theta=1/3696.
The improvement is the use of mixed budgets in M3, with the axis
domains unchanged; it does not contradict ten-direction completeness.

## Retained family, transport and remaining scope

The24 retained ordered triples have ten distinct ordered axis-capacity
cases and require4780 exact vertex-pair evaluations. Each has k_w>0
with k_w>=sum(w)/6, every pair has a zero-budget witness, and every old
total-only triple minimum is nonpositive. The first13 old minima are
zero; the remaining minima are negative. Thus the positive-part old
total-only bound is zero for all24.

The consumer constructs literal labelled boxes, all membership patterns,
capacities, complete rational vertex sets and pair zero witnesses.
It does not read an optimizer's claimed minimum or a proposed graph.
The certificate stores the ordered profiles and integer weights; the
adjacent result stores the recomputed rational evidence.

The box-inclusion argument of
[report494](494-three-fibre-inventories-exclude-a-pair-admissible-triple.md)
transports these exclusions to upward bad supports: a profile whose
boxes include another's activates a superset of later classes under the
same fixed full-label selector, so its survivor fraction cannot increase.
Thus an upward extension simultaneously containing all vertices of one
certified edge would supply three actual bad witnesses whose later
survival violates M4. Coordinate permutations or a global A/B exchange
also transport the local inequality when the literal label bijection is
preserved. Permuting the tested points must permute the weight slots too.

These statements do not assert that all triples touching the infinite
overflow are harmless, or that a support satisfying the retained edges
has an original arithmetic realization. A same-source global upper
bound below m7 and unrestricted noncoverage remain unresolved.

Reproduce the retained result with:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_split_weighted_mixed_bound.py

The standard-library consumer fails if its fresh exact result differs
from the adjacent JSON. No solver, floating-point optimization or new
Lean claim is used by this verification.
